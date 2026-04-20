/**
 * Guard Language Evaluator
 * Evaluates guard expression ASTs against a data valuation.
 * Replaces the old `new Function()` approach with safe tree-walking evaluation.
 */

import { NodeType } from './guard-parser.js';

/**
 * Evaluation error with optional position
 */
export class EvalError extends Error {
  constructor(message, pos) {
    super(message);
    this.name = 'EvalError';
    this.pos = pos;
  }
}

// ─── Precondition Evaluation ──────────────────────────────────────────────

/**
 * Evaluate a precondition AST against the current data valuation.
 * All identifiers refer to current-state values.
 *
 * @param {Object|null} ast - Parsed AST (null = trivially true)
 * @param {Object} valuation - Map of variable names to current values
 * @returns {boolean} Whether the precondition is satisfied
 */
export function evaluatePrecondition(ast, valuation) {
  if (ast === null) return true;
  const result = evaluate(ast, valuation, {});
  return Boolean(result);
}

// ─── Postcondition Evaluation ─────────────────────────────────────────────

/**
 * Analyze a postcondition AST and extract direct assignments and constraints.
 *
 * In postconditions:
 * - `x' = expr` is a direct assignment (x is written to the value of expr)
 * - `x' > expr` or any other relation involving primed vars is a constraint
 * - Conjunctions (`and`) of assignments/constraints are decomposed
 *
 * @param {Object|null} ast - Parsed postcondition AST
 * @param {Object} valuation - Current data valuation { varName: value }
 * @returns {{ assignments: Map<string, *>, constraints: Object[] }}
 *   - assignments: Map from variable name to the computed new value
 *   - constraints: Array of AST nodes representing constraint expressions
 */
export function evaluatePostcondition(ast, valuation) {
  if (ast === null) {
    return { assignments: new Map(), constraints: [] };
  }

  const assignments = new Map();
  const constraints = [];

  // Decompose the AST into individual assignment/constraint clauses
  const clauses = flattenConjunction(ast);

  for (const clause of clauses) {
    const assignment = tryExtractAssignment(clause);
    if (assignment) {
      // Direct assignment: x' = expr → evaluate expr in current valuation
      const { varName, rhsAst } = assignment;
      const value = evaluate(rhsAst, valuation, {});
      assignments.set(varName, value);
    } else {
      // It's a constraint — collect it
      constraints.push(clause);
    }
  }

  return { assignments, constraints };
}

/**
 * Check if a candidate value satisfies a constraint AST.
 * Used by the WebPPL solver fallback for constraint-based postconditions.
 *
 * @param {Object} constraintAst - A constraint AST node
 * @param {Object} readValuation - Current-state (read) variable values
 * @param {Object} writeValuation - Candidate next-state values for primed variables
 * @returns {boolean}
 */
export function checkConstraint(constraintAst, readValuation, writeValuation) {
  const result = evaluate(constraintAst, readValuation, writeValuation);
  return Boolean(result);
}

/**
 * Extract the set of primed (written) variable names from an AST.
 *
 * @param {Object|null} ast - AST to analyze
 * @returns {Set<string>} Set of variable names that appear primed
 */
export function getWrittenVariables(ast) {
  const written = new Set();
  if (!ast) return written;
  collectPrimedVars(ast, written);
  return written;
}

/**
 * Convert a constraint AST to a JavaScript expression string
 * for use with the WebPPL solver. Primed variables are expressed
 * as the variable name without prime (since WebPPL samples them).
 *
 * @param {Object} ast - Constraint AST node
 * @returns {string} JavaScript-like expression string
 */
export function constraintToString(ast) {
  return astToInfix(ast);
}

// ─── Core Evaluation Engine ──────────────────────────────────────────────

/**
 * Recursively evaluate an AST node.
 *
 * @param {Object} node - AST node
 * @param {Object} readVals - Current-state variable values (ident without prime)
 * @param {Object} writeVals - Next-state variable values (ident with prime)
 * @returns {*} The evaluated result (number, boolean, etc.)
 */
function evaluate(node, readVals, writeVals) {
  switch (node.type) {
    case NodeType.LITERAL:
      return node.value;

    case NodeType.VAR:
      if (node.primed) {
        if (node.name in writeVals) return writeVals[node.name];
        if (node.name in readVals) return readVals[node.name];
        throw new EvalError(`Primed variable '${node.name}'' has no value`);
      }
      if (node.name in readVals) return readVals[node.name];
      throw new EvalError(`Variable '${node.name}' is not defined`);

    case NodeType.BINOP:
      return evalBinop(node, readVals, writeVals);

    case NodeType.UNARYOP:
      return evalUnary(node, readVals, writeVals);

    case NodeType.CALL:
      return evalCall(node, readVals, writeVals);

    case NodeType.QUANTIFIER:
      throw new EvalError(
        `Quantifier '${node.kind}' cannot be evaluated at runtime — ` +
        `quantifiers are only used in the SMT verification path`
      );

    case NodeType.LET_EXPR: {
      const extendedRead = { ...readVals };
      for (const binding of node.bindings) {
        extendedRead[binding.name] = evaluate(binding.expr, readVals, writeVals);
      }
      return evaluate(node.body, extendedRead, writeVals);
    }

    default:
      throw new EvalError(`Unknown AST node type: ${node.type}`);
  }
}

function evalBinop(node, readVals, writeVals) {
  const l = evaluate(node.left, readVals, writeVals);
  const r = evaluate(node.right, readVals, writeVals);

  switch (node.op) {
    case 'and':      return Boolean(l) && Boolean(r);
    case 'or':       return Boolean(l) || Boolean(r);
    case '=>':       return !Boolean(l) || Boolean(r);
    case '=':        return l === r;
    case 'distinct': return l !== r;
    case '<':        return l < r;
    case '<=':       return l <= r;
    case '>':        return l > r;
    case '>=':       return l >= r;
    case '+':        return Number(l) + Number(r);
    case '-':        return Number(l) - Number(r);
    case '*':        return Number(l) * Number(r);
    case '/':
      if (Number(r) === 0) throw new EvalError('Division by zero');
      return Number(l) / Number(r);
    default:
      throw new EvalError(`Unknown binary operator: ${node.op}`);
  }
}

function evalUnary(node, readVals, writeVals) {
  const v = evaluate(node.operand, readVals, writeVals);
  switch (node.op) {
    case 'not': return !Boolean(v);
    case '-':   return -Number(v);
    default:
      throw new EvalError(`Unknown unary operator: ${node.op}`);
  }
}

function evalCall(node, readVals, writeVals) {
  const args = node.args.map(a => evaluate(a, readVals, writeVals));

  switch (node.op) {
    case 'and':
      return args.every(a => Boolean(a));
    case 'or':
      return args.some(a => Boolean(a));
    case 'not':
      return !Boolean(args[0]);
    case '=>':
      return !Boolean(args[0]) || Boolean(args[1]);
    case 'ite':
      return Boolean(args[0]) ? args[1] : args[2];
    case '=':
      return args.every((a, i) => i === 0 || a === args[0]);
    case 'distinct':
      // All pairwise distinct
      for (let i = 0; i < args.length; i++) {
        for (let j = i + 1; j < args.length; j++) {
          if (args[i] === args[j]) return false;
        }
      }
      return true;
    case '<':  return args[0] < args[1];
    case '<=': return args[0] <= args[1];
    case '>':  return args[0] > args[1];
    case '>=': return args[0] >= args[1];
    case '+':  return args.reduce((a, b) => Number(a) + Number(b), 0);
    case '-':
      if (args.length === 1) return -Number(args[0]);
      return args.reduce((a, b) => Number(a) - Number(b));
    case '*':  return args.reduce((a, b) => Number(a) * Number(b), 1);
    case '/':
      if (args.length < 2) throw new EvalError(`'/' requires at least 2 arguments`);
      return args.reduce((a, b) => {
        if (Number(b) === 0) throw new EvalError('Division by zero');
        return Number(a) / Number(b);
      });
    default:
      throw new EvalError(`Unknown SMT operator: ${node.op}`);
  }
}

// ─── Helpers ──────────────────────────────────────────────────────────────

/**
 * Flatten nested `and` / BinOp('and') into a flat list of clauses.
 */
function flattenConjunction(node) {
  if (node.type === NodeType.BINOP && node.op === 'and') {
    return [...flattenConjunction(node.left), ...flattenConjunction(node.right)];
  }
  if (node.type === NodeType.CALL && node.op === 'and') {
    return node.args.flatMap(a => flattenConjunction(a));
  }
  return [node];
}

/**
 * Try to extract a direct assignment from a clause:
 *   x' = expr  →  { varName: 'x', rhsAst: expr }
 * Returns null if the clause is not a simple assignment.
 */
function tryExtractAssignment(node) {
  // BinOp('=', Var(x, primed=true), rhs) or Call('=', [Var(x, primed=true), rhs])
  if (node.type === NodeType.BINOP && node.op === '=') {
    if (node.left.type === NodeType.VAR && node.left.primed) {
      return { varName: node.left.name, rhsAst: node.right };
    }
  }
  if (node.type === NodeType.CALL && node.op === '=' && node.args.length === 2) {
    if (node.args[0].type === NodeType.VAR && node.args[0].primed) {
      return { varName: node.args[0].name, rhsAst: node.args[1] };
    }
  }
  return null;
}

/**
 * Recursively collect all primed variable names from an AST.
 */
function collectPrimedVars(node, set) {
  if (!node) return;
  switch (node.type) {
    case NodeType.VAR:
      if (node.primed) set.add(node.name);
      break;
    case NodeType.BINOP:
      collectPrimedVars(node.left, set);
      collectPrimedVars(node.right, set);
      break;
    case NodeType.UNARYOP:
      collectPrimedVars(node.operand, set);
      break;
    case NodeType.CALL:
      for (const arg of node.args) collectPrimedVars(arg, set);
      break;
    case NodeType.QUANTIFIER:
      collectPrimedVars(node.body, set);
      break;
    case NodeType.LET_EXPR:
      for (const b of node.bindings) collectPrimedVars(b.expr, set);
      collectPrimedVars(node.body, set);
      break;
  }
}

/**
 * Convert an AST node to an infix JavaScript-like string.
 * Used for passing constraints to the WebPPL solver.
 */
function astToInfix(node) {
  if (!node) return 'true';

  switch (node.type) {
    case NodeType.LITERAL:
      return String(node.value);

    case NodeType.VAR:
      // For constraint evaluation, primed vars become unprimed
      // (the solver samples the primed var's value)
      return node.name;

    case NodeType.BINOP: {
      const l = astToInfix(node.left);
      const r = astToInfix(node.right);
      const jsOp = node.op === '=' ? '==' : node.op === 'distinct' ? '!=' : node.op;
      if (['and', 'or'].includes(node.op)) {
        const sym = node.op === 'and' ? '&&' : '||';
        return `(${l} ${sym} ${r})`;
      }
      return `(${l} ${jsOp} ${r})`;
    }

    case NodeType.UNARYOP:
      if (node.op === 'not') return `!(${astToInfix(node.operand)})`;
      if (node.op === '-') return `(-(${astToInfix(node.operand)}))`;
      return `${node.op}(${astToInfix(node.operand)})`;

    case NodeType.CALL: {
      const args = node.args.map(a => astToInfix(a));
      if (node.op === 'and') return args.map(a => `(${a})`).join(' && ');
      if (node.op === 'or') return args.map(a => `(${a})`).join(' || ');
      if (node.op === 'not') return `!(${args[0]})`;
      if (node.op === 'ite') return `(${args[0]} ? ${args[1]} : ${args[2]})`;
      if (node.op === '=>') return `(!(${args[0]}) || (${args[1]}))`;
      if (node.op === '=') return args.map((a, i) => i === 0 ? a : `(${args[0]} == ${a})`).slice(1).join(' && ');
      if (node.op === 'distinct') return `(${args[0]} != ${args[1]})`;
      // Arithmetic
      if (['+', '-', '*', '/'].includes(node.op)) {
        if (args.length === 1 && node.op === '-') return `(-(${args[0]}))`;
        return args.reduce((acc, a) => `(${acc} ${node.op} ${a})`);
      }
      // Comparisons
      if (['<', '<=', '>', '>='].includes(node.op)) {
        return `(${args[0]} ${node.op} ${args[1]})`;
      }
      return args.join(` ${node.op} `);
    }

    default:
      return 'true';
  }
}
