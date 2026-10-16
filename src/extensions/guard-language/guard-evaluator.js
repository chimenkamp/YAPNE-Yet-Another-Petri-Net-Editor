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
  /** Create an evaluation error with an optional source position. */
  constructor(message, pos) {
    super(message);
    this.name = 'EvalError';
    this.pos = pos;
  }
}

/** A predicate or update is undefined for the supplied data values. */
export class EvaluationDomainError extends EvalError {}

/** Require a Boolean value instead of applying JavaScript truthiness. */
function requireBoolean(value) {
  if (typeof value !== 'boolean') throw new EvaluationDomainError('Expected a Boolean value');
  return value;
}

/** Require a finite numeric value instead of coercing strings or booleans. */
function requireNumber(value) {
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    throw new EvaluationDomainError('Expected a finite numeric value');
  }
  return requireSafeIntegerValue(value);
}

/**
 * Reject integral numeric values whose identity cannot be preserved by a Number.
 * Precision failures are execution errors, not domain mismatches that may discard
 * one generalized branch while retaining observed alternatives.
 * @param {*} value Evaluated scalar value.
 * @returns {*} Original value within the supported integer range.
 */
function requireSafeIntegerValue(value) {
  if (typeof value === 'number' && Number.isInteger(value) && !Number.isSafeInteger(value)) {
    throw new EvalError('Numeric execution exceeded the safe integer range; the transition was not applied.');
  }
  return value;
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
  return requireBoolean(result);
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
  const updates = getPostconditionUpdates(ast);
  const assignments = new Map();
  for (const [name, rhs] of updates.assignments) {
    assignments.set(name, evaluate(rhs, valuation, {}));
  }
  return { assignments, constraints: updates.constraints };
}

/**
 * Extract deterministic candidate updates while preserving all other clauses.
 * @param {Object|null} ast Postcondition AST.
 * @returns {{assignments: Map<string, Object>, constraints: Object[]}} Candidate expressions and remaining predicates.
 */
export function getPostconditionUpdates(ast) {
  const assignments = new Map();
  const constraints = [];
  for (const clause of ast ? flattenConjunction(ast) : []) {
    const assignment = tryExtractAssignment(clause);
    if (assignment && !assignments.has(assignment.varName)) {
      const { varName, rhsAst } = assignment;
      assignments.set(varName, rhsAst);
    } else {
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
  if (!constraintAst) return true;
  const result = evaluate(constraintAst, readValuation, writeValuation);
  return requireBoolean(result);
}

/**
 * Extract the set of primed (written) variable names from an AST.
 *
 * @param {Object|null} ast - AST to analyze
 * @returns {Set<string>} Set of variable names that appear primed
 */
export function getWrittenVariables(ast) {
  return getVariableReferences(ast).written;
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
      return requireSafeIntegerValue(node.value);

    case NodeType.VAR:
      if (node.primed) {
        if (Object.hasOwn(writeVals, node.name)) return requireSafeIntegerValue(writeVals[node.name]);
        throw new EvaluationDomainError(`Primed variable '${node.name}'' has no value`);
      }
      if (Object.hasOwn(readVals, node.name)) return requireSafeIntegerValue(readVals[node.name]);
      throw new EvaluationDomainError(`Variable '${node.name}' is not defined`);

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
      const extendedRead = Object.assign(Object.create(null), readVals);
      for (const binding of node.bindings) {
        extendedRead[binding.name] = evaluate(binding.expr, readVals, writeVals);
      }
      return evaluate(node.body, extendedRead, writeVals);
    }

    default:
      throw new EvalError(`Unknown AST node type: ${node.type}`);
  }
}

/** Evaluate a binary expression using the shared operator semantics. */
function evalBinop(node, readVals, writeVals) {
  return evalCall({ op: node.op, args: [node.left, node.right] }, readVals, writeVals);
}

/** Evaluate a unary expression using the shared operator semantics. */
function evalUnary(node, readVals, writeVals) {
  return evalCall({ op: node.op, args: [node.operand] }, readVals, writeVals);
}

/** Evaluate lazy Boolean operators and strict scalar arithmetic/comparisons. */
function evalCall(node, readVals, writeVals) {
  if (node.op === 'and') return node.args.every(arg => requireBoolean(evaluate(arg, readVals, writeVals)));
  if (node.op === 'or') return node.args.some(arg => requireBoolean(evaluate(arg, readVals, writeVals)));
  if (node.op === 'not') return !requireBoolean(evaluate(node.args[0], readVals, writeVals));
  if (node.op === 'ite') {
    const selected = requireBoolean(evaluate(node.args[0], readVals, writeVals)) ? 1 : 2;
    return evaluate(node.args[selected], readVals, writeVals);
  }
  if (node.op === '=>') return evaluateImplication(node.args, readVals, writeVals);
  const args = node.args.map(a => evaluate(a, readVals, writeVals));
  switch (node.op) {
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
    case '<': case '<=': case '>': case '>=':
      return evaluateComparison(node.op, args.map(requireNumber));
    case '+': case '-': case '*': case '/':
      return evaluateArithmetic(node.op, args.map(requireNumber));
    default:
      throw new EvalError(`Unknown SMT operator: ${node.op}`);
  }
}

/** Evaluate right-associative SMT implication without evaluating unused terms. */
function evaluateImplication(args, readVals, writeVals) {
  for (let index = 0; index < args.length - 1; index++) {
    if (!requireBoolean(evaluate(args[index], readVals, writeVals))) return true;
  }
  return requireBoolean(evaluate(args[args.length - 1], readVals, writeVals));
}

/** Evaluate every adjacent pair in an SMT comparison chain. */
function evaluateComparison(op, args) {
  return args.every((value, index) => {
    if (index === 0) return true;
    const previous = args[index - 1];
    if (op === '<') return previous < value;
    if (op === '<=') return previous <= value;
    if (op === '>') return previous > value;
    return previous >= value;
  });
}

/** Evaluate finite arithmetic and report undefined operations explicitly. */
function evaluateArithmetic(op, args) {
  // shortcut: Fractions use Number precision; exact-real execution requires rational arithmetic.
  if (op === '+') return args.reduce((left, right) => requireNumber(left + right), 0);
  if (op === '*') return args.reduce((left, right) => requireNumber(left * right), 1);
  if (op === '-' && args.length === 1) return requireNumber(-args[0]);
  return args.reduce((left, right) => {
    if (op === '-') return requireNumber(left - right);
    if (right === 0) throw new EvaluationDomainError('Division by zero');
    return requireNumber(left / right);
  });
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
    if (node.left.type === NodeType.VAR && node.left.primed && getWrittenVariables(node.right).size === 0) {
      return { varName: node.left.name, rhsAst: node.right };
    }
  }
  if (node.type === NodeType.CALL && node.op === '=' && node.args.length === 2) {
    if (node.args[0].type === NodeType.VAR && node.args[0].primed && getWrittenVariables(node.args[1]).size === 0) {
      return { varName: node.args[0].name, rhsAst: node.args[1] };
    }
  }
  return null;
}

/**
 * Collect free current-state and next-state variable references.
 * @param {Object|null} ast Guard AST.
 * @returns {{read: Set<string>, written: Set<string>}} Free variable names by role.
 */
export function getVariableReferences(ast) {
  const references = { read: new Set(), written: new Set() };
  collectReferences(ast, references, new Set());
  return references;
}

/** Traverse references while respecting simultaneous let and quantifier bindings. */
function collectReferences(node, references, bound) {
  if (!node) return;
  switch (node.type) {
    case NodeType.VAR:
      if (node.primed) references.written.add(node.name);
      else if (!bound.has(node.name)) references.read.add(node.name);
      break;
    case NodeType.BINOP:
      collectReferences(node.left, references, bound);
      collectReferences(node.right, references, bound);
      break;
    case NodeType.UNARYOP:
      collectReferences(node.operand, references, bound);
      break;
    case NodeType.CALL:
      for (const arg of node.args) collectReferences(arg, references, bound);
      break;
    case NodeType.QUANTIFIER:
    case NodeType.LET_EXPR:
      for (const binding of node.bindings) collectReferences(binding.expr, references, bound);
      collectReferences(node.body, references, new Set([...bound, ...node.bindings.map(binding => binding.name)]));
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
      if (node.op === 'distinct') {
        return args.flatMap((left, index) => args.slice(index + 1).map(right => `(${left} != ${right})`)).join(' && ');
      }
      // Arithmetic
      if (['+', '-', '*', '/'].includes(node.op)) {
        if (args.length === 1 && node.op === '-') return `(-(${args[0]}))`;
        return args.reduce((acc, a) => `(${acc} ${node.op} ${a})`);
      }
      // Comparisons
      if (['<', '<=', '>', '>='].includes(node.op)) {
        return args.slice(1).map((right, index) => `(${args[index]} ${node.op} ${right})`).join(' && ');
      }
      return args.join(` ${node.op} `);
    }

    default:
      throw new EvalError(`Cannot render AST node '${node.type}' as a runtime constraint`);
  }
}
