/**
 * Guard Language SMT Emitter
 * Converts guard expression ASTs to SMT-LIB2 prefix form with per-step variable indexing.
 * Replaces the old _rewriteGuard / _infixToSmt / _applyStepVars methods in smt-generator.js.
 */

import { NodeType } from './guard-parser.js';

/**
 * Convert an AST to SMT-LIB2 prefix form with step-indexed variables.
 *
 * - Reads (unprimed idents): variable v → v_<step>
 * - Writes (primed idents):  variable v' → v_<step+1>
 * - All primes are removed in the output (Z3 doesn't allow apostrophes in identifiers).
 *
 * @param {Object|null} ast - Parsed AST node
 * @param {number} step - Current step index
 * @param {Array<[string, string]>} dataVarsList - Array of [varName, sort] pairs
 * @param {boolean} isPost - Whether this is a postcondition (primed writes go to step+1)
 * @param {Function} [symFn] - Optional symbol sanitizer function (default: identity)
 * @returns {string} SMT-LIB2 expression string, or empty string if ast is null
 */
export function toSmtLib2(ast, step, dataVarsList, isPost, symFn) {
  if (!ast) return '';

  const sym = symFn || ((s) => s);
  const varNames = new Set(dataVarsList.map(([name]) => name));

  /**
   * Get the stepped variable name for a data variable reference.
   */
  function steppedVar(name, primed) {
    if (varNames.has(name)) {
      const targetStep = primed ? step + 1 : step;
      return `${sym(name)}_${targetStep}`;
    }
    // Not a known data variable — return as-is (e.g., bound quantifier vars)
    return sym(name);
  }

  function emit(node) {
    switch (node.type) {
      case NodeType.LITERAL:
        if (node.sort === 'Bool') return node.value ? 'true' : 'false';
        if (node.sort === 'Real') {
          // Ensure real literals have decimal point
          const s = String(node.value);
          return s.includes('.') ? s : s + '.0';
        }
        return String(node.value);

      case NodeType.VAR:
        return steppedVar(node.name, node.primed);

      case NodeType.BINOP:
        return `(${node.op} ${emit(node.left)} ${emit(node.right)})`;

      case NodeType.UNARYOP:
        if (node.op === '-') {
          // SMT-LIB2 unary minus: (- x)
          return `(- ${emit(node.operand)})`;
        }
        return `(${node.op} ${emit(node.operand)})`;

      case NodeType.CALL:
        return `(${node.op} ${node.args.map(emit).join(' ')})`;

      case NodeType.QUANTIFIER: {
        const bindings = node.bindings
          .map(b => `(${sym(b.name)} ${b.sort})`)
          .join(' ');
        return `(${node.kind} (${bindings}) ${emit(node.body)})`;
      }

      case NodeType.LET_EXPR: {
        const bindings = node.bindings
          .map(b => `(${sym(b.name)} ${emit(b.expr)})`)
          .join(' ');
        return `(let (${bindings}) ${emit(node.body)})`;
      }

      default:
        return 'true';
    }
  }

  return emit(ast);
}

/**
 * Convert an AST to stepped SMT-LIB2 for τ-guard construction.
 * In τ-guards, primed variables are replaced with bound write-variables (v_w)
 * instead of stepped variables.
 *
 * @param {Object|null} ast - Parsed postcondition AST
 * @param {number} step - Current step index
 * @param {Array<[string, string]>} dataVarsList - Array of [varName, sort] pairs
 * @param {Function} [symFn] - Optional symbol sanitizer function
 * @returns {string} SMT-LIB2 expression string
 */
export function toSmtLib2ForTau(ast, step, dataVarsList, symFn) {
  if (!ast) return '';

  const sym = symFn || ((s) => s);
  const varNames = new Set(dataVarsList.map(([name]) => name));

  function steppedVar(name, primed) {
    if (primed && varNames.has(name)) {
      return `${sym(name)}_w`; // bound write variable for existential quantifier
    }
    if (varNames.has(name)) {
      return `${sym(name)}_${step}`;
    }
    return sym(name);
  }

  function emit(node) {
    switch (node.type) {
      case NodeType.LITERAL:
        if (node.sort === 'Bool') return node.value ? 'true' : 'false';
        if (node.sort === 'Real') {
          const s = String(node.value);
          return s.includes('.') ? s : s + '.0';
        }
        return String(node.value);

      case NodeType.VAR:
        return steppedVar(node.name, node.primed);

      case NodeType.BINOP:
        return `(${node.op} ${emit(node.left)} ${emit(node.right)})`;

      case NodeType.UNARYOP:
        if (node.op === '-') return `(- ${emit(node.operand)})`;
        return `(${node.op} ${emit(node.operand)})`;

      case NodeType.CALL:
        return `(${node.op} ${node.args.map(emit).join(' ')})`;

      case NodeType.QUANTIFIER: {
        const bindings = node.bindings
          .map(b => `(${sym(b.name)} ${b.sort})`)
          .join(' ');
        return `(${node.kind} (${bindings}) ${emit(node.body)})`;
      }

      case NodeType.LET_EXPR: {
        const bindings = node.bindings
          .map(b => `(${sym(b.name)} ${emit(b.expr)})`)
          .join(' ');
        return `(let (${bindings}) ${emit(node.body)})`;
      }

      default:
        return 'true';
    }
  }

  return emit(ast);
}

/**
 * Extract the set of written (primed) variable names from an AST.
 * This replaces the old regex-based _writtenVars method.
 *
 * @param {Object|null} ast - Parsed postcondition AST
 * @returns {Set<string>} Variable names that appear primed
 */
export function extractWrittenVars(ast) {
  const written = new Set();
  if (!ast) return written;

  function walk(node) {
    if (!node) return;
    switch (node.type) {
      case NodeType.VAR:
        if (node.primed) written.add(node.name);
        break;
      case NodeType.BINOP:
        walk(node.left);
        walk(node.right);
        break;
      case NodeType.UNARYOP:
        walk(node.operand);
        break;
      case NodeType.CALL:
        for (const arg of node.args) walk(arg);
        break;
      case NodeType.QUANTIFIER:
        walk(node.body);
        break;
      case NodeType.LET_EXPR:
        for (const b of node.bindings) walk(b.expr);
        walk(node.body);
        break;
    }
  }

  walk(ast);
  return written;
}
