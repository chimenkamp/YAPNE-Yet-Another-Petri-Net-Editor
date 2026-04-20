/**
 * Guard Language Validator
 * Validates guard expressions against the well-formedness constraints (spec §5).
 * Returns parse errors with exact token positions for the expression editor dialog.
 */

import { parse, ParseError, LexerError } from './guard-parser.js';
import { NodeType } from './guard-parser.js';

/**
 * Validate a guard expression.
 *
 * @param {string} expression - The expression string to validate
 * @param {string[]} variableNames - Array of declared data variable names
 * @param {boolean} isPrecondition - Whether this is a precondition (primes forbidden)
 * @returns {{ valid: boolean, error: string|null, pos: number|null, ast: Object|null }}
 */
export function validate(expression, variableNames = [], isPrecondition = true) {
  const trimmed = (expression || '').trim();

  // Empty expression is always valid
  if (!trimmed) {
    return { valid: true, error: null, pos: null, ast: null };
  }

  // Step 1: Parse
  let ast, tokens;
  try {
    ({ ast, tokens } = parse(trimmed, { isPostcondition: !isPrecondition }));
  } catch (e) {
    if (e instanceof ParseError || e instanceof LexerError) {
      return { valid: false, error: e.message, pos: e.pos, ast: null };
    }
    return { valid: false, error: `Parse error: ${e.message}`, pos: null, ast: null };
  }

  if (!ast) {
    return { valid: true, error: null, pos: null, ast: null };
  }

  // Step 2: Check well-formedness
  const varSet = new Set(variableNames);
  const result = checkWellFormedness(ast, varSet, isPrecondition);
  if (result) {
    return { valid: false, error: result.error, pos: result.pos, ast: null };
  }

  return { valid: true, error: null, pos: null, ast };
}

/**
 * Check well-formedness of an AST (spec §5).
 *
 * @param {Object} node - AST node
 * @param {Set<string>} varSet - Set of declared variable names
 * @param {boolean} isPrecondition
 * @returns {{ error: string, pos: number|null }|null} Error object or null if valid
 */
function checkWellFormedness(node, varSet, isPrecondition) {
  if (!node) return null;

  switch (node.type) {
    case NodeType.LITERAL:
      return null;

    case NodeType.VAR: {
      // Check that variable is declared
      if (!varSet.has(node.name)) {
        return {
          error: `Unknown variable '${node.name}'. Declared variables: ${[...varSet].join(', ') || '(none)'}`,
          pos: null
        };
      }
      // Check priming rules
      if (node.primed && isPrecondition) {
        return {
          error: `Primed variable '${node.name}'' is not allowed in preconditions`,
          pos: null
        };
      }
      return null;
    }

    case NodeType.BINOP: {
      const lErr = checkWellFormedness(node.left, varSet, isPrecondition);
      if (lErr) return lErr;
      return checkWellFormedness(node.right, varSet, isPrecondition);
    }

    case NodeType.UNARYOP:
      return checkWellFormedness(node.operand, varSet, isPrecondition);

    case NodeType.CALL: {
      for (const arg of node.args) {
        const err = checkWellFormedness(arg, varSet, isPrecondition);
        if (err) return err;
      }
      return null;
    }

    case NodeType.QUANTIFIER: {
      // Extend variable set with bound names for body check
      const extendedVars = new Set(varSet);
      for (const binding of node.bindings) {
        extendedVars.add(binding.name);
      }
      return checkWellFormedness(node.body, extendedVars, isPrecondition);
    }

    case NodeType.LET_EXPR: {
      // Check binding expressions first
      for (const binding of node.bindings) {
        const err = checkWellFormedness(binding.expr, varSet, isPrecondition);
        if (err) return err;
      }
      // Extend variable set with let bindings for body check
      const extendedVars = new Set(varSet);
      for (const binding of node.bindings) {
        extendedVars.add(binding.name);
      }
      return checkWellFormedness(node.body, extendedVars, isPrecondition);
    }

    default:
      return null;
  }
}

/**
 * Validate a precondition expression (convenience wrapper).
 *
 * @param {string} expression
 * @param {string[]} variableNames
 * @returns {{ valid: boolean, error: string|null, pos: number|null }}
 */
export function validatePrecondition(expression, variableNames = []) {
  const result = validate(expression, variableNames, true);
  return { valid: result.valid, error: result.error, pos: result.pos };
}

/**
 * Validate a postcondition expression (convenience wrapper).
 * Additional checks: at least one primed variable should appear if the expression is non-empty.
 *
 * @param {string} expression
 * @param {string[]} variableNames
 * @returns {{ valid: boolean, error: string|null, pos: number|null }}
 */
export function validatePostcondition(expression, variableNames = []) {
  const result = validate(expression, variableNames, false);
  if (!result.valid) {
    return { valid: false, error: result.error, pos: result.pos };
  }

  // If non-empty, check that at least one primed variable appears
  if (result.ast) {
    const hasPrimed = containsPrimedVar(result.ast);
    if (!hasPrimed) {
      return {
        valid: false,
        error: `Postcondition must contain at least one primed variable (e.g., x' = ...). ` +
               `Use variable' to denote the next-state value.`,
        pos: null
      };
    }
  }

  return { valid: true, error: null, pos: null };
}

/**
 * Check if an AST contains any primed variable reference.
 */
function containsPrimedVar(node) {
  if (!node) return false;
  switch (node.type) {
    case NodeType.VAR:
      return node.primed;
    case NodeType.BINOP:
      return containsPrimedVar(node.left) || containsPrimedVar(node.right);
    case NodeType.UNARYOP:
      return containsPrimedVar(node.operand);
    case NodeType.CALL:
      return node.args.some(containsPrimedVar);
    case NodeType.QUANTIFIER:
      return containsPrimedVar(node.body);
    case NodeType.LET_EXPR:
      return node.bindings.some(b => containsPrimedVar(b.expr)) || containsPrimedVar(node.body);
    default:
      return false;
  }
}
