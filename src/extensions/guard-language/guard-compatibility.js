import { NodeType, quoteGuardIdentifier } from './guard-parser.js';
import { getPostconditionUpdates, getVariableReferences } from './guard-evaluator.js';
import { validate } from './guard-validator.js';

/** @typedef {{supported: boolean, reasons: string[]}} FeatureCompatibility */

/** Original soundness theorem covers real comparisons and finite Boolean data. */
const SOUNDNESS_TYPES = new Set(['real', 'float', 'double', 'bool', 'boolean']);
/** Comparisons in the real-domain theorem of Suvorov and Lomazova, Proposition 6.2. */
const PAPER_COMPARISONS = new Set(['=', 'distinct', '<', '<=', '>', '>=']);

/** Convert model collections to arrays without changing the model. */
function modelValues(collection) {
  return collection instanceof Map ? [...collection.values()] : (collection || []);
}

/** Create a compatibility result from its unsupported-feature explanations. */
function profile(reasons) {
  return { supported: reasons.length === 0, reasons: [...new Set(reasons)] };
}

/** Return the immediate AST children, including let binding expressions. */
function children(node) {
  if (!node) return [];
  if (node.type === NodeType.BINOP) return [node.left, node.right];
  if (node.type === NodeType.UNARYOP) return [node.operand];
  if (node.type === NodeType.CALL) return node.args;
  if (node.type === NodeType.QUANTIFIER) return [node.body];
  if (node.type === NodeType.LET_EXPR) return [...node.bindings.map(binding => binding.expr), node.body];
  return [];
}

/**
 * Detect quantified formulas, which the native evaluator cannot execute.
 * @param {Object|null} node Guard AST.
 * @returns {boolean} Whether a quantified formula occurs.
 */
export function hasQuantifier(node) {
  return !!node && (node.type === NodeType.QUANTIFIER || children(node).some(hasQuantifier));
}

/** Check the theorem's variable/constant operands, including signed constants. */
function isPaperAtom(node) {
  if ([NodeType.VAR, NodeType.LITERAL].includes(node.type)) return true;
  return node.type === NodeType.CALL && node.op === '-' && node.args.length === 1 && node.args[0].type === NodeType.LITERAL;
}

/** Check the original guard language, without widening it to SMT arithmetic. */
function isPaperPredicate(node) {
  if (!node) return true;
  if (node.type === NodeType.LITERAL) return node.sort === 'Bool';
  const operands = children(node);
  if (['and', 'or', 'not'].includes(node.op)) return operands.every(isPaperPredicate);
  return PAPER_COMPARISONS.has(node.op) && operands.length >= 2 && operands.every(isPaperAtom);
}

/**
 * Classify a permitted comparison operand without treating Boolean data as numeric.
 * @param {Object} node Paper comparison operand.
 * @param {Map<string, string>} variableTypes Declared variable types.
 * @returns {'Bool'|'Number'|null} Compatible comparison domain.
 */
function paperAtomSort(node, variableTypes) {
  if (node.type === NodeType.VAR) {
    const type = variableTypes.get(node.name);
    if (['bool', 'boolean'].includes(type)) return 'Bool';
    return ['real', 'float', 'double'].includes(type) ? 'Number' : null;
  }
  if (node.type === NodeType.LITERAL) return node.sort === 'Bool' ? 'Bool' : 'Number';
  return node.op === '-' && paperAtomSort(node.args[0], variableTypes) === 'Number' ? 'Number' : null;
}

/**
 * Require matching comparison domains and numeric operands for order relations.
 * @param {Object|null} node Predicate already checked against the paper grammar.
 * @param {Map<string, string>} variableTypes Declared variable types.
 * @returns {boolean} Whether the predicate has valid Boolean/numeric operand types.
 */
function hasCompatiblePaperTypes(node, variableTypes) {
  if (!node || node.type === NodeType.LITERAL) return true;
  const operands = children(node);
  if (['and', 'or', 'not'].includes(node.op)) {
    return operands.every(operand => hasCompatiblePaperTypes(operand, variableTypes));
  }
  const sorts = operands.map(operand => paperAtomSort(operand, variableTypes));
  if (!sorts[0] || !sorts.every(sort => sort === sorts[0])) return false;
  return ['=', 'distinct'].includes(node.op) || sorts[0] === 'Number';
}

/** Identify formats the existing regex-based WebPPL translator does not support. */
function requiresSharedParser(expression) {
  const text = (expression || '').trim();
  return /^\(/.test(text) || /\b(?:And|Or|Not|If|Implies|Distinct)\s*\(/.test(text) ||
    /(^|[^|])\|(?!\|)|=>|\b(?:ite|exists|forall|let)\b|(?<![<>=!])=(?!=)/.test(text) || /\b(?:True|False)\b/.test(text);
}

/** Check that each written variable has a deterministic expression in old values. */
function nativePostconditionSupported(ast) {
  const updates = getPostconditionUpdates(ast);
  return [...getVariableReferences(ast).written].every(name => updates.assignments.has(name));
}

/** Flag net structures that the existing WebPPL translator cannot preserve.
 * @param {Object} net Model with places/arcs as arrays or Maps.
 * @param {string[]} reasons Unsupported-feature explanations.
 * @returns {void}
 */
function assessProbabilisticStructure(net, reasons) {
  const arcs = modelValues(net.arcs);
  if (arcs.some(arc => (arc.type ?? 'regular') !== 'regular')) {
    reasons.push('The existing WebPPL translator supports regular arcs only.');
  }
  const endpoints = arcs.map(arc => JSON.stringify([arc.source, arc.target]));
  if (new Set(endpoints).size !== endpoints.length) {
    reasons.push('The existing WebPPL translator does not preserve parallel arcs.');
  }
  if (modelValues(net.places).some(place => place.capacity !== null && place.capacity !== undefined)) {
    reasons.push('The existing WebPPL translator does not enforce place capacities.');
  }
}

/** Add explanations for one transition's parser and execution capabilities. */
function assessTransition(transition, variableTypes, reasons) {
  const label = transition.label || transition.id || 'Transition';
  const prefix = `${label}: `;
  const names = [...variableTypes.keys()];
  const pre = validate(transition.precondition || '', names, true);
  const post = validate(transition.postcondition || '', names, false);
  for (const result of [pre, post]) {
    if (!result.valid) {
      for (const feature of Object.values(reasons)) feature.push(prefix + result.error);
      return;
    }
  }
  const generalized = transition.discoveryContract?.generalized !== false;
  if (generalized && (hasQuantifier(pre.ast) || hasQuantifier(post.ast))) {
    reasons.simulation.push(prefix + 'Quantified guards cannot be evaluated during simulation.');
  }
  if (generalized && !nativePostconditionSupported(post.ast)) {
    reasons.simulation.push(prefix + 'A relational write has no deterministic expression in current values; native simulation does not sample arbitrary constraints.');
  }
  if (!isPaperPredicate(pre.ast) || !isPaperPredicate(post.ast)) {
    reasons.soundness.push(prefix + 'The soundness paper permits Boolean combinations of variable/constant comparisons, without arithmetic terms, quantifiers, let, or conditional expressions.');
  } else if (!hasCompatiblePaperTypes(pre.ast, variableTypes) || !hasCompatiblePaperTypes(post.ast, variableTypes)) {
    reasons.soundness.push(prefix + 'Soundness comparisons require compatible operand types; ordering requires numeric values, and Boolean data cannot be compared with numbers.');
  }
  if (requiresSharedParser(transition.precondition)) {
    reasons.probabilistic.push(prefix + 'This guard syntax requires the shared parser and is unsupported by the existing WebPPL translator.');
  }
  if (getVariableReferences(post.ast).written.size > 0) {
    reasons.probabilistic.push(prefix + 'Written values require scheduler sampling and whole-run conditioning; native deterministic updates do not establish the paper probability distribution.');
  } else if (post.ast && !(post.ast.type === NodeType.LITERAL && post.ast.value === true)) {
    reasons.probabilistic.push(prefix + 'The existing WebPPL translator does not observe read-only postconditions.');
  }
  if (transition.discoveryContract) {
    reasons.probabilistic.push(prefix + 'The retained Discovery relation has no paper scheduler translation.');
    reasons.soundness.push(prefix + 'The retained Discovery relation has no translation to the soundness paper guard model.');
  }
}

/**
 * Describe supported execution paths without broadening either paper's claims.
 * @param {Object} net Model with transitions/dataVariables as arrays or Maps.
 * @returns {{simulation: FeatureCompatibility, probabilistic: FeatureCompatibility, soundness: FeatureCompatibility}} Static feature eligibility; not a proof of soundness or distributional equivalence.
 */
export function assessGuardCompatibility(net) {
  const reasons = { simulation: [], probabilistic: [], soundness: [] };
  assessProbabilisticStructure(net, reasons.probabilistic);
  const variables = modelValues(net.dataVariables);
  const variableTypes = new Map(variables.map(variable => [variable.name, (variable.type || 'int').toLowerCase()]));
  for (const variable of variables) {
    const type = (variable.type || 'int').toLowerCase();
    if (!SOUNDNESS_TYPES.has(type)) {
      reasons.soundness.push(`${variable.name}: The soundness implementation supports real/Boolean domains; unbounded integers lack the paper's termination guarantee, and generic data domains have no verifier encoding.`);
    }
    if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(variable.name) || quoteGuardIdentifier(variable.name) !== variable.name) {
      reasons.soundness.push(`${variable.name}: The existing soundness emitter cannot preserve this identifier without a verified alias mapping.`);
      reasons.probabilistic.push(`${variable.name}: The existing WebPPL translator requires a simple identifier.`);
    }
    if (['data', 'string'].includes(type)) {
      reasons.probabilistic.push(`${variable.name}: The paper translation implemented here does not encode generic scalar data domains.`);
    }
  }
  for (const transition of modelValues(net.transitions)) assessTransition(transition, variableTypes, reasons);
  return {
    simulation: profile(reasons.simulation),
    probabilistic: profile(reasons.probabilistic),
    soundness: profile(reasons.soundness),
  };
}
