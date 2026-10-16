/** @typedef {boolean | number | string} DataValue */
/** @typedef {Record<string, DataValue>} Valuation */
/** @typedef {{before: Valuation, after: Valuation}} ObservedPair */
/** @typedef {{generalized: boolean, observedPairs: ObservedPair[]}} DiscoveryContract */

/** Check a Discovery scalar without converting booleans or missing sentinels.
 * @param {unknown} value
 * @returns {boolean}
 */
export function isDataValue(value) {
  return typeof value === 'boolean' || typeof value === 'string' ||
    (typeof value === 'number' && Number.isFinite(value));
}

/** Validate a complete retained state at the import/execution boundary.
 * @param {unknown} valuation
 * @returns {void}
 */
function validateValuation(valuation) {
  if (!valuation || typeof valuation !== 'object' || Array.isArray(valuation) ||
      !Object.values(valuation).every(isDataValue)) {
    throw new Error('Discovery states must contain only finite JSON scalar values.');
  }
}

/** Reject malformed retained relations instead of ignoring their evidence.
 * @param {DiscoveryContract} contract
 * @returns {void}
 */
export function validateDiscoveryContract(contract) {
  if (!contract || typeof contract.generalized !== 'boolean' || !Array.isArray(contract.observedPairs)) {
    throw new Error('Discovery contract requires generalized and observedPairs.');
  }
  for (const pair of contract.observedPairs) {
    if (!pair || typeof pair !== 'object') throw new Error('Invalid Discovery observed pair.');
    validateValuation(pair.before);
    validateValuation(pair.after);
  }
}

/** Validate alternative exact goals against the net's declared places.
 * @param {Record<string, number>[]} markings
 * @param {Set<string>} placeIds
 * @returns {void}
 */
export function validateFinalMarkings(markings, placeIds) {
  if (!Array.isArray(markings)) throw new Error('Final markings must be an array.');
  for (const marking of markings) {
    if (!marking || typeof marking !== 'object' || Array.isArray(marking) ||
        Object.entries(marking).some(([id, tokens]) => !placeIds.has(id) || !Number.isSafeInteger(tokens) || tokens < 0)) {
      throw new Error('Each final marking requires known places and nonnegative integer token counts.');
    }
  }
}

/** Compare complete states, preserving type and absent-key distinctions.
 * @param {Valuation} left
 * @param {Valuation} right
 * @returns {boolean}
 */
export function equalValuations(left, right) {
  const keys = Object.keys(left);
  return keys.length === Object.keys(right).length &&
    keys.every(key => Object.hasOwn(right, key) && left[key] === right[key]);
}

/** Add one distinct possible successor without assigning empirical weights.
 * @param {Valuation[]} successors
 * @param {Valuation} candidate
 * @returns {void}
 */
export function addSuccessor(successors, candidate) {
  if (!successors.some(existing => equalValuations(existing, candidate))) {
    successors.push({ ...candidate });
  }
}

/** Return the exact finite relation successors for the current whole state.
 * @param {DiscoveryContract} contract
 * @param {Valuation} valuation
 * @returns {Valuation[]}
 */
export function getObservedSuccessors(contract, valuation) {
  validateDiscoveryContract(contract);
  /** @type {Valuation[]} */
  const successors = [];
  for (const pair of contract.observedPairs) {
    if (equalValuations(pair.before, valuation)) addSuccessor(successors, pair.after);
  }
  return successors;
}

/** Uniformly select a distinct permitted successor using the configured RNG.
 * This native execution choice is not a discovered probability distribution.
 * @param {Valuation[]} successors
 * @param {() => number} random
 * @returns {Valuation}
 */
export function selectSuccessor(successors, random) {
  if (successors.length === 0) throw new Error('No data successor satisfies this transition.');
  if (successors.length === 1) return successors[0];
  const draw = random();
  if (!Number.isFinite(draw) || draw < 0 || draw >= 1) {
    throw new Error('The random source must return a finite value in [0, 1).');
  }
  return successors[Math.floor(draw * successors.length)];
}
