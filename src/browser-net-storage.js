/** Browser-local JSON storage; each named model has its own atomic storage entry. */
/** @type {string} */
export const DRAFT_NAME = 'unsaved draft';
/** @type {string} */
const DRAFT_KEY = 'yapne_autosave';
/** @type {string} */
const MODEL_PREFIX = 'yapne_model:';

/** Normalize and validate a user-provided model name.
 * @param {string} name Proposed name.
 * @returns {string} Trimmed name.
 */
export function validateModelName(name) {
  const trimmed = name.trim();
  if (!trimmed) throw new Error('Enter a model name.');
  if (trimmed.toLowerCase() === DRAFT_NAME) throw new Error('The name "unsaved draft" is reserved for automatic recovery.');
  return trimmed;
}

/** List the recovery draft and named models without interpreting stored JSON.
 * @returns {string[]} Available model names.
 */
export function listBrowserModels() {
  /** @type {string[]} */
  const names = [];
  for (let index = 0; index < localStorage.length; index++) {
    const key = localStorage.key(index);
    if (key?.startsWith(MODEL_PREFIX)) names.push(key.slice(MODEL_PREFIX.length));
  }
  names.sort((left, right) => left.localeCompare(right));
  if (localStorage.getItem(DRAFT_KEY) !== null) names.unshift(DRAFT_NAME);
  return names;
}

/** Read a selected model, allowing the caller to validate it before replacement.
 * @param {string} name Stored name.
 * @returns {string} Model JSON.
 */
export function readBrowserModel(name) {
  const json = localStorage.getItem(name === DRAFT_NAME ? DRAFT_KEY : MODEL_PREFIX + name);
  if (json === null) throw new Error('This model is no longer in browser storage.');
  return json;
}

/** Save a named model; storage errors propagate so callers cannot report success.
 * @param {string} name User-provided name.
 * @param {string} json Complete model JSON.
 * @returns {void}
 */
export function saveBrowserModel(name, json) {
  localStorage.setItem(MODEL_PREFIX + validateModelName(name), json);
}

/** Persist the recovery draft in the existing autosave slot.
 * @param {string} json Complete model JSON.
 * @returns {void}
 */
export function saveDraft(json) {
  localStorage.setItem(DRAFT_KEY, json);
}

/** Read an existing draft, including drafts written by older versions.
 * @returns {string|null} Draft JSON when present.
 */
export function readDraft() {
  return localStorage.getItem(DRAFT_KEY);
}

/** Remove only the recovery draft after an explicit save or undo to saved state.
 * @returns {void}
 */
export function clearDraft() {
  localStorage.removeItem(DRAFT_KEY);
}
