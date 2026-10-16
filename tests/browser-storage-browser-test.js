/** End-to-end checks against the actual editor and browser localStorage. */
/** @type {number} */
const READY_TIMEOUT_MS = 15_000;
/** @type {number} */
const READY_POLL_MS = 50;
/** @type {number} */
const NARROW_WIDTH_PX = 390;
/** @type {HTMLIFrameElement} */
const frame = document.querySelector('iframe');
const status = document.getElementById('status');
/** @type {string[]} */
const checks = [];
/** @type {string} */
const firstName = 'Storage test <b>first</b>';
/** @type {string} */
const secondName = 'Storage test second';

/** Load the real application, optionally simulating a denied storage getter.
 * @returns {Promise<void>}
 */
async function initializeFrame() {
  if (new URLSearchParams(location.search).has('narrow')) frame.style.width = `${NARROW_WIDTH_PX}px`;
  if (!new URLSearchParams(location.search).has('denied')) {
    localStorage.setItem('hasSeenHelpDialog', 'true');
    frame.src = '../index.html';
    return;
  }
  const response = await fetch('../index.html');
  const html = await response.text();
  const base = new URL('../', location.href).href;
  const denyStorage = `<base href="${base}"><script>window.__startupAlerts = []; window.alert = message => window.__startupAlerts.push(message); Object.defineProperty(window, 'localStorage', { get() { throw new DOMException('Storage access denied', 'SecurityError'); } });<\/script>`;
  frame.srcdoc = html.replace('<head>', '<head>' + denyStorage);
}

/** Assert a browser-observable behavior and record it for the test report.
 * @param {boolean} condition Expected result.
 * @param {string} message Behavior under test.
 * @returns {void}
 */
function check(condition, message) {
  if (!condition) throw new Error(message);
  checks.push(message);
}

/** Wait for a fresh editor instance to complete data-net and storage initialization.
 * @returns {Promise<void>}
 */
async function ready() {
  const started = Date.now();
  while (!frame.contentWindow.petriApp?.browserStorageDialog) {
    if (frame.contentWindow.__startupAlerts?.length) throw new Error(frame.contentWindow.__startupAlerts.join('; '));
    if (Date.now() - started > READY_TIMEOUT_MS) throw new Error('Browser storage initialization timed out');
    await new Promise(resolve => setTimeout(resolve, READY_POLL_MS));
  }
  frame.contentDocument.getElementById('help-dialog-close').click();
}

/** Submit the actual named-save dialog.
 * @param {string} name Model name to enter.
 * @returns {void}
 */
function saveNamed(name) {
  const doc = frame.contentDocument;
  doc.getElementById('btn-save-browser').click();
  doc.getElementById('browser-model-name').value = name;
  doc.querySelector('#browser-storage-dialog form').requestSubmit();
}

/** Select a model in the actual load dialog and submit it.
 * @param {string} name Stored model name.
 * @returns {void}
 */
function loadNamed(name) {
  const doc = frame.contentDocument;
  doc.getElementById('btn-load-browser').click();
  doc.getElementById('browser-model-list').value = name;
  doc.querySelector('#browser-storage-dialog form').requestSubmit();
}

/** Check visible controls, real named storage, and complete JSON draft writes.
 * @returns {void}
 */
function checkNamedModels() {
  const win = frame.contentWindow;
  const doc = frame.contentDocument;
  const app = win.petriApp;
  const dialog = doc.getElementById('browser-storage-dialog');
  win.confirm = () => true;
  check(!app.autoSave.isDirty, 'initial model is clean');
  check(localStorage.getItem('yapne_autosave') === null, 'initial state does not create a draft');
  app.api.petriNet.name = 'First saved model';
  app.handleNetworkChanged();
  check(app.autoSave.isDirty, 'edits immediately become dirty');
  check(JSON.parse(localStorage.getItem('yapne_autosave')).name === 'First saved model', 'edits immediately persist the full JSON draft');
  check(doc.getElementById('model-save-status').textContent.includes('Unsaved changes'), 'editor shows the unsaved warning');
  saveNamed(firstName);
  check(!dialog.open && !app.autoSave.isDirty, 'named save closes the dialog and clears dirty state');
  check(localStorage.getItem('yapne_autosave') === null, 'explicit save clears the recovery draft');
  app.api.petriNet.name = 'Second saved model';
  app.handleNetworkChanged();
  saveNamed(secondName);
  doc.getElementById('btn-load-browser').click();
  check(dialog.open, 'Load (Browser) opens a modal dialog');
  check(doc.getElementById('browser-model-list').options.length === 2, 'multiple named models are listed');
  check(doc.getElementById('browser-model-list').options[0].textContent === firstName && !dialog.querySelector('b'), 'model names render as text');
  check(/between browsers/.test(dialog.textContent) && /cache or site data/.test(dialog.textContent), 'load dialog explains browser isolation and data loss');
  dialog.close();
  loadNamed(firstName);
  check(app.api.petriNet.name === 'First saved model' && !app.autoSave.isDirty, 'selected model loads and becomes the saved baseline');
}

/** Check canceled and invalid operations without losing existing work.
 * @returns {void}
 */
function checkRejectedOperations() {
  const win = frame.contentWindow;
  const doc = frame.contentDocument;
  const app = win.petriApp;
  const dialog = doc.getElementById('browser-storage-dialog');
  app.api.petriNet.name = 'Unsaved replacement';
  app.handleNetworkChanged();
  win.confirm = () => false;
  loadNamed(secondName);
  check(app.api.petriNet.name === 'Unsaved replacement' && dialog.open, 'canceling replacement preserves unsaved work');
  dialog.close();
  const original = localStorage.getItem('yapne_model:' + firstName);
  saveNamed(firstName);
  check(localStorage.getItem('yapne_model:' + firstName) === original && dialog.open, 'canceling overwrite preserves the named save');
  dialog.close();
  saveNamed('unsaved draft');
  check(dialog.open && /reserved/.test(dialog.querySelector('[role="alert"]').textContent), 'reserved draft name is rejected');
  dialog.close();
  win.confirm = () => true;
  localStorage.setItem('yapne_model:Storage test corrupt', '{broken');
  const beforeInvalidLoad = app.api;
  loadNamed('Storage test corrupt');
  check(app.api === beforeInvalidLoad && dialog.open, 'corrupt named JSON leaves the current model intact');
  dialog.close();
  localStorage.removeItem('yapne_model:Storage test corrupt');
}

/** Exercise the file loader with real data-net editor and renderer instances.
 * @returns {Promise<void>}
 */
async function checkJSONFiles() {
  const win = frame.contentWindow;
  const app = win.petriApp;
  const variableId = app.api.createDataVariable('storage_test_x', 'int', 3);
  const transitionId = app.api.createDataTransition(200, 100, 'Stored step', 'storage_test_x > 0', "storage_test_x' = storage_test_x + 1");
  app.api.updateDataVariableValue(variableId, 9);
  const json = app.api.exportAsJSON();
  check(await app.loadFromFile(new win.File([json], 'stored-data-net.json')), 'JSON files use the shared model loader');
  check(app.api.getDataVariable(variableId).currentValue === 9, 'file loading preserves current data values');
  check(app.api.petriNet.transitions.get(transitionId).postcondition.includes('storage_test_x'), 'file loading preserves transition guards');
  check(app.editor.petriNet === app.api.petriNet && app.editor.renderer.petriNet === app.api.petriNet, 'loaded editor and renderer reference the same data model');
  check(!app.autoSave.isDirty, 'successful file loading establishes a saved baseline');
}

/** Exercise storage quota errors at the browser API boundary.
 * @returns {void}
 */
function checkStorageFailure() {
  const win = frame.contentWindow;
  const doc = frame.contentDocument;
  const app = win.petriApp;
  const dialog = doc.getElementById('browser-storage-dialog');
  const setItem = win.Storage.prototype.setItem;
  win.Storage.prototype.setItem = function(key, value) {
    if (key.startsWith('yapne_')) throw new DOMException('Test quota exceeded', 'QuotaExceededError');
    return setItem.call(this, key, value);
  };
  try {
    app.api.petriNet.name = 'Quota failure';
    app.handleNetworkChanged();
    check(/could not be saved/.test(doc.getElementById('model-save-status').textContent), 'quota failure appears in the editor');
    saveNamed('Storage test failed');
    check(dialog.open && /quota/.test(dialog.querySelector('[role="alert"]').textContent), 'failed named save stays open with an error');
    check(app.autoSave.isDirty, 'failed saves never mark the model saved');
    dialog.close();
  } finally {
    win.Storage.prototype.setItem = setItem;
  }
}

/** Reload the full application, then check recovered content and history.
 * @returns {Promise<void>}
 */
async function checkReloadAndHistory() {
  const app = frame.contentWindow.petriApp;
  const doc = frame.contentDocument;
  app.api.petriNet.name = 'Recovered after refresh';
  app.handleNetworkChanged();
  check(/Unsaved changes/.test(doc.getElementById('model-save-status').textContent), 'draft saves recover when storage becomes available');
  const draft = localStorage.getItem('yapne_autosave');
  app.autoSave.stop();
  await new Promise(resolve => {
    frame.addEventListener('load', resolve, { once: true });
    frame.contentWindow.location.reload();
  });
  await ready();
  const restored = frame.contentWindow.petriApp;
  check(restored.api.petriNet.name === 'Recovered after refresh', 'full page reload automatically restores the unsaved draft');
  check(restored.autoSave.isDirty, 'restored recovery draft remains visibly unsaved');
  check(restored.api.exportAsJSON() === draft, 'recovery preserves the complete serialized model');
  restored.api.petriNet.name = 'Post-recovery edit';
  restored.handleNetworkChanged();
  restored.performUndo();
  check(restored.api.petriNet.name === 'Recovered after refresh', 'undo after recovery starts from the recovered model');
  saveNamed('Storage test recovered');
  restored.api.petriNet.name = 'After save';
  restored.handleNetworkChanged();
  restored.performUndo();
  check(!restored.autoSave.isDirty, 'undo to the explicitly saved state clears dirty status');
  restored.performRedo();
  check(restored.autoSave.isDirty, 'redo away from the saved state restores dirty status');
  restored.autoSave.stop();
}

/** Verify the editor remains usable when browser storage access is denied.
 * @returns {void}
 */
function checkDeniedStorage() {
  const app = frame.contentWindow.petriApp;
  const doc = frame.contentDocument;
  check(/Could not restore/.test(doc.getElementById('model-save-status').textContent), 'denied storage shows a recovery warning');
  app.api.petriNet.name = 'Still editable';
  app.handleNetworkChanged();
  check(app.autoSave.isDirty, 'editing works without storage permission');
  doc.getElementById('btn-save-browser').click();
  const dialog = doc.getElementById('browser-storage-dialog');
  check(dialog.open && dialog.querySelector('[type="submit"]').disabled, 'unavailable browser saves are disabled');
  check(/unavailable/.test(dialog.querySelector('[role="alert"]').textContent), 'dialog explains denied storage');
  check(frame.contentWindow.__startupAlerts.length === 0, `startup has no alert failures: ${frame.contentWindow.__startupAlerts.join('; ')}`);
  app.autoSave.stop();
}

/** Run integration checks against an isolated browser profile.
 * @returns {Promise<void>}
 */
async function run() {
  await initializeFrame();
  await ready();
  if (new URLSearchParams(location.search).has('denied')) {
    checkDeniedStorage();
  } else {
    checkNamedModels();
    await checkJSONFiles();
    checkRejectedOperations();
    checkStorageFailure();
    await checkReloadAndHistory();
  }
  if (new URLSearchParams(location.search).has('visual')) {
    frame.contentWindow.petriApp.browserStorageDialog.open('load');
    const bounds = frame.contentDocument.getElementById('browser-storage-dialog').getBoundingClientRect();
    check(bounds.left >= 0 && bounds.right <= frame.contentWindow.innerWidth, 'dialog fits within the available viewport');
    const indicator = frame.contentDocument.getElementById('model-save-status').getBoundingClientRect();
    const title = frame.contentDocument.querySelector('.header-title').getBoundingClientRect();
    check(indicator.top >= title.bottom, 'save status remains below the header title');
    status.dataset.viewport = JSON.stringify({ outer: innerWidth, frame: frame.contentWindow.innerWidth, dialog: bounds.toJSON() });
  }
  status.dataset.result = 'pass';
  status.textContent = `PASS: ${checks.length} browser storage checks`;
}

run().catch(error => {
  status.dataset.result = 'fail';
  status.textContent = `FAIL after ${checks.length} checks: ${error.stack}`;
});
