import assert from 'node:assert/strict';
import test from 'node:test';
import { DataPetriNet, DataVariable, DataAwareTransition } from '../src/extensions/dpn-model.js';
import { Place } from '../src/petri-net-simulator.js';

/** Skip drawing in tests that exercise the real model-loading orchestration.
 * @returns {void}
 */
function ignoreUI() {}

globalThis.window = {};
globalThis.document = { createElement: ignoreUI, querySelector: ignoreUI, getElementById: ignoreUI };
const { default: PetriNetApp } = await import('../src/petri-net-app.js');

/** Build a model with data, guards and explicit final markings.
 * @returns {DataPetriNet} Test model.
 */
function dataModel() {
  const net = new DataPetriNet('stored', 'Saved model');
  net.addPlace(new Place('p', { x: 10, y: 20 }, 'Start', 2));
  net.addDataVariable(new DataVariable('x', 'x', 'int', 3));
  net.addTransition(new DataAwareTransition('t', { x: 100, y: 20 }, 'Step', 1, 0, 'x > 0', "x' = x + 1"));
  net.finalMarkings = [{ p: 2 }];
  return net;
}

/** Provide only UI boundaries; parsing and load orchestration remain real.
 * @returns {PetriNetApp} Application fixture.
 */
function appFixture() {
  const app = Object.create(PetriNetApp.prototype);
  app.api = { petriNet: dataModel() };
  app.stopAutoRun = ignoreUI;
  app.stopAllInteractions = ignoreUI;
  app.destroyCurrentEditor = () => { app.api = null; };
  app._installLoadedModel = net => { app.api = { petriNet: net }; };
  app._refreshLoadedModel = ignoreUI;
  return app;
}

test('invalid browser JSON cannot destroy the current editor or model', () => {
  const app = appFixture();
  const original = app.api;
  assert.throws(() => app.loadModelJSON('{broken'));
  assert.equal(app.api, original);
  const invalid = JSON.parse(dataModel().toJSON());
  invalid.finalMarkings = [{ missing: 1 }];
  assert.throws(() => app.loadModelJSON(JSON.stringify(invalid)), /final marking/i);
  assert.equal(app.api, original);
});

test('browser model restoration preserves data, guards, positions and final markings', () => {
  const app = appFixture();
  const net = dataModel();
  net.dataVariables.get('x').setValue(9);
  app.loadModelJSON(net.toJSON());
  assert.ok(app.api.petriNet instanceof DataPetriNet);
  assert.equal(app.api.petriNet.dataVariables.get('x').initialValue, 3);
  assert.equal(app.api.petriNet.dataVariables.get('x').currentValue, 9);
  assert.equal(app.api.petriNet.transitions.get('t').postcondition, "x' = x + 1");
  assert.deepEqual(app.api.petriNet.places.get('p').position, { x: 10, y: 20 });
  assert.deepEqual(app.api.petriNet.finalMarkings, [{ p: 2 }]);
  assert.equal(app._isRestoring, false);
});

test('file loading uses the same validated loader and marks success saved', async () => {
  const app = appFixture();
  let saved = false;
  app.autoSave = { isDirty: false, saveNow: ignoreUI, markSaved: () => { saved = true; } };
  const net = dataModel();
  assert.equal(await app.loadFromFile(new Blob([net.toJSON()])), true);
  assert.equal(app.api.petriNet.name, net.name);
  assert.equal(saved, true);
});

test('JSON export commits the active property and marks the exported model saved', context => {
  const app = appFixture();
  let saved = false;
  let downloadRequested = false;
  let exported;
  app.commitFocusedPropertiesInput = () => { app.api.petriNet.name = 'Committed property'; };
  app.api.exportAsJSON = () => app.api.petriNet.toJSON();
  app.autoSave = { markSaved: () => { saved = true; } };
  context.mock.method(URL, 'createObjectURL', blob => { exported = blob; return 'blob:test'; });
  context.mock.method(URL, 'revokeObjectURL', ignoreUI);
  context.mock.method(document, 'createElement', () => ({ click: () => { downloadRequested = true; } }));
  app.saveToFile();
  assert.ok(exported instanceof Blob);
  assert.equal(app.api.petriNet.name, 'Committed property');
  assert.equal(downloadRequested, true);
  assert.equal(saved, true);
});

test('a rejected JSON file leaves the model intact and is not marked saved', async context => {
  const app = appFixture();
  const original = app.api;
  let saved = false;
  let message = '';
  globalThis.alert = text => { message = text; };
  context.after(() => { delete globalThis.alert; });
  app.autoSave = { saveNow: ignoreUI, isDirty: false, markSaved: () => { saved = true; } };
  assert.equal(await app.loadFromFile(new Blob(['{broken'])), false);
  assert.equal(app.api, original);
  assert.equal(saved, false);
  assert.match(message, /Error loading file/);
});

test('template loading returns the file-loader result, including cancellation', async context => {
  const app = appFixture();
  context.mock.method(globalThis, 'fetch', async () => new Response(dataModel().toJSON()));
  app.loadFromFile = async () => false;
  assert.equal(await app.loadTemplate('/example.json'), false);
});

test('canceling Python model replacement keeps the import dialog open', async () => {
  const { PythonImportDialog } = await import('../src/extensions/python-import-dialog.js');
  const dialog = Object.create(PythonImportDialog.prototype);
  let closed = false;
  dialog._code = 'x = 1';
  dialog._overlay = { querySelector: () => ({ value: '1' }) };
  dialog._app = { loadFromFile: async () => false };
  dialog.close = () => { closed = true; };
  await dialog._doImport();
  assert.equal(closed, false);
});
