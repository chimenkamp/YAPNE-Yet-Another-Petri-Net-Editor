import assert from 'node:assert/strict';
import test from 'node:test';
import { PetriNet, Place, PetriNetAPI } from '../src/petri-net-simulator.js';
import { DataPetriNet, DataVariable, DataAwareTransition } from '../src/extensions/dpn-model.js';

/** Ignore browser-only drawing in the prototype fixture.
 * @returns {void}
 */
function ignoreUI() {}

globalThis.window = {};
globalThis.document = { createElement: ignoreUI, querySelector: ignoreUI, getElementById: ignoreUI };
const { default: PetriNetApp } = await import('../src/petri-net-app.js');

/** Invoke the real reset implementation without constructing a browser app.
 * @param {PetriNet} net
 * @returns {PetriNetApp}
 */
function createApp(net) {
  const app = Object.create(PetriNetApp.prototype);
  app.api = { petriNet: net };
  app.editor = { selectedElement: null, render: ignoreUI };
  app.updateTokensDisplay = ignoreUI;
  app.updateSelectedElementProperties = ignoreUI;
  app.simulationStarted = false;
  app.initialState = null;
  app.updateFinalMarkingDisplay = ignoreUI;
  app.propertiesPanel = { innerHTML: '' };
  app._syncActionHistory = ignoreUI;
  app.updateUndoRedoButtons = ignoreUI;
  return app;
}

test('simulation reset restores the actual model current values and absent root state', () => {
  const net = new DataPetriNet('reset');
  net.addPlace(new Place('p', { x: 0, y: 0 }, 'Start', 1));
  net.addDataVariable(new DataVariable('number-id', 'number', 'int', 3));
  net.addDataVariable(new DataVariable('absent-id', 'absent', 'data'));
  net.dataVariables.get('number-id').setValue(7);
  const app = createApp(net);
  app.captureInitialState();
  assert.equal(app.simulationStarted, true);
  net.places.get('p').tokens = 4;
  net.dataVariables.get('number-id').setValue(9);
  net.dataVariables.get('absent-id').setValue('__DPN_MISSING__');
  assert.equal(app.restoreInitialState(), true);
  assert.equal(net.places.get('p').tokens, 1);
  assert.deepEqual(net.getDataValuation(), { number: 7 });
  assert.equal(net.dataVariables.get('number-id').initialValue, 3);
});

test('ordinary Petri net reset still restores tokens and missing snapshots return false', () => {
  const net = new PetriNet('reset');
  net.addPlace(new Place('p', { x: 0, y: 0 }, 'Start', 2));
  const app = createApp(net);
  assert.equal(app.restoreInitialState(), false);
  app.captureInitialState();
  net.places.get('p').tokens = 9;
  assert.equal(app.restoreInitialState(), true);
  assert.equal(net.places.get('p').tokens, 2);
});

test('real undo and redo preserve Discovery contracts and model references', () => {
  const net = new DataPetriNet('history', 'History', '', { arcSemantics: { inhibitorUsesWeight: true } });
  net.addPlace(new Place('p', { x: 0, y: 0 }, 'Place', 1));
  const variable = new DataVariable('x', 'x', 'data');
  variable.sourceName = 'Original X';
  net.addDataVariable(variable);
  const transition = new DataAwareTransition('t', { x: 100, y: 0 }, 'Activity');
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: true } }] };
  net.addTransition(transition);
  net.finalMarkings = [{ p: 1 }];
  net.discoveryMetadata = { sourceTool: 'dpn-discovery', formatVersion: '2' };
  const before = net.toJSON();
  const maps = [net.places, net.transitions, net.arcs, net.dataVariables];
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: { x: true }, after: { x: false } }] };
  variable.setValue(true);
  net.finalMarkings = [{}];
  net.setArcSemantics({ inhibitorUsesWeight: false });
  net.discoveryMetadata = { sourceTool: 'dpn-discovery', formatVersion: '2', edited: true };
  const after = net.toJSON();
  const app = createApp(net);
  app._undoStack = [{ json: before }, { json: after }];
  app._redoStack = [];
  app.performUndo();
  assert.equal(app.api.petriNet, net);
  assert.equal(net.places, maps[0]);
  assert.equal(net.transitions, maps[1]);
  assert.equal(net.arcs, maps[2]);
  assert.equal(net.dataVariables, maps[3]);
  assert.deepEqual(net.transitions.get('t').discoveryContract, JSON.parse(before).transitions[0].discoveryContract);
  assert.deepEqual(net.finalMarkings, [{ p: 1 }]);
  assert.equal(net.getArcSemantics().inhibitorUsesWeight, true);
  assert.deepEqual(net.discoveryMetadata, { sourceTool: 'dpn-discovery', formatVersion: '2' });
  assert.deepEqual(net.getDataValuation(), {});
  assert.equal(net.dataVariables.get('x').sourceName, 'Original X');
  app.performRedo();
  assert.deepEqual(net.transitions.get('t').discoveryContract, JSON.parse(after).transitions[0].discoveryContract);
  assert.deepEqual(net.finalMarkings, [{}]);
  assert.equal(net.getArcSemantics().inhibitorUsesWeight, false);
  assert.deepEqual(net.getDataValuation(), { x: true });
  net.dataVariables.get('x').reset();
  assert.deepEqual(net.getDataValuation(), {});
});

test('invalid history snapshots fail before modifying the live model', () => {
  const net = new DataPetriNet('history');
  net.addPlace(new Place('p', { x: 0, y: 0 }, 'Place', 1));
  const before = net.toJSON();
  const data = JSON.parse(before);
  data.finalMarkings = [{ unknown: 1 }];
  const app = createApp(net);
  assert.throws(() => app._restoreSnapshot(JSON.stringify(data)), /final marking/i);
  assert.equal(net.toJSON(), before);
  assert.equal(app._isRestoring, false);
  data.finalMarkings = [];
  data.transitions = [{ id: 'invalid', position: { x: 0, y: 0 }, label: 'Invalid', precondition: 'invalid(' }];
  assert.throws(() => app._restoreSnapshot(JSON.stringify(data)));
  assert.equal(net.toJSON(), before);
});

test('transition properties display unsupported native guards as plain text', context => {
  const net = new DataPetriNet('display');
  net.addDataVariable(new DataVariable('x', 'x', 'int', 0));
  const transition = new DataAwareTransition('t', { x: 0, y: 0 }, 'Constraint', 1, 0, '', "x' > x");
  net.addTransition(transition);
  const app = createApp(net);
  const children = [];
  const status = { innerHTML: '', appendChild: child => children.push(child) };
  context.mock.method(document, 'getElementById', id => id === 'transition-status-container' ? status : null);
  context.mock.method(document, 'createElement', () => ({ textContent: '' }));
  app.updateTransitionStatus('t');
  assert.equal(transition.isEnabled, false);
  assert.match(children[0].textContent, /native.*deterministic|sampling/i);
  assert.match(status.innerHTML, /Disabled/);
});

test('final-marking display reports exact alternatives instead of absent legacy flags', context => {
  const net = new DataPetriNet('goals');
  net.addPlace(new Place('p', { x: 0, y: 0 }, '<Place>', 0));
  net.finalMarkings = [{ p: 1 }, {}];
  const app = createApp(net);
  app.api.checkFinalMarkings = () => PetriNetAPI.prototype.checkFinalMarkings.call(app.api);
  const target = { innerHTML: '', textContent: '' };
  context.mock.method(document, 'getElementById', id => id === 'final-marking-content' ? target : null);
  PetriNetApp.prototype.updateFinalMarkingDisplay.call(app);
  assert.match(target.textContent, /exact.*final.*reached/i);
  assert.match(target.textContent, /2/);
  net.places.get('p').tokens = 2;
  PetriNetApp.prototype.updateFinalMarkingDisplay.call(app);
  assert.match(target.textContent, /no.*exact.*reached/i);
});
