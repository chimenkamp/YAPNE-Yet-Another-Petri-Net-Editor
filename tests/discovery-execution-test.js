import assert from 'node:assert/strict';
import test from 'node:test';
import { DataPetriNet, DataVariable, DataAwareTransition } from '../src/extensions/dpn-model.js';
import { Place, Arc, PetriNetEditor } from '../src/petri-net-simulator.js';
import { EventLogGenerator } from '../src/event-log-generator.js';
import { ProbabilisticEventLogGenerator } from '../src/extensions/probabilistic-event-log-generator.js';

/** Create a one-step data net with an initially absent Discovery variable.
 * @returns {{net: DataPetriNet, transition: DataAwareTransition}}
 */
function createNet() {
  const net = new DataPetriNet('n', 'Discovery', 'Imported contract', { arcSemantics: { inhibitorUsesWeight: true } });
  net.addPlace(new Place('start', { x: 0, y: 0 }, 'Start', 1));
  net.addPlace(new Place('end', { x: 100, y: 0 }, 'End', 0, null, 1));
  const transition = new DataAwareTransition('t', { x: 50, y: 0 }, 'Activity');
  net.addTransition(transition);
  net.addArc(new Arc('a1', 'start', 't'));
  net.addArc(new Arc('a2', 't', 'end'));
  net.addDataVariable(new DataVariable('x', 'x', 'data'));
  net.finalMarkings = [{ end: 1 }];
  net.discoveryMetadata = { sourceTool: 'dpn-discovery' };
  return { net, transition };
}

test('editor copy and paste preserve retained states with arbitrary scalar names', () => {
  const { net, transition } = createNet();
  const state = JSON.parse('{"__proto__":"kept","x":true}');
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: state }] };
  const editor = Object.create(PetriNetEditor.prototype);
  Object.assign(editor, { petriNet: net, selectedElements: new Map([['t', { id: 't', type: 'transition' }]]),
    autoConnectEnabled: false, snapToGrid: false, callbacks: {},
    generateUUID: () => 't-copy', setMultiSelection: () => {}, render: () => {} });
  assert.equal(editor.copySelection(), true);
  assert.equal(editor.pasteSelection(), true);
  const copied = net.transitions.get('t-copy');
  assert.ok(copied instanceof DataAwareTransition);
  assert.deepEqual(copied.discoveryContract, transition.discoveryContract);
  copied.discoveryContract.observedPairs[0].after.x = false;
  assert.equal(transition.discoveryContract.observedPairs[0].after.x, true);
  assert.deepEqual(copied.getSuccessorValuations({}), [JSON.parse('{"__proto__":"kept","x":false}')]);
});

test('Discovery starts with an empty valuation and reset restores absence', async () => {
  const { net, transition } = createNet();
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: '__DPN_MISSING__' } }] };
  assert.deepEqual(net.getDataValuation(), {});
  assert.equal(await net.fireTransition('t'), true);
  assert.deepEqual(net.getDataValuation(), { x: '__DPN_MISSING__' });
  net.dataVariables.get('x').reset();
  assert.deepEqual(net.getDataValuation(), {});
});

test('retained relation matches complete typed before snapshots', () => {
  const { net, transition } = createNet();
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: { x: true }, after: { x: false } }] };
  net.setDataValuation({ x: 1 });
  assert.equal(net.isTransitionEnabled('t'), false);
  net.setDataValuation({ x: true });
  assert.equal(net.isTransitionEnabled('t'), true);
  net.addDataVariable(new DataVariable('y', 'y', 'data', 2));
  assert.equal(net.isTransitionEnabled('t'), false);
});

test('retained and generalized successors are united and deduplicated', async () => {
  const { net, transition } = createNet();
  net.setDataValuation({ x: 2 });
  transition.precondition = 'x > 0';
  transition.postcondition = "x' = x + 1";
  transition.discoveryContract = { generalized: true, observedPairs: [
    { before: { x: 2 }, after: { x: 9 } },
    { before: { x: 2 }, after: { x: 9 } },
    { before: { x: 2 }, after: { x: 3 } }
  ] };
  assert.deepEqual(transition.getSuccessorValuations({ x: 2 }), [{ x: 9 }, { x: 3 }]);
  assert.equal(await net.fireTransition('t', () => 0.75), true);
  assert.deepEqual(net.getDataValuation(), { x: 3 });
});

test('an inapplicable generalized domain does not discard observed alternatives', async () => {
  const { net, transition } = createNet();
  transition.precondition = 'x > 0';
  transition.postcondition = "x' = x + 1";
  transition.discoveryContract = { generalized: true, observedPairs: [{ before: {}, after: { x: 'start' } }] };
  assert.equal(await net.fireTransition('t'), true);
  assert.deepEqual(net.getDataValuation(), { x: 'start' });
});

test('observed after states replace the valuation including removed variables', async () => {
  const { net, transition } = createNet();
  net.setDataValuation({ x: 4 });
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: { x: 4 }, after: {} }] };
  assert.equal(await net.fireTransition('t'), true);
  assert.deepEqual(net.getDataValuation(), {});
});

test('deterministic assignments use the same old state and check every predicate', async () => {
  const { net, transition } = createNet();
  net.setDataValuation({ x: 2 });
  net.addDataVariable(new DataVariable('y', 'y', 'int', 5));
  transition.postcondition = "x' = y and y' = x";
  assert.equal(await net.fireTransition('t'), true);
  assert.deepEqual(net.getDataValuation(), { x: 5, y: 2 });
  for (const postcondition of ["x' = 1 and x' > 5", "x' = 1 and x' = 2"]) {
    const invalid = createNet();
    invalid.transition.postcondition = postcondition;
    assert.equal(await invalid.net.fireTransition('t'), false);
    assert.equal(invalid.net.places.get('start').tokens, 1);
    assert.deepEqual(invalid.net.getDataValuation(), {});
  }
});

test('unsupported postcondition sampling fails before tokens change', async () => {
  const { net, transition } = createNet();
  net.setDataValuation({ x: 2 });
  transition.postcondition = "x' > x";
  await assert.rejects(net.fireTransition('t'), /native|deterministic/i);
  assert.equal(net.places.get('start').tokens, 1);
  assert.deepEqual(net.getDataValuation(), { x: 2 });
});

test('invalid data and random sources fail without changing tokens', async () => {
  const { net, transition } = createNet();
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: Infinity } }] };
  await assert.rejects(net.fireTransition('t'), /finite|scalar/i);
  assert.equal(net.places.get('start').tokens, 1);
  transition.discoveryContract.observedPairs = [{ before: {}, after: { x: 1 } }, { before: {}, after: { x: 2 } }];
  await assert.rejects(net.fireTransition('t', () => 1), /random/i);
  assert.equal(net.places.get('start').tokens, 1);
});

test('JSON and both event clones preserve contracts, goals, absence and silent flags', () => {
  const { net, transition } = createNet();
  transition.silent = true;
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: true } }] };
  net.dataVariables.get('x').sourceName = 'Original X';
  net.setDataValuation({ x: true });
  const clones = [DataPetriNet.fromJSON(net.toJSON()), new EventLogGenerator(net).clonePetriNet(), new ProbabilisticEventLogGenerator(net).cloneNet()];
  for (const clone of clones) {
    assert.deepEqual(clone.finalMarkings, net.finalMarkings);
    assert.deepEqual(clone.discoveryMetadata, net.discoveryMetadata);
    assert.deepEqual(clone.transitions.get('t').discoveryContract, transition.discoveryContract);
    assert.equal(clone.transitions.get('t').silent, true);
    assert.equal(clone.places.get('end').finalMarking, 1);
    assert.equal(clone.getArcSemantics().inhibitorUsesWeight, true);
    assert.deepEqual(clone.getDataValuation(true), { 'Original X': true });
    clone.dataVariables.get('x').reset();
    assert.deepEqual(clone.getDataValuation(), {});
  }
  assert.match(net.toPNML(), /<model-json>/);
});

test('ordinary data variables reset to initial rather than current saved values', () => {
  const { net } = createNet();
  const variable = new DataVariable('n', 'n', 'int', 3);
  net.addDataVariable(variable);
  variable.setValue(8);
  const clone = DataPetriNet.fromJSON(net.toJSON());
  clone.dataVariables.get('n').reset();
  assert.equal(clone.dataVariables.get('n').getValue(), 3);
});

test('legacy logging emits no activity event or step for a refused firing', async () => {
  const { net, transition } = createNet();
  transition.postcondition = "x' = 1 and x' > 5";
  const generator = new EventLogGenerator(net, { eventLogFormat: 'lifecycle' });
  const simulationCase = generator.createCase();
  generator.selectNextTransition = () => 't';
  const initialLength = generator.eventLog.length;
  await generator.processCase(simulationCase);
  assert.equal(simulationCase.steps, 0);
  assert.equal(generator.eventLog.length, initialLength + 1);
  assert.equal(generator.eventLog.at(-1).status, 'failed');
  assert.equal(generator.eventLog.filter(row => row['concept:name'] === 'Activity').length, 0);
});

test('Discovery event logs preserve unchanged observed values in every event', async () => {
  const { net, transition } = createNet();
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: true } }] };
  net.dataVariables.get('x').sourceName = 'Original X';
  net.places.get('end').finalMarking = null;
  net.addPlace(new Place('final', { x: 200, y: 0 }, 'Final', 0, null, 1));
  const next = new DataAwareTransition('next', { x: 150, y: 0 }, 'Next');
  next.discoveryContract = { generalized: false, observedPairs: [{ before: { x: true }, after: { x: true } }] };
  net.addTransition(next);
  net.addArc(new Arc('a3', 'end', 'next'));
  net.addArc(new Arc('a4', 'next', 'final'));
  net.finalMarkings = [{ final: 1 }];
  const generator = new EventLogGenerator(net, { eventLogFormat: 'classic', seed: 10 });
  const simulationCase = generator.createCase();
  await generator.processCase(simulationCase);
  await generator.processCase(simulationCase);
  assert.deepEqual(generator.eventLog.map(row => row['Original X']), [true, true]);
  const probabilistic = new ProbabilisticEventLogGenerator(net, { eventLogFormat: 'classic', seed: 10 });
  const rows = await probabilistic.generateCases(1);
  assert.deepEqual(rows.map(row => row['Original X']), [true, true]);
});

test('alternative final markings require an exact marking in classic log generation', () => {
  const { net } = createNet();
  const generator = new EventLogGenerator(net);
  const simulationCase = generator.createCase();
  simulationCase.net.places.get('end').tokens = 1;
  assert.equal(generator.isCaseComplete(simulationCase), false);
  simulationCase.net.places.get('start').tokens = 0;
  assert.equal(generator.isCaseComplete(simulationCase), true);
});

test('an initially final Discovery case records no transition', async () => {
  const { net, transition } = createNet();
  net.finalMarkings = [{ start: 1 }];
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: 1 } }] };
  const generator = new EventLogGenerator(net, { eventLogFormat: 'classic' });
  const simulationCase = generator.createCase();
  await generator.processCase(simulationCase);
  assert.equal(simulationCase.steps, 0);
  assert.deepEqual(generator.eventLog, []);
});

test('concurrent attempts cannot apply an update calculated from stale data', async () => {
  const { net, transition } = createNet();
  net.places.get('start').tokens = 2;
  net.setDataValuation({ x: 0 });
  transition.postcondition = "x' = x + 1";
  const results = await Promise.all([net.fireTransition('t'), net.fireTransition('t')]);
  assert.deepEqual(results, [true, false]);
  assert.deepEqual(net.getDataValuation(), { x: 1 });
  assert.equal(net.places.get('start').tokens, 1);
});

test('JSON import rejects unknown or negative alternative final markings', () => {
  const { net } = createNet();
  for (const marking of [{ missing: 1 }, { end: -1 }, { end: 0.5 }]) {
    const data = JSON.parse(net.toJSON());
    data.finalMarkings = [marking];
    assert.throws(() => DataPetriNet.fromJSON(JSON.stringify(data)), /final marking/i);
  }
});

test('unsupported native relations remain displayable with an explicit diagnostic', async () => {
  const { net, transition } = createNet();
  for (const condition of ["x' > x", "(exists ((z Real)) (= x' z))"]) {
    transition.postcondition = condition;
    net.updateEnabledTransitions();
    assert.equal(transition.isEnabled, false);
    assert.match(transition.nativeExecutionError, /native|quantified|sampling/i);
    await assert.rejects(net.fireTransition('t'), /native|quantified|sampling/i);
  }
  transition.postcondition = "x' = 1";
  net.updateEnabledTransitions();
  assert.equal(transition.isEnabled, true);
  assert.equal(transition.nativeExecutionError, null);
  transition.precondition = 'invalid(';
  assert.throws(() => net.updateEnabledTransitions());
});

test('Discovery rejects null evidence and excludes Boolean symbolic updates', async () => {
  const { net, transition } = createNet();
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: null } }] };
  await assert.rejects(net.fireTransition('t'), /scalar/i);
  transition.discoveryContract = { generalized: true, observedPairs: [] };
  transition.postcondition = "x' = true";
  assert.equal(net.isTransitionEnabled('t'), false);
  transition.discoveryContract.observedPairs = [{ before: {}, after: { x: true } }];
  assert.equal(net.isTransitionEnabled('t'), true);
});

test('a Discovery deadlock terminates the case without claiming the final marking', async () => {
  const { net, transition } = createNet();
  transition.discoveryContract = { generalized: false, observedPairs: [] };
  const generator = new EventLogGenerator(net, { eventLogFormat: 'lifecycle' });
  const simulationCase = generator.createCase();
  generator.activeCases.push(simulationCase);
  assert.equal(await generator.processCase(simulationCase), false);
  assert.equal(simulationCase.state, 'deadlock');
  assert.equal(generator.activeCases.length, 0);
  assert.equal(generator.eventLog.at(-1).status, 'deadlock');
});

test('classic logs reject metadata-name collisions while lifecycle retains nested data', async () => {
  const { net, transition } = createNet();
  net.dataVariables.get('x').sourceName = 'concept:name';
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: true } }] };
  assert.throws(() => new EventLogGenerator(net, { eventLogFormat: 'classic' }), /lifecycle/i);
  const classic = new ProbabilisticEventLogGenerator(net, { eventLogFormat: 'classic' });
  await assert.rejects(classic.generateCases(1), /lifecycle/i);
  const lifecycle = new ProbabilisticEventLogGenerator(net, { eventLogFormat: 'lifecycle' });
  const rows = await lifecycle.generateCases(1);
  const activity = rows.find(row => row['concept:name'] === 'Activity' && row.variables_after);
  assert.deepEqual(JSON.parse(activity.variables_after), { 'concept:name': true });
});

test('Discovery v1 metadata retains complete snapshots without retained relations', () => {
  const { net } = createNet();
  const probabilistic = new ProbabilisticEventLogGenerator(net, { eventLogFormat: 'classic' });
  probabilistic.previousVariableValues.case = { x: 4 };
  probabilistic.logClassicEvent('case', 'A', new Date(), { x: 4 });
  assert.equal(probabilistic.eventLog[0].x, 4);
});

test('both classic event generators preserve a scalar named __proto__', async () => {
  const { net, transition } = createNet();
  net.dataVariables.get('x').sourceName = '__proto__';
  transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: 'kept' } }] };
  const legacy = new EventLogGenerator(net, { eventLogFormat: 'classic' });
  await legacy.processCase(legacy.createCase());
  const probabilistic = new ProbabilisticEventLogGenerator(net, { eventLogFormat: 'classic' });
  const rows = await probabilistic.generateCases(1);
  for (const row of [legacy.eventLog[0], rows[0]]) {
    assert.equal(Object.hasOwn(row, '__proto__'), true);
    assert.equal(row.__proto__, 'kept');
    assert.equal(row['concept:name'], 'Activity');
    assert.equal(Object.getPrototypeOf(row), Object.prototype);
  }
});

test('probabilistic logs distinguish a goal, deadlock, and continuing run at the step cap', async () => {
  for (const expected of ['goal', 'deadlock', 'max_steps_exceeded']) {
    const { net, transition } = createNet();
    transition.discoveryContract = { generalized: false, observedPairs: [{ before: {}, after: { x: 1 } }] };
    if (expected !== 'goal') net.finalMarkings = [{ end: 2 }];
    if (expected === 'max_steps_exceeded') {
      net.addTransition(new DataAwareTransition('loop', { x: 150, y: 0 }, 'Loop'));
      net.addArc(new Arc('loop-in', 'end', 'loop'));
      net.addArc(new Arc('loop-out', 'loop', 'end'));
    }
    const generator = new ProbabilisticEventLogGenerator(net, { eventLogFormat: 'lifecycle', maxStepsPerCase: 1 });
    const rows = await generator.generateCases(1);
    assert.equal(generator.cases[0].status, expected);
    assert.equal(rows.at(-1).status, expected);
  }
});
