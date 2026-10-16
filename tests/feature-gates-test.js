import assert from 'node:assert/strict';
import test from 'node:test';
import vm from 'node:vm';
import { DataPetriNet, DataVariable, DataAwareTransition } from '../src/extensions/dpn-model.js';
import { Place, Arc, PetriNetAPI } from '../src/petri-net-simulator.js';
import { ProbabilisticExecutionEngine } from '../src/extensions/probabilistic-execution.js';
import { WebPPLCodeGenerator } from '../src/extensions/webppl-code-generator.js';
import { assessGuardCompatibility } from '../src/extensions/guard-language/guard-compatibility.js';

/** Build a runnable one-step arithmetic net for feature-boundary checks. */
function netWithUpdate() {
  const net = new DataPetriNet('n');
  net.addPlace(new Place('p0', { x: 0, y: 0 }, '', 1));
  net.addPlace(new Place('p1', { x: 100, y: 0 }, '', 0, null, 1));
  net.addDataVariable(new DataVariable('x', 'x', 'real', 1));
  net.addTransition(new DataAwareTransition('t', { x: 50, y: 0 }, 'step', 1, 0, 'true', "(= x' (+ x 1))"));
  net.addArc(new Arc('a', 'p0', 't')); net.addArc(new Arc('b', 't', 'p1'));
  return net;
}

test('WebPPL rejects writes without a verified scheduler translation', () => {
  assert.throws(() => new WebPPLCodeGenerator().generateCode(netWithUpdate()), /sampling|scheduler|unsupported/i);
});

test('explicit WebPPL step cannot silently run native execution', async () => {
  const engine = new ProbabilisticExecutionEngine({ executionMode: 'webppl' });
  await assert.rejects(engine.step(netWithUpdate()), /native|full.*simulation/i);
});

test('full WebPPL execution does not fall back to another probability model', async () => {
  const engine = new ProbabilisticExecutionEngine({ executionMode: 'webppl' });
  engine.runWebPPLSimulation = async () => { throw new Error('Inference unavailable'); };
  await assert.rejects(engine.runFullSimulation(netWithUpdate()), /Inference unavailable/);
});

test('alternative final markings are exact and usable without per-place flags', () => {
  const net = netWithUpdate();
  net.places.get('p1').finalMarking = null;
  net.finalMarkings = [{ p1: 1 }];
  const engine = new ProbabilisticExecutionEngine();
  assert.doesNotThrow(() => engine.validateGoalStateDefinition(net));
  assert.equal(engine.checkGoalState(net).isGoal, false);
  net.places.get('p0').tokens = 0; net.places.get('p1').tokens = 1;
  assert.equal(engine.checkGoalState(net).reason, 'final_marking_reached');
  net.places.get('p0').tokens = 1;
  assert.equal(engine.checkGoalState(net).isGoal, false);
});

test('native engine passes its configured random source to observed choices', async () => {
  const net = netWithUpdate();
  net.transitions.get('t').discoveryContract = { generalized: false, observedPairs: [
    { before: { x: 1 }, after: { x: 2 } }, { before: { x: 1 }, after: { x: 3 } }
  ] };
  const engine = new ProbabilisticExecutionEngine({ seed: 10 });
  engine.random = () => 0.9;
  await engine.step(net);
  assert.equal(net.getDataValuation().x, 3);
});

test('paper execution validates compatibility before loading its backend', async () => {
  const engine = new ProbabilisticExecutionEngine({ executionMode: 'webppl' });
  let loaded = false;
  engine.getWebPPL = async () => { loaded = true; return null; };
  const net = netWithUpdate();
  await assert.rejects(engine.runWebPPLSimulation(net), /unsupported.*scheduler|sampling/i);
  assert.equal(loaded, false);
  assert.equal(net.places.get('p0').tokens, 1);
});

test('an unavailable explicit paper backend rejects without native mutation', async () => {
  const engine = new ProbabilisticExecutionEngine({ executionMode: 'webppl' });
  engine.getWebPPL = async () => null;
  const net = netWithUpdate();
  net.transitions.get('t').postcondition = '';
  await assert.rejects(engine.runWebPPLSimulation(net), /WebPPL.*unavailable/i);
  assert.equal(net.places.get('p0').tokens, 1);
  assert.equal(net.getDataValuation().x, 1);
});

test('refused native firing reports failure without a successful trace', async () => {
  const net = netWithUpdate();
  net.fireTransition = async () => false;
  const engine = new ProbabilisticExecutionEngine();
  assert.equal((await engine.stepNative(net)).status, 'failed');
  const result = await engine.runNativeSimulation(net);
  assert.equal(result.status, 'failed');
  assert.deepEqual(result.trace, []);
});

test('a final marking reached at the native step cap is still a goal', async () => {
  const net = netWithUpdate();
  net.finalMarkings = [{ p1: 1 }];
  const engine = new ProbabilisticExecutionEngine({ maxSteps: 1 });
  const result = await engine.runNativeSimulation(net);
  assert.equal(result.status, 'goal');
  assert.equal(result.traceLength, 1);
  assert.equal(result.goalDetails.exactFinalMarking, true);
});

test('final-marking API checks exact alternatives independently of display flags', () => {
  const net = netWithUpdate();
  net.finalMarkings = [{ p1: 1 }, {}];
  const api = Object.create(PetriNetAPI.prototype);
  api.petriNet = net;
  net.places.get('p1').tokens = 1;
  assert.equal(api.checkFinalMarkings().allSatisfied, false, 'extra tokens prevent an exact final marking');
  net.places.get('p0').tokens = 0;
  let result = api.checkFinalMarkings();
  assert.equal(result.exactFinalMarkings, true);
  assert.deepEqual(result.finalMarkingAlternatives.map(alternative => alternative.reached), [true, false]);
  assert.equal(result.allSatisfied, true);
  net.places.get('p1').tokens = 0;
  result = api.checkFinalMarkings();
  assert.equal(result.allSatisfied, true, 'the empty marking is a valid alternative goal');
});

test('generated paper goals preserve exact alternatives for live and JSON nets', () => {
  const net = netWithUpdate();
  net.transitions.get('t').postcondition = '';
  net.places.get('p1').finalMarking = null;
  net.finalMarkings = [{ p1: 1 }, {}];
  const generator = new WebPPLCodeGenerator({ maxSteps: 1 });
  for (const input of [net, JSON.parse(net.toJSON())]) {
    const code = generator.generateCode(input, { includeComments: false });
    assert.match(code, /state\.marking\["p0"\] === 0/);
    const normalized = generator.normalizeNet(input);
    const check = vm.runInNewContext(`${generator.generateGoalStateCheck(normalized, false)}; isGoalState`);
    assert.equal(check({ marking: { p0: 0, p1: 1 } }), true);
    assert.equal(check({ marking: { p0: 1, p1: 1 } }), false);
    assert.equal(check({ marking: { p0: 0, p1: 2 } }), false);
    assert.equal(check({ marking: { p0: 0, p1: 0 } }), true);
  }
});

test('the real WebPPL backend accepts its store/result callback and reaches the goal at the cap', async () => {
  for (const exact of [false, true]) {
    const net = netWithUpdate();
    net.transitions.get('t').postcondition = '';
    if (exact) {
      net.finalMarkings = [{ p1: 1 }, {}];
      net.places.get('p1').finalMarking = null;
    }
    const engine = new ProbabilisticExecutionEngine({ executionMode: 'webppl', maxSteps: 1 });
    const result = await engine.runWebPPLSimulation(net);
    assert.equal(result.executionMode, 'webppl');
    assert.equal(result.status, 'goal');
    assert.equal(result.traceLength, 1);
    assert.equal(net.places.get('p0').tokens, 0);
    assert.equal(net.places.get('p1').tokens, 1);
  }
});

test('paper profile and code generation reject special arcs without disabling native simulation', () => {
  for (const type of ['read', 'inhibitor', 'reset']) {
    const net = netWithUpdate();
    net.transitions.get('t').postcondition = '';
    net.arcs.get('a').type = type;
    for (const input of [net, JSON.parse(net.toJSON())]) {
      const profile = assessGuardCompatibility(input);
      assert.equal(profile.simulation.supported, true);
      assert.equal(profile.probabilistic.supported, false);
      assert.match(profile.probabilistic.reasons.join(' '), /regular arcs/i);
      assert.throws(() => new WebPPLCodeGenerator().generateCode(input), /regular arcs/i);
    }
  }
});

test('paper profile rejects parallel endpoint arcs', () => {
  const net = netWithUpdate();
  net.transitions.get('t').postcondition = '';
  assert.equal(assessGuardCompatibility(net).probabilistic.supported, true);
  net.addArc(new Arc('parallel', 'p0', 't'));
  assert.match(assessGuardCompatibility(net).probabilistic.reasons.join(' '), /parallel arcs/i);
  assert.throws(() => new WebPPLCodeGenerator().generateCode(net), /parallel arcs/i);
  net.arcs.delete('parallel');
  assert.equal(assessGuardCompatibility(net).probabilistic.supported, true);
});

test('paper profile rejects finite place capacities including zero', () => {
  const net = netWithUpdate();
  net.transitions.get('t').postcondition = '';
  for (const capacity of [0, 1]) {
    net.places.get('p1').capacity = capacity;
    for (const input of [net, JSON.parse(net.toJSON())]) {
      assert.equal(assessGuardCompatibility(input).simulation.supported, true);
      assert.match(assessGuardCompatibility(input).probabilistic.reasons.join(' '), /capacities/i);
      assert.throws(() => new WebPPLCodeGenerator().generateCode(input), /capacities/i);
    }
  }
  net.places.get('p1').capacity = null;
  assert.equal(assessGuardCompatibility(net).probabilistic.supported, true);
});
