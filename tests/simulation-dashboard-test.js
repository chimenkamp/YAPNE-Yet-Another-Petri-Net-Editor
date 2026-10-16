import assert from 'node:assert/strict';
import test from 'node:test';
import { PetriNetAPI } from '../src/petri-net-simulator.js';
import { DataPetriNetAPI } from '../src/extensions/dpn-api.js';
import { ProbabilisticExecutionIntegration } from '../src/extensions/probabilistic-integration.js';
import { SimulationDashboard } from '../src/simulation-dashboard.js';

/** Ignore a browser UI operation in the headless fixture. @returns {void} */
function ignoreUI() {}

globalThis.window = {};
globalThis.document = {
  createElement: ignoreUI,
  querySelector: ignoreUI,
  getElementById: ignoreUI
};
globalThis.alert = ignoreUI;
const { default: PetriNetApp } = await import('../src/petri-net-app.js');

/**
 * Build a real net whose final marking can leave a loop enabled.
 * @param {{ loop?: boolean, initiallyFinal?: boolean, alternative?: boolean }} options Net variants.
 * @returns {{ api: DataPetriNetAPI, start: string, goal: string, finish: string }} Net and identifiers.
 */
function createGoalApi({ loop = true, initiallyFinal = false, alternative = false } = {}) {
  const api = new DataPetriNetAPI('goal-net', 'Goal regression', '');
  const start = api.createPlace(0, 0, 'Start', initiallyFinal ? 0 : 1);
  const goal = api.createPlace(100, 0, 'Goal', initiallyFinal ? 1 : 0, 1);
  const finish = api.createDataTransition(50, 0, 'Finish');
  api.createArc(start, finish);
  api.createArc(finish, goal);
  if (loop) {
    const repeat = api.createDataTransition(150, 0, 'Repeat');
    api.createArc(goal, repeat);
    api.createArc(repeat, goal);
  }
  if (alternative) {
    const other = api.createDataTransition(50, 50, 'Alternative');
    api.createArc(start, other);
    api.createArc(other, goal);
  }
  return { api, start, goal, finish };
}

/**
 * Build a real nonterminal loop for step-limit checks.
 * @returns {DataPetriNetAPI} Net that remains active after firing.
 */
function createLoopApi() {
  const api = new DataPetriNetAPI('loop-net', 'Loop regression', '');
  const place = api.createPlace(0, 0, 'Work', 1);
  const repeat = api.createDataTransition(100, 0, 'Repeat');
  api.createArc(place, repeat);
  api.createArc(repeat, place);
  return api;
}

/**
 * Connect the actual app, dashboard, API, and optional engine to headless UI and timers.
 * @param {import('node:test').TestContext} context Test lifecycle and mocks.
 * @param {PetriNetAPI} api Real model API.
 * @param {boolean} probabilistic Whether to install the real probabilistic integration.
 * @returns {{ app: PetriNetApp, dashboard: SimulationDashboard, alerts: string[], timers: Map<number, () => Promise<void>>, indicator: { className: string }, statusText: { textContent: string } }} Fixture state.
 */
function createFixture(context, api, probabilistic = true) {
  const alerts = [];
  const timers = new Map();
  const indicator = { className: '' };
  const statusText = { textContent: '' };
  const banner = {
    /** Select a status node. @param {string} selector Node selector. @returns {typeof indicator | typeof statusText} Status node. */
    querySelector: selector => selector === '.status-indicator' ? indicator : statusText
  };
  const element = {
    classList: { add: ignoreUI, remove: ignoreUI },
    addEventListener: ignoreUI,
    /** Select the status banner. @param {string} selector Node selector. @returns {typeof banner | null} Matching node. */
    querySelector: selector => selector === '#sim-status-banner' ? banner : null
  };
  context.mock.method(document, 'createElement',
    /** Create a headless UI node. @returns {typeof element} UI node. */
    () => ({ ...element }));
  context.mock.method(document, 'querySelector',
    /** Omit page containers. @returns {null} No container. */
    () => null);
  context.mock.method(document, 'getElementById',
    /** Supply the WebPPL viewer button. @returns {typeof element} UI node. */
    () => element);
  context.mock.method(globalThis, 'alert',
    /** Record a dialog. @param {string} message Dialog text. @returns {number} Recorded dialog count. */
    message => alerts.push(message));
  context.mock.method(console, 'log', ignoreUI);
  let nextTimerId = 0;
  context.mock.method(globalThis, 'setInterval',
    /** Register a controlled tick. @param {() => Promise<void>} callback Timer callback. @returns {number} Timer identifier. */
    callback => {
      const id = ++nextTimerId;
      timers.set(id, callback);
      return id;
    });
  context.mock.method(globalThis, 'clearInterval',
    /** Remove a controlled tick. @param {number} id Timer identifier. @returns {boolean} Whether it was active. */
    id => timers.delete(id));

  const app = Object.create(PetriNetApp.prototype);
  app.api = api;
  app.editor = null;
  app.autoRunInterval = null;
  app.simulationStarted = false;
  app.initialState = null;
  app.updateTokensDisplay = ignoreUI;
  app.updateSelectedElementProperties = ignoreUI;
  if (probabilistic) {
    const integration = new ProbabilisticExecutionIntegration(app);
    integration.engine.reseed(1);
  }
  const dashboard = new SimulationDashboard(app);
  app.simDashboard = dashboard;
  return { app, dashboard, alerts, timers, indicator, statusText };
}

/**
 * Execute the dashboard's real interval callback once without wall-clock waiting.
 * @param {Map<number, () => Promise<void>>} timers Controlled active interval callbacks.
 * @returns {Promise<void>} Completion of one timer tick.
 */
async function tick(timers) {
  assert.equal(timers.size, 1, 'exactly one dashboard interval should be active');
  await timers.values().next().value();
}

test('auto-run stops at a final marking even when a loop remains enabled',
  /** Check loop termination. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { api, goal } = createGoalApi();
    const { dashboard, alerts, timers, indicator, statusText } = createFixture(context, api);
    dashboard.startAutoRun();
    await tick(timers);
    assert.equal(api.petriNet.places.get(goal).tokens, 1);
    assert.equal(api.getEnabledTransitions().length, 1, 'the final marking still enables Repeat');
    assert.equal(dashboard.isRunning, false);
    assert.equal(timers.size, 0);
    assert.equal(dashboard.autoRunTimer, null);
    assert.match(indicator.className, /completed/);
    assert.match(statusText.textContent, /goal state reached/i);
    assert.equal(dashboard.stepCount, 1);
    assert.deepEqual(dashboard.traceLog.map(
      /** Read fired labels. @param {{ transitions: string[] }} entry Trace entry. @returns {string[]} Fired labels. */
      entry => entry.transitions), [['Finish']]);
    await dashboard.step();
    assert.equal(dashboard.stepCount, 1, 'another step at the goal must not count a firing');
    assert.equal(dashboard.traceLog.length, 1);
    assert.deepEqual(alerts, []);
  });

test('an initially final marking stops without a step or trace',
  /** Check initial completion. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { api } = createGoalApi({ initiallyFinal: true });
    const { dashboard, alerts, timers, indicator } = createFixture(context, api);
    dashboard.startAutoRun();
    await tick(timers);
    assert.equal(dashboard.stepCount, 0);
    assert.deepEqual(dashboard.traceLog, []);
    assert.equal(timers.size, 0);
    assert.equal(dashboard.isRunning, false);
    assert.match(indicator.className, /completed/);
    assert.deepEqual(alerts, []);
  });

test('a final sink marking is completed rather than deadlocked',
  /** Check goal precedence. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { api } = createGoalApi({ loop: false });
    const { dashboard, timers, indicator, statusText } = createFixture(context, api);
    dashboard.startAutoRun();
    await tick(timers);
    assert.equal(api.getEnabledTransitions().length, 0);
    assert.equal(dashboard.stepCount, 1);
    assert.equal(dashboard.isRunning, false);
    assert.equal(timers.size, 0);
    assert.match(indicator.className, /completed/);
    assert.match(statusText.textContent, /goal state reached/i);
    await dashboard.step();
    assert.match(indicator.className, /completed/);
    assert.equal(dashboard.traceLog.length, 1);
  });

test('an actual deadlock stops without a phantom step or trace',
  /** Check deadlock termination. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { api, start } = createGoalApi({ loop: false });
    api.petriNet.places.get(start).tokens = 0;
    const { dashboard, alerts, timers, indicator, statusText } = createFixture(context, api);
    dashboard.startAutoRun();
    await tick(timers);
    assert.equal(dashboard.stepCount, 0);
    assert.deepEqual(dashboard.traceLog, []);
    assert.equal(timers.size, 0);
    assert.equal(dashboard.isRunning, false);
    assert.match(indicator.className, /deadlocked/);
    assert.match(statusText.textContent, /no enabled transitions|deadlock/i);
    assert.deepEqual(alerts, []);
  });

test('step limit keeps its completed status and never counts an extra step',
  /** Check step-limit termination. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { dashboard, timers, indicator, statusText } = createFixture(context, createLoopApi());
    dashboard.maxSteps = 1;
    dashboard.startAutoRun();
    await tick(timers);
    if (timers.size) await tick(timers);
    assert.equal(dashboard.stepCount, 1);
    assert.equal(dashboard.traceLog.length, 1);
    assert.equal(dashboard.isRunning, false);
    assert.equal(timers.size, 0);
    assert.match(indicator.className, /completed/);
    assert.match(statusText.textContent, /max steps reached/i);
    await dashboard.step();
    assert.equal(dashboard.stepCount, 1);
    assert.match(indicator.className, /completed/);
  });

test('default manual probabilistic steps alert while both silent entry points suppress alerts',
  /** Check alert options. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { api } = createGoalApi({ initiallyFinal: true });
    const { app, alerts } = createFixture(context, api);
    assert.equal((await app.stepSimulation()).status, 'goal');
    assert.equal(alerts.length, 1);
    assert.match(alerts[0], /goal state reached/i);
    await app.stepSimulation({ silent: true });
    await app.stepSimulationProbabilistic({ silent: true });
    assert.equal(alerts.length, 1);
  });

test('probabilistic trace records only the selected transition',
  /** Check scheduler trace labels. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const { api } = createGoalApi({ alternative: true });
    const fire = context.mock.method(api.petriNet, 'fireTransition');
    const { dashboard } = createFixture(context, api);
    await dashboard.step();
    assert.equal(fire.mock.callCount(), 1);
    const firedId = fire.mock.calls[0].arguments[0];
    const label = api.petriNet.transitions.get(firedId).label;
    assert.deepEqual(dashboard.traceLog.map(
      /** Read fired labels. @param {{ transitions: string[] }} entry Trace entry. @returns {string[]} Fired labels. */
      entry => entry.transitions), [[label]]);
  });

test('base application boolean success still records a real firing',
  /** Check base-step success compatibility. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const api = new PetriNetAPI('base-net', 'Base regression', '');
    const place = api.createPlace(0, 0, 'Start', 1);
    const transition = api.createTransition(100, 0, 'Consume');
    api.createArc(place, transition);
    const { dashboard, alerts } = createFixture(context, api, false);
    await dashboard.step();
    assert.equal(api.petriNet.places.get(place).tokens, 0);
    assert.equal(dashboard.stepCount, 1);
    assert.deepEqual(dashboard.traceLog.map(
      /** Read fired labels. @param {{ transitions: string[] }} entry Trace entry. @returns {string[]} Fired labels. */
      entry => entry.transitions), [['Consume']]);
    assert.deepEqual(alerts, []);
  });

test('base application boolean failure does not record a phantom step',
  /** Check base-step failure compatibility. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const api = new PetriNetAPI('base-net', 'Base failure regression', '');
    const place = api.createPlace(0, 0, 'Start', 1);
    const transition = api.createTransition(100, 0, 'Consume');
    api.createArc(place, transition);
    const { app, dashboard, alerts } = createFixture(context, api, false);
    const originalStep = app.stepSimulation;
    context.mock.method(app, 'stepSimulation',
      /** Disable the transition before the real base step. @param {{ silent?: boolean }} options Step options. @returns {Promise<boolean>} Base step result. */
      async options => {
        api.petriNet.places.get(place).tokens = 0;
        return originalStep.call(app, options);
      });
    await dashboard.step();
    assert.equal(dashboard.stepCount, 0);
    assert.deepEqual(dashboard.traceLog, []);
    assert.deepEqual(alerts, []);
  });

test('an unsuccessful active firing stops without claiming a goal or deadlock',
  /** Check unsuccessful firing status. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const api = createLoopApi();
    const { dashboard, alerts, timers, indicator, statusText } = createFixture(context, api);
    context.mock.method(api.petriNet, 'fireTransition',
      /** Inject an unsuccessful model firing. @returns {Promise<boolean>} Failed firing result. */
      async () => false);
    dashboard.startAutoRun();
    await tick(timers);
    assert.equal(api.getEnabledTransitions().length, 1);
    assert.equal(dashboard.stepCount, 0);
    assert.deepEqual(dashboard.traceLog, []);
    assert.equal(dashboard.isRunning, false);
    assert.equal(timers.size, 0);
    assert.doesNotMatch(indicator.className, /completed|deadlocked/);
    assert.doesNotMatch(statusText.textContent, /goal|deadlock/i);
    assert.deepEqual(alerts, []);
  });

test('a rejected firing propagates without recording a step or trace',
  /** Check rejection propagation. @param {import('node:test').TestContext} context Test lifecycle. @returns {Promise<void>} Assertions completed. */
  async context => {
    const api = createLoopApi();
    const { dashboard } = createFixture(context, api);
    const failure = new Error('Firing failed');
    context.mock.method(api.petriNet, 'fireTransition',
      /** Inject a rejected model firing. @returns {Promise<never>} Rejected firing. */
      async () => { throw failure; });
    await assert.rejects(dashboard.step(), failure);
    assert.equal(dashboard.stepCount, 0);
    assert.deepEqual(dashboard.traceLog, []);
  });

test('dashboard displays exact alternative goals without per-place final flags',
  /** Check imported goal display through the real API. @returns {void} Assertions completed. */
  () => {
    const { api, start, goal } = createGoalApi();
    for (const place of api.petriNet.places.values()) place.finalMarking = null;
    api.petriNet.finalMarkings = [{ [goal]: 1 }, {}];
    const container = { innerHTML: '', textContent: '' };
    const dashboard = Object.create(SimulationDashboard.prototype);
    dashboard.app = { api };
    dashboard.panel = {
      /** Select the final-marking output. @param {string} selector CSS selector. @returns {typeof container|null} Matching output. */
      querySelector: selector => selector === '#sim-final-markings' ? container : null
    };
    dashboard._updateFinalMarkings();
    assert.match(container.textContent, /no.*exact.*reached/i);
    assert.match(container.textContent, /2 alternative goals/);
    api.petriNet.places.get(start).tokens = 0;
    api.petriNet.places.get(goal).tokens = 1;
    dashboard._updateFinalMarkings();
    assert.match(container.textContent, /^an exact final marking.*reached/i);
    api.petriNet.places.get(start).tokens = 1;
    dashboard._updateFinalMarkings();
    assert.match(container.textContent, /no.*exact.*reached/i);
  });
