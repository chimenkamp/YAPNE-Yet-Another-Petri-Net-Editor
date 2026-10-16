import { readPNML, parseInitialValue } from '../src/extensions/pnml-reader.js';

/** Assert one PNML numeric boundary requirement in the real browser parser. */
function assert(condition, message) {
  if (!condition) throw new Error(message);
}

/** Require an explicit numeric-range error instead of a silently rounded value. */
function rejectsUnsafe(action, label) {
  let failure;
  try { action(); } catch (error) { failure = error; }
  assert(failure && /safe integer/i.test(failure.message), `${label}: unsafe integer must be rejected explicitly`);
}

/** Create a retained-relation PNML document with the supplied raw JSON number. */
function observedPnml(number) {
  return `<pnml><net id="numeric"><page id="page"><transition id="t">
    <toolspecific tool="dpn-discovery"><contract generalized="false" observedPairCount="1">
    <observedPair><before>{}</before><after>{"x":${number},"text":"9007199254740993","flag":true}</after></observedPair>
    </contract></toolspecific></transition></page></net></pnml>`;
}

/** Embed a raw serialized YAPNE model while retaining the original numeric text. */
function savedModelPnml(dataVariables, transitions = '[]') {
  return `<pnml><net id="saved"><toolspecific tool="YAPNE"><model-json>
    {"id":"n","places":[],"arcs":[],"transitions":${transitions},"dataVariables":${dataVariables}}
    </model-json></toolspecific></net></pnml>`;
}

/** Check unsafe integers at declaration, observed-relation, and saved-model boundaries. */
export function runPnmlNumericTests() {
  for (const number of ['9007199254740993', '-9007199254740993', '9007199254740992', '9.007199254740993e15', '9007199254740993.0']) {
    for (const type of ['real', 'int', 'data']) {
      rejectsUnsafe(() => parseInitialValue(number, type), `${type} initial ${number}`);
    }
    rejectsUnsafe(() => readPNML(observedPnml(number)), `retained value ${number}`);
    for (const field of ['currentValue', 'initialValue']) {
      rejectsUnsafe(() => readPNML(savedModelPnml(`[{"id":"x","name":"x","type":"data","${field}":${number}}]`)), `saved ${field} ${number}`);
      for (const type of ['real', 'int']) {
        rejectsUnsafe(() => readPNML(savedModelPnml(`[{"id":"x","name":"x","type":"${type}","${field}":"${number}"}]`)), `saved ${type} string ${field} ${number}`);
      }
    }
  }
  const relation = '[{"id":"t","label":"T","discoveryContract":{"generalized":false,"observedPairs":[{"before":{},"after":{"x":9007199254740993}}]}}]';
  rejectsUnsafe(() => readPNML(savedModelPnml('[]', relation)), 'saved retained relation');
  for (const number of ['9007199254740991', '-9007199254740991', '1.25', '1e-7']) {
    assert(parseInitialValue(number, 'real') === Number(number), `supported real ${number}`);
    const parsed = readPNML(observedPnml(number));
    const after = parsed.transitions[0].discoveryContract.observedPairs[0].after;
    assert(after.x === Number(number), `supported retained value ${number}`);
    assert(after.text === '9007199254740993' && after.flag === true, 'String and Boolean data must preserve their types');
  }
  const restored = readPNML(savedModelPnml('[{"id":"x","name":"x","type":"data","initialValue":1e-7,"currentValue":1.25}]'));
  assert(restored.dataVariables[0].initialValue === 1e-7 && restored.dataVariables[0].currentValue === 1.25, 'Supported saved numeric state must survive');
  const text = readPNML(savedModelPnml('[{"id":"x","name":"x","type":"data","initialValue":"9007199254740993","currentValue":"9007199254740993"}]'));
  assert(text.dataVariables[0].currentValue === '9007199254740993' && text.dataVariables[0].initialValue === '9007199254740993', 'Saved data strings must remain exact strings');
  const typed = readPNML(savedModelPnml('[{"id":"x","name":"x","type":"real","initialValue":"1e-7","currentValue":"1.25"}]'));
  assert(Number(typed.dataVariables[0].currentValue) === 1.25 && Number(typed.dataVariables[0].initialValue) === 1e-7, 'Supported saved numeric strings must survive');
  return 'PNML numeric tests passed';
}
