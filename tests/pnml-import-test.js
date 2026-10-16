import { PNMLImporter } from '../src/extensions/pnml-importer.js';
import { DataPetriNet } from '../src/extensions/dpn-model.js';
import { EventLogGenerator } from '../src/event-log-generator.js';
import { assessGuardCompatibility } from '../src/extensions/guard-language/guard-compatibility.js';
import { SuvorovLomazovaVerifier } from '../src/extensions/soundness-verification/suvorov-lomazova/suvorov-lomazova-verifier.js';

/** Assert an import invariant in the browser's real XML implementation. */
function assert(condition, message) {
  if (!condition) throw new Error(message);
}

/** Exercise the actual PNML reader without constructing editor UI. */
export async function runPnmlImportTests() {
  const reader = Object.create(PNMLImporter.prototype);
  const legacy = reader.parsePNML(`<pnml><net id="discovered"><page id="page0">
    <place id="p0"><initialMarking><text>1</text></initialMarking></place>
    <place id="p1"/>
    <transition id="setup"><name><text>Setup</text></name>
      <toolspecific tool="dpn-discovery" version="1.0"><guard>true</guard></toolspecific>
      <toolspecific tool="dpn-discovery" version="1.0">
        <update variable="a">0</update><update variable="b">1</update>
        <update variable="temp">(+ a b)</update>
      </toolspecific>
    </transition>
    <arc id="in" source="p0" target="setup"/><arc id="out" source="setup" target="p1"/>
    </page><toolspecific tool="dpn-discovery" version="1.0">
      <variable name="a"/><variable name="b"/><variable name="temp"/>
    </toolspecific></net></pnml>`);
  assert(legacy.dataVariables.length === 3, 'Discovery variables must be extracted');
  assert(legacy.transitions[0].precondition === 'true', 'Discovery guard must be retained');
  assert(legacy.transitions[0].postcondition.includes("temp'"), 'Discovery updates must become primed equalities');
  assert(legacy.dataVariables.every(variable => variable.requiresInitialValue), 'Missing legacy initial values require user input');
  const native = reader.parsePNML(`<pnml><net id="native"><page id="page">
    <place id="p"/><transition id="t"><dataGuard><text>x &gt; 0</text></dataGuard>
    <dataUpdate><text>x' = x + 1</text></dataUpdate></transition></page>
    <dataVariables><variable id="v" type="int"><name>x</name><initialValue><text>2</text></initialValue></variable></dataVariables>
    </net></pnml>`);
  assert(native.transitions[0].postcondition.includes("x'"), 'Explicit dataUpdate must not be overwritten');
  assert(native.dataVariables[0].currentValue === 2, 'Typed initial value must survive');
  const finite = reader.parsePNML(`<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml"><net id="finite"><page id="page">
    <place id="p0"><initialMarking><text>1</text></initialMarking></place><place id="p1"/>
    <transition id="t"><toolspecific tool="dpn-discovery" version="2.0"><contract generalized="false" observedPairCount="1">
      <observedPair><before>{}</before><after>{"status":"ready"}</after></observedPair>
    </contract></toolspecific></transition></page>
    <toolspecific tool="dpn-discovery" version="1.0"><variable name="status"/></toolspecific>
    <toolspecific tool="dpn-discovery" version="2.0"><finalmarkings><marking><place idref="p1"><text>1</text></place></marking></finalmarkings></toolspecific>
    </net></pnml>`);
  assert(finite.places.length === 2, 'Final marking references must not become places');
  assert(finite.finalMarkings[0].p1 === 1, 'Explicit final marking must be preserved');
  assert(finite.transitions[0].discoveryContract.observedPairs[0].after.status === 'ready', 'Finite relation must be retained');
  assert(finite.dataVariables[0].currentValue === undefined, 'Initial finite-relation valuation must be empty');
  assert(finite.dataVariables[0].type === 'data', 'Mixed event data must not become a numeric variable');
  const plain = reader.parsePNML('<pnml><net id="n"><page id="p"><place id="p0"/><transition id="t"/></page></net></pnml>');
  assert(plain.transitions[0].precondition === '', 'Plain PNML must stay unguarded');
  let rejected = false;
  try { reader.parsePNML('<pnml><net><page><arc source="missing" target="unknown"/></page></net></pnml>'); }
  catch { rejected = true; }
  assert(rejected, 'Broken references must be rejected before replacing the editor model');
  checkImportBoundaries(reader);
  checkLegacyIdentifierBoundaries(reader);
  await checkExporterFixtures(reader);
  await checkSuppliedExample(reader);
  return 'PNML import tests passed';
}

/** Build an old Discovery expression with its declared original identifier. */
function legacyExpressionPnml(name, expression, element = 'guard') {
  return `<pnml><net id="legacy"><page id="page"><transition id="t">
    <toolspecific tool="dpn-discovery"><${element} variable="result">${expression}</${element}></toolspecific>
    </transition></page><toolspecific tool="dpn-discovery"><variable name="${name}"/></toolspecific></net></pnml>`;
}

/** Refuse old unescaped names instead of silently importing a different formula. */
function checkLegacyIdentifierBoundaries(reader) {
  for (const [name, expression, element] of [
    ['x-y', '21/2 &gt;= x-y', 'guard'],
    ['true', 'true &gt; 0', 'guard'],
    ['x_r', 'x_r &gt; 0', 'guard'],
    ['true', 'true', 'update']
  ]) {
    let failure;
    try { reader.parsePNML(legacyExpressionPnml(name, expression, element)); }
    catch (error) { failure = error; }
    assert(failure && /ambiguous.*identifier.*re-export/i.test(failure.message), `Legacy ${name}: ambiguous identifiers require re-export`);
  }
  const unconditional = reader.parsePNML(legacyExpressionPnml('true', 'true'));
  assert(unconditional.transitions[0].precondition === 'true', 'Legacy unconditional true must remain usable');
  const quoted = reader.parsePNML(legacyExpressionPnml('x-y', '(&gt; |x-y| 0)'));
  assert(quoted.dataVariables.length === 1 && quoted.transitions[0].precondition.includes('|x-y|'), 'Explicitly quoted legacy names must remain exact');
  const unrelated = reader.parsePNML(legacyExpressionPnml('x-y', 'x-y_other &gt; 0'));
  assert(unrelated.transitions[0].precondition.includes('y_other'), 'A declared name must not match a longer unrelated identifier');
}

/** Cover capture avoidance and identifiers before maps can discard imported data. */
function checkImportBoundaries(reader) {
  const input = `<pnml><net id="n"><page id="page"><place id="p"/><transition id="t">
    <toolspecific tool="dpn-discovery" version="1.0"><guard syntax="smtlib2">(let ((local 10)) (&gt; dpn_var_0 local))</guard></toolspecific>
    </transition></page><toolspecific tool="dpn-discovery" version="1.0"><variable name="local" symbol="dpn_var_0"/></toolspecific></net></pnml>`;
  const parsed = reader.parsePNML(input);
  parsed.dataVariables[0].currentValue = 12;
  const net = DataPetriNet.fromJSON(JSON.stringify(parsed));
  assert(net.transitions.get('t').evaluatePrecondition({ local: 12 }), 'Free variables must not be captured by imported let bindings');
  const missing = reader.parsePNML(`<pnml><net id="n"><page id="page"><transition id="t" guard="y &gt; x"/></page>
    <dataVariables><variable id="variable_1" type="real"><name>x</name><initialValue>1</initialValue></variable></dataVariables></net></pnml>`);
  assert(new Set(missing.dataVariables.map(variable => variable.id)).size === 2, 'Inferred variables need distinct IDs');
  const native = reader.parsePNML(`<pnml><net id="n"><page id="p"><transition id="t" guard="x &gt; 0"/></page>
    <dataVariables><variable id="v" type="real"><name>x</name><initialValue>1</initialValue></variable></dataVariables></net></pnml>`);
  assert(native.transitions[0].precondition === 'x > 0', 'Valid existing infix must remain usable by the legacy WebPPL translator');
  let rejected = false;
  try { reader.parsePNML('<pnml><net><page><transition id="t"/><place id="p"/><arc id="a" source="p" target="t"/><arc id="a" source="t" target="p"/></page></net></pnml>'); }
  catch { rejected = true; }
  assert(rejected, 'Duplicate arc IDs must not silently collapse');
}

/** Run genuine exports from every solver through import, execution and log generation. */
async function checkExporterFixtures(reader) {
  for (const backend of ['z3', 'cvc5', 'yices2']) {
    const response = await fetch(`./fixtures/discovery-${backend}.pnml`);
    assert(response.ok, `${backend}: fixture must load`);
    const parsed = reader.parsePNML(await response.text());
    const net = DataPetriNet.fromJSON(JSON.stringify(parsed));
    assert(Object.keys(net.getDataValuation()).length === 0, `${backend}: initial state must be empty`);
    const initial = [...net.transitions.values()].find(transition => transition.label === 'Initialize');
    const update = [...net.transitions.values()].find(transition => transition.label === 'Swap and increment');
    assert(await net.fireTransition(initial.id), `${backend}: initialize must fire`);
    assert(net.getDataValuation(true)['x|y'] === 7, `${backend}: original pipe name must survive`);
    assert(net.getDataValuation(true)['x\\y'] === 11, `${backend}: original backslash name must survive`);
    assert(await net.fireTransition(update.id, () => 0.99), `${backend}: update must fire`);
    assert(net.getDataValuation().x === 3 && net.getDataValuation().y === 3, `${backend}: assignments must use old values`);
    const restored = reader.parsePNML(net.toPNML());
    assert(restored.transitions.some(transition => transition.discoveryContract), `${backend}: PNML roundtrip must preserve contracts`);
    const fresh = DataPetriNet.fromJSON(JSON.stringify(parsed));
    const generator = new EventLogGenerator(fresh, { seed: 7, eventLogFormat: 'classic' });
    await generator.simulateCases(2, 10);
    const activities = generator.eventLog.filter(event => event['concept:name'] === 'Swap and increment');
    assert(activities.length === 2, `${backend}: each case must log the update`);
    assert(activities.every(event => event['x|y'] === 7), `${backend}: complete event payload must retain original names`);
  }
}

/** Execute the user's exact transition/arc example with explicit initial data choices. */
async function checkSuppliedExample(reader) {
  const response = await fetch('./fixtures/discovery-prefix-example.pnml');
  const parsed = reader.parsePNML(await response.text());
  assert(parsed.places.length === 7 && parsed.transitions.length === 7, 'Supplied example structure must survive');
  for (const variable of parsed.dataVariables) {
    variable.currentValue = variable.name === 'n' ? 7 : 0;
    variable.initialValue = variable.currentValue;
    variable.requiresInitialValue = false;
  }
  assert(assessGuardCompatibility(parsed).simulation.supported, 'Supplied grammar must support native simulation');
  const net = DataPetriNet.fromJSON(JSON.stringify(parsed));
  const sequence = ['t_T_Setup_7', 't_T_CheckLoop_3', 't_T_CalcTemp_1', 't_T_SetA_5', 't_T_SetB_6', 't_T_IncI_4'];
  for (const transition of sequence) assert(await net.fireTransition(transition), `${transition} must fire`);
  const values = net.getDataValuation();
  assert(values.a === 1 && values.b === 1 && values.i === 2 && values.n === 7, 'Supplied formulas must preserve their actual values');
  let rejected = false;
  try { new SuvorovLomazovaVerifier(net); }
  catch (error) { rejected = /arithmetic|soundness.*grammar/i.test(error.message); }
  assert(rejected, 'Arithmetic model must be refused by the paper soundness gate');
}
