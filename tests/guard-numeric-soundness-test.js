import test from 'node:test';
import assert from 'node:assert/strict';
import { init } from 'z3-solver';
import { parse } from '../src/extensions/guard-language/guard-parser.js';
import { toSmtLib2, toSmtLib2ForTau } from '../src/extensions/guard-language/guard-smt-emitter.js';
import { assessGuardCompatibility } from '../src/extensions/guard-language/guard-compatibility.js';
import { SmtFromDpnGenerator } from '../src/extensions/soundness-verification/suvorov-lomazova/smt-generator.js';
import { EvalError, EvaluationDomainError, evaluatePrecondition, evaluatePostcondition, checkConstraint } from '../src/extensions/guard-language/guard-evaluator.js';
import { DataPetriNet } from '../src/extensions/dpn-model.js';

/** Unsafe integer tokens must never be silently rounded during guard import. */
test('integer literals reject values outside the safe range, including rational operands', () => {
  for (const expression of ['(= x 9007199254740993)', '(= x -9007199254740993)',
    '(= x (/ 9007199254740993 3))', '(= x 1/9007199254740993)', 'x == 9007199254740992']) {
    assert.throws(() => parse(expression), /safe integer/i, expression);
  }
  for (const expression of ['(= x 9007199254740991)', '(= x -9007199254740991)',
    '(= x 1.5)', '(= x 1e-7)', '(= x 1e21)']) {
    assert.doesNotThrow(() => parse(expression), expression);
  }
});

/** Standard SMT decimals and unary minus must survive both emitter paths. */
test('scientific numeric values emit decimal SMT terms accepted by Z3', async () => {
  const { Context } = await init();
  const context = new Context('numeric_guard_emission');
  const samples = [
    ['0.0000001', '0.0000001'],
    ['-1.25e-7', '(- 0.000000125)'],
    ['1e21', '1000000000000000000000.0'],
    ['-1e21', '(- 1000000000000000000000.0)'],
    ['1.0', '1.0'],
    ['-2', '(- 2)'],
    ['5e-324', `0.${'0'.repeat(323)}5`],
    ['1.7976931348623157e308', `17976931348623157${'0'.repeat(292)}.0`],
  ];
  for (const [input, expected] of samples) {
    const ast = parse(`(= x' ${input})`, { isPostcondition: true }).ast;
    const stepped = toSmtLib2(ast, 0, [['x', 'Real']], true);
    const tau = toSmtLib2ForTau(ast, 0, [['x', 'Real']]);
    assert.equal(stepped, `(= x_1 ${expected})`, input);
    assert.equal(tau, `(= x_w ${expected})`, input);
    const solver = new context.Solver();
    solver.fromString(`(declare-const x_1 Real) (declare-const x_w Real) (assert ${stepped}) (assert ${tau})`);
    assert.equal(await solver.check(), 'sat', input);
  }
});

/** Initial data must use the same valid numeric syntax as transition predicates. */
test('initial SMT data expands exponents and rejects non-finite values', () => {
  const generator = new SmtFromDpnGenerator();
  const net = { places: [], transitions: [], arcs: [], dataVariables: [{ name: 'x', type: 'real', currentValue: 1e-7 }] };
  assert.match(generator.generateSMT(net, { K: 0 }), /\(assert \(= x_0 0\.0000001\)\)/);
  assert.match(generator.generateSMT(net, { K: 0, initialData: { x: -1e21 } }), /\(assert \(= x_0 \(- 1000000000000000000000\.0\)\)\)/);
  assert.throws(() => generator.generateSMT(net, { K: 0, initialData: { x: Infinity } }), /finite/);
});

/** Compare only operands belonging to a compatible paper-supported domain. */
test('soundness eligibility rejects incompatible Boolean and numeric operands', () => {
  const variables = [{ name: 'flag', type: 'bool' }, { name: 'other', type: 'boolean' }, { name: 'x', type: 'real' }];
  for (const expression of ['flag > 0', '(= flag 1)', '(distinct x flag)',
    '(and true (= flag x))', '(= (- true) false)', '(< flag other)']) {
    const profile = assessGuardCompatibility({ dataVariables: variables, transitions: [{ precondition: expression }] }).soundness;
    assert.equal(profile.supported, false, expression);
    assert.match(profile.reasons.join(' '), /type|Boolean|numeric/i);
  }
  for (const expression of ['(= flag true)', '(distinct flag other)', '(> x -1)',
    '(<= -1 0.5 x)', '(and (= flag false) (> x 0))']) {
    assert.equal(assessGuardCompatibility({ dataVariables: variables, transitions: [{ precondition: expression }] }).soundness.supported, true, expression);
  }
  assert.equal(assessGuardCompatibility({ dataVariables: variables, transitions: [{ postcondition: "(= flag' x)" }] }).soundness.supported, false);
  assert.equal(assessGuardCompatibility({ dataVariables: variables, transitions: [{ postcondition: "(and (= flag' true) (= x' 1))" }] }).soundness.supported, true);
});

/** Recognize an explicit precision failure that cannot be treated as a missing branch. */
function isPrecisionError(error) {
  return error instanceof EvalError && !(error instanceof EvaluationDomainError) && /safe integer/i.test(error.message);
}

/** Reject unsafe operands and intermediate results before later arithmetic hides them. */
test('native arithmetic rejects unsafe integer operands and every intermediate result', () => {
  for (const rhs of ['(+ x 1)', '(- x -1)', '(* x 2)', '(/ x 0.5)',
    '(+ x 1 -1)', '(- x -1 1)', '(* x 2 0)', '(/ x 0.5 2)', '1e21']) {
    const ast = parse(`(= x' ${rhs})`, { isPostcondition: true }).ast;
    assert.throws(() => evaluatePostcondition(ast, { x: Number.MAX_SAFE_INTEGER }), isPrecisionError, rhs);
  }
  for (const expression of ['(= x x)', '(< x 1)', '(= (- x) 0)']) {
    assert.throws(() => evaluatePrecondition(parse(expression).ast, { x: Number.MAX_SAFE_INTEGER + 1 }), isPrecisionError, expression);
  }
  const constraint = parse("(= x' x')", { isPostcondition: true }).ast;
  assert.throws(() => checkConstraint(constraint, {}, { x: Number.MAX_SAFE_INTEGER + 1 }), isPrecisionError);
  const fractional = parse("(= x' (+ 0.1 0.2))", { isPostcondition: true }).ast;
  assert.equal(evaluatePostcondition(fractional, {}).assignments.get('x'), 0.1 + 0.2);
});

/** Overflow must leave the real model unchanged, even when observed evidence could fire. */
test('unsafe generalized arithmetic rejects firing without mutating tokens or data', async () => {
  for (const observed of [false, true]) {
    const transition = { id: 't', label: 'Increment', precondition: 'true', postcondition: "x' = x + 1" };
    if (observed) transition.discoveryContract = { generalized: true, observedPairs: [
      { before: { x: Number.MAX_SAFE_INTEGER }, after: { x: 0 } }
    ] };
    const net = DataPetriNet.fromJSON(JSON.stringify({
      id: 'numeric', places: [{ id: 'start', tokens: 1 }, { id: 'end', tokens: 0 }],
      transitions: [transition], arcs: [{ id: 'in', source: 'start', target: 't', weight: 1 }, { id: 'out', source: 't', target: 'end', weight: 1 }],
      dataVariables: [{ id: 'x', name: 'x', type: observed ? 'data' : 'real', initialValue: Number.MAX_SAFE_INTEGER, currentValue: Number.MAX_SAFE_INTEGER }]
    }));
    await assert.rejects(net.fireTransition('t'), isPrecisionError);
    assert.equal(net.places.get('start').tokens, 1);
    assert.equal(net.places.get('end').tokens, 0);
    assert.deepEqual(net.getDataValuation(), { x: Number.MAX_SAFE_INTEGER });
  }
});
