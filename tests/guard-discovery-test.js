import test from 'node:test';
import assert from 'node:assert/strict';
import * as parser from '../src/extensions/guard-language/guard-parser.js';
import * as evaluator from '../src/extensions/guard-language/guard-evaluator.js';
import { validatePostcondition } from '../src/extensions/guard-language/guard-validator.js';

/** Parse a guard and evaluate it in a supplied state. */
function evaluate(expression, values = {}) {
  return evaluator.evaluatePrecondition(parser.parse(expression).ast, values);
}

/** Discovery prefix arithmetic and legacy Z3/infix grouping share semantics. */
test('discovery prefix, legacy Z3, and grouped infix preserve their meaning', () => {
  assert.equal(evaluate('(< (+ 99/2 (* -1 score)) 0)', { score: 50 }), true);
  assert.equal(evaluate('And(score > 1, Or(score < 3, Not(flag)), If(flag, score == 2, score == 5))', { score: 5, flag: false }), true);
  assert.equal(evaluate('(score > 1) and (score < 3 or !flag)', { score: 5, flag: false }), true);
  assert.equal(evaluate('(-score + 2) < 0', { score: 5 }), true);
  assert.equal(evaluate('(- score + 2) < 0', { score: 5 }), true);
  assert.equal(evaluate('(not flag and score > 1)', { score: 5, flag: false }), true);
  assert.equal(evaluate('(And(score > 1, Not(flag)))', { score: 5, flag: false }), true);
});

/** Quoted identifiers preserve original names without making keywords ambiguous. */
test('quoted names and primes round trip through canonical guards', () => {
  const { ast } = parser.parse('(and (= |amount due|\' (+ |amount due| 1)) (= |and|\' |x_r|))', { isPostcondition: true });
  const output = parser.toGuardString(ast);
  assert.deepEqual(parser.parse(output, { isPostcondition: true }).ast, ast);
  assert.deepEqual([...evaluator.getVariableReferences(ast).read].sort(), ['amount due', 'x_r']);
  assert.deepEqual([...evaluator.getVariableReferences(ast).written].sort(), ['amount due', 'and']);
  assert.throws(() => parser.parse('(= |broken 1)'), /quoted|Unterminated/i);
  assert.throws(() => parser.quoteGuardIdentifier('a|b'), /alias/);
  assert.throws(() => parser.quoteGuardIdentifier('a\\b'), /alias/);
  assert.throws(() => parser.parse('(= |a\\b| 1)'), /Backslash/);
});

/** Canonical output preserves small decimals, exponent values and Real sorts. */
test('numeric canonical output remains parseable at exponent boundaries', () => {
  for (const expression of ['(= x 0.0000001)', '(= x -1e+21)', '(= x 1.0)', '(= x (/ 1 10000000))']) {
    const ast = parser.parse(expression).ast;
    assert.deepEqual(parser.parse(parser.toGuardString(ast)).ast, ast);
  }
  assert.throws(() => parser.parse('(= x 1e999)'), /finite/i);
});

/** SMT comparison chains and implication must evaluate every relevant operand. */
test('n-ary comparisons and right-associated implication are exact', () => {
  assert.equal(evaluate('(< 1 3 2)'), false);
  assert.equal(evaluate('(<= 1 2 2 3)'), true);
  assert.equal(evaluate('(distinct 1 2 1)'), false);
  assert.equal(evaluate('(=> false true false)'), true);
  assert.throws(() => parser.parse('(not true false)'), /argument/);
});

/** Unselected Boolean branches and conditional branches must not be evaluated. */
test('logical and conditional operators short circuit', () => {
  assert.equal(evaluate('(or true (= (/ 1 0) 1))'), true);
  assert.equal(evaluate('(and false (= (/ 1 0) 1))'), false);
  assert.equal(evaluate('(= (ite true 4 (/ 1 0)) 4)'), true);
});

/** Keep all predicate clauses and distinguish old from new values. */
test('postcondition updates preserve duplicates, constraints, and simultaneous reads', () => {
  const { ast } = parser.parse('(and (= x\' (+ x 1)) (= y\' x) (= x\' 99))', { isPostcondition: true });
  const result = evaluator.evaluatePostcondition(ast, { x: 2, y: 0 });
  assert.deepEqual(Object.fromEntries(result.assignments), { x: 3, y: 2 });
  assert.equal(result.constraints.length, 1);
  assert.equal(evaluator.checkConstraint(ast, { x: 2, y: 0 }, Object.fromEntries(result.assignments)), false);
  const primed = parser.parse('(= x\' y\')', { isPostcondition: true }).ast;
  assert.equal(evaluator.getPostconditionUpdates(primed).assignments.size, 0);
  assert.throws(() => evaluator.checkConstraint(primed, { x: 1, y: 1 }, {}), /no value/);
});

/** Free variable collection must respect simultaneous let and quantifier bindings. */
test('variable collection excludes bound names', () => {
  const { ast } = parser.parse('(let ((local source)) (and (> local 0) (exists ((bound Real)) (> bound other))))');
  assert.deepEqual([...evaluator.getVariableReferences(ast).read].sort(), ['other', 'source']);
  assert.equal(evaluate('(let ((__proto__ 2)) (= __proto__ 2))'), true);
});

/** Invalid types must not silently become numbers or Boolean values. */
test('runtime rejects type-inapplicable numeric and Boolean operations', () => {
  assert.throws(() => evaluate('x < 2', { x: true }), /number|numeric/i);
  assert.throws(() => evaluate('(= (+ x 1) 2)', { x: '1' }), /number|numeric/i);
  assert.throws(() => evaluate('x and true', { x: 1 }), /Boolean/i);
  assert.throws(() => evaluate('x', { x: 1 }), /Boolean/i);
  assert.equal(evaluate('(= x 1)', { x: true }), false);
});

/** A postcondition is a predicate even when it does not update a variable. */
test('read-only postconditions and true are valid', () => {
  assert.equal(validatePostcondition('true', []).valid, true);
  assert.equal(validatePostcondition('x > 1', ['x']).valid, true);
});

/** Feature eligibility must remain narrower than the accepted editor grammar. */
test('compatibility profiles separate native execution and paper algorithms', async () => {
  const { assessGuardCompatibility } = await import('../src/extensions/guard-language/guard-compatibility.js');
  const net = { dataVariables: [{ name: 'x', type: 'real' }], transitions: [{ id: 't', precondition: 'x > 0', postcondition: "x' = x + 1" }] };
  const profile = assessGuardCompatibility(net);
  assert.equal(profile.simulation.supported, true);
  assert.equal(profile.probabilistic.supported, false);
  assert.equal(profile.soundness.supported, false);
  net.transitions[0].postcondition = "x' > x";
  const constraintProfile = assessGuardCompatibility(net);
  assert.equal(constraintProfile.simulation.supported, false);
  assert.equal(constraintProfile.soundness.supported, true);
  net.dataVariables[0].type = 'int';
  assert.equal(assessGuardCompatibility(net).soundness.supported, false);
});

/** Retained-only execution never evaluates inactive generalized metadata. */
test('retained-only discovery profiles ignore inactive generalized constraints', async () => {
  const { assessGuardCompatibility } = await import('../src/extensions/guard-language/guard-compatibility.js');
  const net = { dataVariables: [{ name: 'x', type: 'data' }], transitions: [{ id: 't', precondition: '(exists ((v Real)) (> v x))', postcondition: "x' > x", discoveryContract: { generalized: false, observedPairs: [{ before: {}, after: { x: 2 } }] } }] };
  const result = assessGuardCompatibility(net);
  assert.equal(result.simulation.supported, true);
  assert.equal(result.probabilistic.supported, false);
  assert.equal(result.soundness.supported, false);
});
