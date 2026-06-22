import assert from 'node:assert/strict';

import { PythonToDPN } from '../src/extensions/python-dpn-transpiler.js';
import { parse } from '../src/extensions/guard-language/guard-parser.js';
import { evaluatePrecondition } from '../src/extensions/guard-language/guard-evaluator.js';

const { ast } = parse('(x % 2) == 1 && y ** 2 == 9', { isPostcondition: false });
assert.equal(evaluatePrecondition(ast, { x: 5, y: 3 }), true);
assert.equal(evaluatePrecondition(ast, { x: 4, y: 3 }), false);

const { ast: precedenceAst } = parse('-2 ** 2 == -4', { isPostcondition: false });
assert.equal(evaluatePrecondition(precedenceAst, {}), true);

const dpn = new PythonToDPN().convert(`
x = 10
r = x % 4
p = r ** 3
p %= 5
p **= 2
if p % 2 == 1:
    r = p
else:
    r = p ** 2
`);

function transitionByLabel(label) {
  return Array.from(dpn.transitions.values()).find(t => t.label === label);
}

assert.equal(transitionByLabel('r = x % 4').postcondition, "r' = x % 4");
assert.equal(transitionByLabel('p = r ** 3').postcondition, "p' = r ** 3");
assert.equal(transitionByLabel('p %= 5').postcondition, "p' = p % (5)");
assert.equal(transitionByLabel('p **= 2').postcondition, "p' = p ** (2)");

const thenTransition = transitionByLabel('r = p');
const elseTransition = transitionByLabel('r = p ** 2');

assert.equal(thenTransition.precondition, 'p % 2 == 1');
assert.equal(thenTransition.evaluatePrecondition({ p: 25 }), true);
assert.equal(thenTransition.evaluatePrecondition({ p: 24 }), false);

assert.equal(elseTransition.precondition, '!(p % 2 == 1)');
assert.equal(elseTransition.evaluatePrecondition({ p: 25 }), false);
assert.equal(elseTransition.evaluatePrecondition({ p: 24 }), true);

assert.deepEqual(await transitionByLabel('r = x % 4').evaluatePostcondition({ x: 10, r: 0, p: 0 }), {
  x: 10,
  r: 2,
  p: 0
});
assert.deepEqual(await transitionByLabel('p **= 2').evaluatePostcondition({ x: 10, r: 2, p: 3 }), {
  x: 10,
  r: 2,
  p: 9
});

console.log('Python importer modulo and exponent tests passed.');

const rngCode = `
def rng_next(seed: int) -> int:
    """
    Creates the next pseudo-random number state.
    """
    multiplier: int = 1103515245
    increment: int = 12345
    modulus: int = 2147483648

    seed = (multiplier * seed + increment) % modulus

    return seed


def rng_int(seed: int, minimum: int, maximum: int) -> tuple[int, int]:
    """
    Creates a pseudo-random integer in a given range.
    """
    seed = rng_next(seed)

    size: int = maximum - minimum + 1
    value: int = minimum + seed % size

    return value, seed


number, seed = rng_int(seed, 1, 10)
`;

const rngDpn = new PythonToDPN().convert(rngCode);

async function fireLinearNet(net, maxSteps = 50) {
  for (let i = 0; i < maxSteps; i++) {
    const enabled = Array.from(net.transitions.keys()).find(id => net.isTransitionEnabled(id));
    if (!enabled) return;
    await net.fireTransition(enabled);
  }
  throw new Error(`Expected PRNG DPN to finish within ${maxSteps} steps`);
}

await fireLinearNet(rngDpn);

assert.equal(rngDpn.getDataValuation().seed, 12345);
assert.equal(rngDpn.getDataValuation().number, 6);

console.log('Python importer PRNG example test passed.');
