import assert from 'node:assert/strict';
import { PetriNet, Place, Transition, Arc } from '../src/petri-net-simulator.js';

function netWithPlaceAndTransition(tokens = 0, capacity = null) {
  const net = new PetriNet('n1');
  const place = new Place('p1', { x: 0, y: 0 }, 'p1', tokens, capacity);
  const transition = new Transition('t1', { x: 100, y: 0 }, 't1');
  net.addPlace(place);
  net.addTransition(transition);
  return { net, place, transition };
}

{
  const { net, place } = netWithPlaceAndTransition(1);
  net.addArc(new Arc('a1', 'p1', 't1', 1, 'regular'));
  net.addArc(new Arc('a2', 'p1', 't1', 1, 'regular'));

  assert.equal(net.isTransitionEnabled('t1'), false, 'parallel PT arcs require the sum of their weights');
  assert.equal(net.fireTransition('t1'), false);
  assert.equal(place.tokens, 1);

  place.tokens = 2;
  assert.equal(net.isTransitionEnabled('t1'), true);
  assert.equal(net.fireTransition('t1'), true);
  assert.equal(place.tokens, 0, 'parallel PT arcs consume the sum of their weights');
}

{
  const { net, place } = netWithPlaceAndTransition(2);
  net.addArc(new Arc('read', 't1', 'p1', 2, 'read'));

  assert.equal(net.isTransitionEnabled('t1'), true, 'read arcs are place-transition predicates in either direction');
  assert.equal(net.fireTransition('t1'), true);
  assert.equal(place.tokens, 2, 'read arcs do not consume tokens');

  place.tokens = 1;
  assert.equal(net.isTransitionEnabled('t1'), false);
}

{
  const { net, place } = netWithPlaceAndTransition(0);
  net.addArc(new Arc('inh', 't1', 'p1', 5, 'inhibitor'));

  assert.equal(net.isTransitionEnabled('t1'), true, 'default inhibitor arcs ignore weight and require zero tokens');
  place.tokens = 1;
  assert.equal(net.isTransitionEnabled('t1'), false);

  net.setArcSemantics({ inhibitorUsesWeight: true });
  assert.equal(net.isTransitionEnabled('t1'), true, 'weighted inhibitor mode can be enabled explicitly');
}

{
  const { net, place } = netWithPlaceAndTransition(4);
  net.addArc(new Arc('reset', 't1', 'p1', 9, 'reset'));

  assert.equal(net.fireTransition('t1'), true);
  assert.equal(place.tokens, 0, 'reset arcs reset the connected place in either direction');
}

{
  const { net, place } = netWithPlaceAndTransition(5);
  net.addArc(new Arc('reset', 'p1', 't1', 1, 'reset'));
  net.addArc(new Arc('produce', 't1', 'p1', 2, 'regular'));

  assert.equal(net.fireTransition('t1'), true);
  assert.equal(place.tokens, 2, 'firing order is consume, reset, then produce');
}

{
  const { net, place } = netWithPlaceAndTransition(1, 1);
  net.addArc(new Arc('produce', 't1', 'p1', 1, 'regular'));

  assert.equal(net.isTransitionEnabled('t1'), false, 'strict capacity disables transitions that would overflow outputs');
  assert.equal(net.fireTransition('t1'), false);
  assert.equal(place.tokens, 1);

  net.setArcSemantics({ capacityRule: 'clamp' });
  assert.equal(net.isTransitionEnabled('t1'), true);
  assert.equal(net.fireTransition('t1'), true);
  assert.equal(place.tokens, 1, 'clamp mode preserves the previous YAPNE capacity behavior');
}

console.log('Petri net arc semantics tests passed.');
