import { test } from 'node:test';
import assert from 'node:assert/strict';
import { blockerOf, certificate } from '../src/analysis.js';
import { network, torus } from '../src/raster.js';
import { makeRng } from '../src/rng.js';
import { aheadOf, boxClear, breakDown, CLASSIC, DEFAULTS, EXIT, fromGrid, halfStep, plan, TRAIN } from '../src/sim.js';

// Seed the roaming entrant's committed tail directly, so each test fixes the
// routing choice and exercises the production blocker, gate and half-step.
const withBoxTail = (net, grid, tail) => {
  const s = fromGrid(net, grid);
  s.species[0] = 0;
  s.ahead.set(tail);
  s.aheadLen[0] = tail.length;
  return s;
};

const withJunction = (width, ...cells) => {
  const net = torus(width, 2);
  net.junction.fill(0);
  for (const cell of cells) net.junction[cell] = 1;
  return net;
};

test('a same-axis cycle with one indirect box blocker captures its upstream car under both rules', () => {
  const net = withJunction(3, 1);
  const initial = withBoxTail(net, [[1, 0, 1], [0, 0, 2]], [2]);
  assert.deepEqual(blockerOf(net, initial, 0, true), [1, false]);
  assert.deepEqual(blockerOf(net, initial, 1, true), [0, true]);
  assert.deepEqual(blockerOf(net, initial, 2, true), [1, true]);
  assert.equal(initial.axis[0], initial.axis[1]);

  for (const rule of [CLASSIC, TRAIN]) {
    const opts = { rule, box: true };
    const { cores, frozen } = certificate(net, initial, opts);
    assert.deepEqual(cores, [[0, 1]]);
    assert.deepEqual([...frozen], [2, 2, 1]);
    let s = initial;
    for (let t = 0; t < 8; t++) {
      s = halfStep(net, s, opts);
      assert.equal(s.moved, 0);
      assert.deepEqual(s.pos, initial.pos);
      assert.deepEqual(s.next, initial.next);
      assert.deepEqual(aheadOf(s, 0), [2]);
    }
    assert.equal(certificate(net, initial, { rule, box: false }).count, 0);
    assert.equal(halfStep(net, initial, { rule, box: false }).pos[0], 1);
  }
});

test('TRAIN cannot enter a box in the same half-step that its indirect blocker leaves', () => {
  // Open street 0→1→2→3 with a second approach 5→1, making cell 1 a junction.
  const net = network({
    W: 4, H: 2, road: Uint8Array.of(1, 1, 1, 1, 0, 1, 0, 0),
    edges: [[0, 1, 0, 0], [1, 2, 0, 0], [2, 3, 0, 0], [5, 1, 0, -Math.PI / 2]],
    exit: Uint8Array.of(0, 0, 0, 1, 0, 0, 0, 0), entries: [0, 5],
  });
  const opts = { ...DEFAULTS, rule: TRAIN, box: true };
  const route = plan(net, 0, -1, 0, makeRng(1), opts);
  assert.deepEqual(route, [1, 2]);
  const initial = withBoxTail(net, [[1, 0, 1, 0], [0, 0, 0, 0]], route.slice(1));
  initial.species[1] = 0;
  assert.deepEqual(blockerOf(net, initial, 0, true), [1, false]);
  assert.equal(boxClear(net, initial, 0), false);
  const after = halfStep(net, initial, opts);
  assert.deepEqual([...after.pos], [0, 3]);
  assert.deepEqual([...after.last], [-1, 0]);
  assert.equal(boxClear(net, after, 0), true);
  assert.equal(halfStep(net, halfStep(net, after, opts), opts).pos[0], 1);
});

test('box blocker selection prefers the occupied target, then the first occupied tail cell', () => {
  const net = withJunction(5, 1, 2);
  const target = withBoxTail(net, [[1, 1, 1, 1, 0], [0, 0, 0, 0, 0]], [2, 3]);
  assert.deepEqual(blockerOf(net, target, 0, true), [1, true]);

  const tail = withBoxTail(net, [[1, 0, 1, 1, 0], [0, 0, 0, 0, 0]], [2, 3]);
  assert.deepEqual(blockerOf(net, tail, 0, true), [1, false]);
  const laterTail = withBoxTail(net, [[1, 0, 0, 1, 0], [0, 0, 0, 0, 0]], [2, 3]);
  assert.deepEqual(blockerOf(net, laterTail, 0, true), [1, false]);
  assert.equal(boxClear(net, laterTail, 0), false);
  net.junction[0] = 1; // Car 0 is now already in the junction for this control.
  assert.equal(boxClear(net, tail, 0), true);
  assert.deepEqual(blockerOf(net, tail, 0, true), [-1, false]);
  assert.equal(halfStep(net, tail, { rule: CLASSIC, box: true }).pos[0], 1);
});

test('EXIT at the end of a committed box tail is not an occupied cell', () => {
  const net = withJunction(3, 1);
  net.exit[1] = 1;
  const initial = withBoxTail(net, [[1, 0, 0], [0, 0, 0]], [EXIT]);
  assert.equal(boxClear(net, initial, 0), true);
  assert.deepEqual(blockerOf(net, initial, 0, true), [-1, false]);
  assert.equal(halfStep(net, initial, { rule: TRAIN, box: true }).pos[0], 1);
});

test('a direct mixed-axis cycle is immobile under TRAIN', () => {
  const net = torus(2, 2);
  const initial = fromGrid(net, [[1, 2], [2, 1]]);
  const opts = { rule: TRAIN };
  assert.equal(certificate(net, initial, opts).count, 4);
  let s = initial;
  for (let t = 0; t < 4; t++) {
    s = halfStep(net, s, opts);
    assert.equal(s.moved, 0);
    assert.deepEqual(s.pos, initial.pos);
  }
});

test('TRAIN can rotate a full same-axis ring, and a stalled contender can suppress it', () => {
  const net = torus(3, 2);
  const initial = fromGrid(net, [[1, 1, 1], [0, 0, 0]]);
  const opts = { rule: TRAIN };
  assert.equal(certificate(net, initial, opts).count, 0);
  assert.deepEqual([...halfStep(net, initial, opts).pos], [1, 2, 0]);
  const stalled = breakDown(initial, 1, 1);
  assert.equal(certificate(net, stalled, opts).count, 0);
  assert.equal(halfStep(net, stalled, opts).moved, 0);
});

test('a singleton TRAIN self-loop records movement without a change of position', () => {
  const net = torus(1, 2);
  const initial = fromGrid(net, [[1], [0]]);
  assert.equal(halfStep(net, initial, { rule: CLASSIC }).moved, 0);
  const after = halfStep(net, initial, { rule: TRAIN });
  assert.deepEqual(after.pos, initial.pos);
  assert.equal(after.last[0], initial.t);
  assert.equal(after.moved, 1);
});
