import { test } from 'node:test';
import assert from 'node:assert/strict';
import { network, torus } from '../src/raster.js';
import { breakDown, DEFAULTS, EXIT, fromGrid, halfStep, init, TRAIN, turnOptions } from '../src/sim.js';
import { greatestTrap, safeCells, safeCellTurnTable, trapInput, trapSet, verifySafeCellCertificate } from '../src/realflow.js';

const reroute = { reroute: true };
const opts = { ...DEFAULTS, ...reroute };
const fork = (exit) => network({
  W: 3, H: 1, road: Uint8Array.of(1, 1, 1), exit, entries: [0],
  edges: [[0, 1, 0, 0], [2, 1, 0, Math.PI], [1, 2, 0, 0], [1, 0, 0, Math.PI]],
});

test('an empty menu stays trapped while an option with no blockers escapes', () => {
  assert.deepEqual([...greatestTrap({ cars: [0, 1], menus: [[], [[]]] })], [1, 0]);
  assert.deepEqual([...greatestTrap({
    cars: [0, 1, 2], menus: [[[1], [2]], [[0], [2]], [[0], [1]]],
  })], [1, 1, 1]);
});

test('an empty legal turn list is uncertified, and the simulator fallback is an explicit exit', () => {
  const net = network({ W: 3, H: 1, road: Uint8Array.of(1, 1, 1), edges: [[0, 1, 0, 0]], entries: [0] });
  assert.deepEqual(safeCellTurnTable(net, opts), [
    [{ prev: -1, cells: [1] }], [{ prev: 0, cells: [] }], [{ prev: -1, cells: [] }],
  ]);
  assert.deepEqual(safeCells(net, opts).ranks, [null, null, null]);
  const s = halfStep(net, init(net, 1, 1, opts), opts);
  assert.equal(s.pos[0], 1);
  assert.equal(s.next[0], EXIT);
  assert.deepEqual(trapInput(net, s, opts, reroute).menus, [[[]]]);
  assert.deepEqual([...trapSet(net, s, opts, reroute)], [0]);
});

test('all arrivals need a descent witness and the residual set must be closed', () => {
  const net = fork(Uint8Array.of(0, 0, 1));
  assert.deepEqual(safeCellTurnTable(net, opts)[1], [{ prev: 0, cells: [2] }, { prev: 2, cells: [0] }]);
  const { ranks } = safeCells(net, opts);
  assert.deepEqual(ranks, [null, null, 0]);
  assert.ok(verifySafeCellCertificate(net, opts, ranks));
  assert.equal(verifySafeCellCertificate(net, opts, [2, 1, 0]), false);
  assert.equal(verifySafeCellCertificate(net, opts, [null, null, null]), false);
});

test('a prior-heading plan outside the re-routing menu can still take its vacant committed hop', () => {
  const net = fork();
  const s = fromGrid(net, [[0, 1, 1]]);
  s.species[0] = 0;
  s.prev[0] = 0;
  s.next[0] = 0;
  s.next[1] = 1;
  assert.deepEqual(turnOptions(net, 1, 0, opts).cells, [2]);
  assert.deepEqual(turnOptions(net, 1, 0, opts, Math.PI).cells, [2, 0]);
  assert.deepEqual(trapInput(net, s, opts, reroute).menus, [[[], [1]], [[0]]]);
  assert.deepEqual([...trapSet(net, s, opts, reroute)], [0, 0]);
  assert.equal(halfStep(net, s, opts).pos[0], 0);
});

test('fixed-species cars can trap on ranked cells, and TRAIN can rotate the CLASSIC trap', () => {
  const net = torus(2, 1);
  net.exit.fill(1);
  const s = fromGrid(net, [[1, 1]]);
  assert.equal(safeCells(net, opts).count, 2);
  assert.deepEqual([...trapSet(net, s, opts, reroute)], [1, 1]);
  assert.equal(halfStep(net, s, opts).moved, 0);
  const train = { ...opts, rule: TRAIN };
  assert.equal(halfStep(net, s, train).moved, 2);
  assert.throws(() => verifySafeCellCertificate(net, train, [0, 0]), /CLASSIC/);
});

test('a temporary breakdown can stop an untrapped vehicle through several half-steps', () => {
  const net = network({
    W: 2, H: 1, road: Uint8Array.of(1, 1), edges: [[0, 1, 0, 0]],
    exit: Uint8Array.of(0, 1), entries: [0],
  });
  let s = breakDown(init(net, 1, 2, opts), 0, 4);
  assert.deepEqual(safeCells(net, opts).ranks, [1, 0]);
  assert.deepEqual([...trapSet(net, s, opts, reroute)], [0]);
  for (let t = 0; t < 4; t++) {
    s = halfStep(net, s, opts);
    assert.equal(s.moved, 0);
  }
  assert.equal(halfStep(net, s, opts).moved, 1);
});

test('an exit and immediate re-entry count as movement even at the same cell', () => {
  const net = torus(1, 1);
  net.exit[0] = 1;
  const s = init(net, 1, 2, opts);
  s.next[0] = EXIT;
  assert.deepEqual([...trapSet(net, s, opts, reroute)], [0]);
  const after = halfStep(net, s, opts);
  assert.deepEqual(after.pos, s.pos);
  assert.equal(after.exited, 1);
  assert.equal(after.last[0], s.t);
});
