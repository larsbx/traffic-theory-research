import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { breakDown, halfStep, isStalled } from '../src/sim.js';
import { certificate } from '../src/analysis.js';
import { levelSpec, movePlayer, depot, newLevel, contact, tick, POINTS, ORDER, RULESETS } from '../src/game.js';

const presets = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const netOf = (id) => rasterize(presets.places.find((p) => p.id === id).roads, { ...WINDOW, drive: PLACES.find((q) => q.id === id).drive });

test('level ladder: every place once per loop, one traffic law repealed per loop', () => {
  ORDER.forEach((id, i) => assert.equal(levelSpec(i).place, id));
  assert.equal(levelSpec(0).rules.name, RULESETS[0].name);
  assert.equal(levelSpec(6).rules.name, RULESETS[1].name);
  assert.equal(levelSpec(99).rules.name, RULESETS.at(-1).name);
  assert.ok(levelSpec(1).rho > levelSpec(0).rho && levelSpec(99).rho <= 0.6);
});

test('the truck only drives on road and takes buffered turns', () => {
  const net = netOf('midtown');
  let p = { cell: depot(net), dir: 'left', want: 'up' };
  for (let i = 0; i < 300; i++) {
    p = movePlayer(net, { ...p, want: ['up', 'left', 'down', 'right'][i % 4] });
    assert.equal(net.road[p.cell], 1);
  }
});

test('towing: only incidents and certified-frozen cars, scored by kind', () => {
  const net = netOf('etoile');
  let { sim, game } = newLevel(net, { ...levelSpec(22), rho: 0.5 }, undefined, 3);
  for (let t = 0; t < 400; t++) sim = halfStep(net, sim, game.spec.rules);
  const { frozen } = certificate(net, sim, game.spec.rules);
  const free = frozen.findIndex((f, k) => !f && sim.pos[k] >= 0 && !isStalled(sim, k));
  const core = frozen.indexOf(2);
  assert.ok(free >= 0 && core >= 0);
  const at = (k) => ({ ...game, player: { ...game.player, cell: sim.pos[k] } });
  assert.equal(contact(net, sim, at(free)).events.length, 0);
  const towed = contact(net, sim, at(core));
  assert.equal(towed.game.score, game.score + POINTS.core);
  assert.equal(towed.sim.pos[core], -1);
  const stalled = breakDown(sim, free, 50);
  assert.equal(contact(net, stalled, at(free)).events[0].kind, 'incident');
});

test('a level runs to an end state; trips and score only grow', () => {
  const net = netOf('grachten');
  let { sim, game } = newLevel(net, { ...levelSpec(0), length: 300 }, undefined, 2);
  game = { ...game, player: { ...game.player, safeUntil: Infinity } };
  let last = game;
  while (game.status === 'play') {
    ({ sim, game } = tick(net, sim, game));
    assert.ok(game.score >= last.score && (game.trips ?? 0) >= (last.trips ?? 0));
    last = game;
  }
  assert.ok(['clear', 'short'].includes(game.status));
  assert.ok(game.quota > 0);
});

test('a truck parked on a busy lane gets run over: lives fall, then game over', () => {
  const net = netOf('grachten');
  let { sim, game } = newLevel(net, { ...levelSpec(0), length: 3000 }, undefined, 2);
  const lives = [];
  while (game.status === 'play') { ({ sim, game } = tick(net, sim, game)); lives.push(game.lives); }
  assert.equal(game.status, 'over');
  assert.deepEqual([...new Set(lives)], [3, 2, 1, 0]);
});
