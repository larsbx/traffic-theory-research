import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { network, rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { safeCells, safeCellTurnTable, trapSet, verifySafeCellCertificate } from '../src/realflow.js';
import { breakDown, DEFAULTS, EXIT, fromGrid, halfStep, init, LAWS } from '../src/sim.js';

const routing = { reroute: true };
const classic = { ...DEFAULTS, ...routing };
const [leanVerifier] = process.argv.slice(2);
let leanComparisons = 0;

function waitBounds(cap, maxRank) {
  const k = BigInt(cap);
  const bounds = [k];
  for (let rank = 1; rank <= maxRank; rank++) bounds.push(k * (bounds[rank - 1] + 1n));
  if (leanVerifier) {
    const result = spawnSync(leanVerifier, ['--wait-bounds', String(cap), String(maxRank)], { encoding: 'utf8' });
    if (result.error) throw result.error;
    assert.equal(result.status, 0, result.stderr);
    assert.deepEqual(JSON.parse(result.stdout), bounds.map(String));
    leanComparisons += bounds.length;
  }
  return bounds;
}

// Count missed clear checkpoints per legal destination during each waiting
// episode. A departure is an event even if respawn makes the position equal.
function observe(net, opts, initial, horizon, assertSnapshot = () => {}) {
  const table = safeCellTurnTable(net, opts);
  const missed = Array.from(initial.pos, () => new Map());
  const frames = [];
  let maxMissed = 0;
  let refills = 0;
  let start = initial;
  for (let i = 0; i < horizon; i++) {
    assertSnapshot(start);
    const end = halfStep(net, start, opts);
    frames.push([start.pos, Int8Array.from(end.last, (last) => Number(last === start.t))]);
    for (const [car, cell] of start.pos.entries()) {
      if (cell < 0) continue;
      assert.equal(start.species[car], 0);
      assert.equal(start.aheadLen[car], 0);
      const arrival = table[cell].find(({ prev }) => prev === start.prev[car]);
      assert.ok(arrival, `missing arrival for car ${car} at cell ${cell}`);
      if (end.last[car] === start.t) {
        if (end.occ[cell] >= 0) refills++;
        missed[car].clear();
      } else {
        assert.equal(end.pos[car], cell);
        assert.equal(end.prev[car], start.prev[car]);
        for (const dest of new Set(arrival.cells)) {
          if (dest !== EXIT && start.occ[dest] >= 0) continue;
          const count = (missed[car].get(dest) ?? 0) + 1;
          missed[car].set(dest, count);
          maxMissed = Math.max(maxMissed, count);
        }
      }
    }
    start = end;
  }
  return { frames, cap: maxMissed + 1, refills, end: start };
}

function verifyWindows(ranks, { frames, cap, refills }) {
  assert.equal(refills, 0, 'a departure did not leave a vacant checkpoint');
  const bounds = waitBounds(cap, Math.max(...ranks));
  const next = new Int32Array(frames[0][0].length).fill(frames.length);
  let checked = 0;
  let higherRank = 0;
  for (let i = frames.length - 1; i >= 0; i--) {
    const [positions, moved] = frames[i];
    for (const [k, cell] of positions.entries()) {
      if (moved[k]) next[k] = i;
      if (cell < 0 || ranks[cell] === null) continue;
      const bound = bounds[ranks[cell]];
      if (bound > BigInt(frames.length - i)) continue;
      assert.ok(BigInt(next[k] - i) < bound, `car ${k} exceeded rank ${ranks[cell]} budget`);
      checked++;
      if (ranks[cell] > 0) higherRank++;
    }
  }
  return { checkedWindows: checked, higherRankWindows: higherRank };
}

function corridor(cells, refill) {
  const edges = Array.from({ length: cells - 1 }, (_, c) => [c, c + 1, 0, 0]);
  if (refill) edges.push([cells - 1, cells - 1, 0, 0]);
  const exit = new Uint8Array(cells);
  exit[cells - 1] = 1;
  return network({
    W: cells, H: 1, road: new Uint8Array(cells).fill(1), edges, exit,
    entries: refill ? [cells - 1] : [0],
  });
}

function lineState(net) {
  const state = fromGrid(net, [Array(net.W).fill(1)]);
  state.species.fill(0);
  for (let c = 0; c < net.W; c++) {
    state.prev[c] = c - 1;
    state.next[c] = c + 1 === net.W ? EXIT : c + 1;
  }
  return state;
}

const exitRoad = corridor(1, true);
const exitRanks = safeCells(exitRoad, classic).ranks;
assert.deepEqual(exitRanks, [0]);
const stalls = [0, 1, 8, 64, 512].map((duration) => {
  const opts = { ...classic, respawnDelay: 2 };
  const initial = breakDown(lineState(exitRoad), 0, duration);
  const observed = observe(exitRoad, opts, initial, duration + 2, (state) =>
    assert.ok(trapSet(exitRoad, state, opts, routing).every((member) => !member)));
  const firstMove = observed.frames.findIndex(([, moved]) => moved[0]);
  assert.equal(firstMove, duration + (duration % 2));
  assert.equal(observed.refills, 0);
  return { duration, firstMove, cap: observed.cap };
});

const line = corridor(5, false);
const drain = { ...classic, respawnDelay: 128 };
const drained = observe(line, drain, lineState(line), 96);
assert.equal(drained.cap, 2);
assert.equal(drained.end.exited, 5);
const lineRanks = safeCells(line, drain).ranks;
assert.deepEqual(lineRanks, [4, 3, 2, 1, 0]);
const drainWindows = verifyWindows(lineRanks, drained);
assert.ok(drainWindows.higherRankWindows > 5);

const refill = corridor(2, true);
const refillRanks = safeCells(refill, classic).ranks;
assert.deepEqual(refillRanks, [1, 0]);
const refilled = observe(refill, classic, lineState(refill), 64, (state) => {
  assert.deepEqual([...state.pos], [0, 1]);
  assert.ok(trapSet(refill, state, classic, routing).every((member) => !member));
});
assert.equal(refilled.cap, 2);
assert.equal(refilled.refills, 32);
assert.ok(refilled.frames.every(([, moved], i) => !moved[0] && moved[1] === Number(i % 2 === 0)));
assert.ok(BigInt(refilled.frames.length) > waitBounds(refilled.cap, 1)[1]);
assert.throws(() => verifyWindows(refillRanks, refilled), /vacant checkpoint/);

// With the same periodic exits and a one-step delay, the vacancy appears
// only in the wrong phase for the follower's horizontal hop.
const phased = { ...classic, respawnDelay: 1 };
const wrongPhase = observe(refill, phased, lineState(refill), 64, (state) => {
  assert.equal(state.pos[0], 0);
  assert.equal(state.occ[1], state.t % 2 === 0 ? 1 : -1);
  assert.ok(trapSet(refill, state, phased, routing).every((member) => !member));
});
assert.equal(wrongPhase.refills, 0);
assert.equal(wrongPhase.cap, 33);
assert.ok(wrongPhase.frames.every(([, moved], i) => !moved[0] && moved[1] === Number(i % 2 === 0)));

const data = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const maps = [];
const horizon = 192;
for (const { id, roads } of data.places) {
  const net = rasterize(roads, { ...WINDOW, drive: PLACES.find((place) => place.id === id).drive });
  for (const law of LAWS.filter((law) => !law.box)) {
    const opts = { ...classic, ...law, respawnDelay: horizon + 1, slow: 0.1 };
    const { ranks, count, roadCells } = safeCells(net, opts);
    assert.equal(count, roadCells);
    assert.ok(verifySafeCellCertificate(net, opts, ranks));
    const initial = init(net, Math.ceil(roadCells / 4), 17, opts);
    const observed = observe(net, opts, initial, horizon);
    const checks = verifyWindows(ranks, observed);
    maps.push({ id, law: law.name, horizon, observedServiceCap: observed.cap, ...checks });
  }
}
assert.equal(maps.length, 12);
assert.ok(maps.every(({ checkedWindows }) => checkedWindows > 0));
assert.ok(maps.some(({ higherRankWindows }) => higherRankWindows > 0));
console.log(JSON.stringify({
  stalls, drainWindows,
  immediateRefill: { cap: refilled.cap, refills: refilled.refills, stationaryHalfSteps: refilled.frames.length },
  phaseMismatch: { missedVacancies: wrongPhase.cap - 1, stationaryHalfSteps: wrongPhase.frames.length },
  maps, leanComparisons,
}));
