import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { network, rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { safeCells, trapSet } from '../src/realflow.js';
import { DEFAULTS, EXIT, fromGrid, greenAxis, halfStep, init, LAWS, previewMoves, tow } from '../src/sim.js';

const routing = { reroute: true };
const classic = { ...DEFAULTS, ...routing };
const clocks = [];
const merges = [];
const deadlines = [];
const rankDeadlines = [];

// One clear target approached from each axis. Inspect the actual resolver
// at every start phase, with and without the junction signal gate.
const signalNet = network({
  W: 2, H: 2, road: Uint8Array.of(1, 1, 0, 1), exit: Uint8Array.of(0, 1, 0, 0),
  edges: [[0, 1, 0, 0], [3, 1, 0, -Math.PI / 2]],
});
const inbound = [fromGrid(signalNet, [[1, 0], [0, 0]]), fromGrid(signalNet, [[0, 0], [0, 2]])];
let clockWindows = 0;
for (let green = 1; green <= 24; green++) {
  for (const junction of [false, true]) for (const [axis, car] of inbound.entries()) {
    signalNet.junction[1] = Number(junction);
    car.species[0] = 0;
    car.next[0] = 1;
    const opts = { ...classic, green };
    const allowed = Array.from({ length: 4 * green }, (_, t) => {
      const { want } = previewMoves(signalNet, { ...car, t }, opts);
      const expected = want[0] === 1;
      assert.equal(expected, t % 2 === axis && (!junction || greenAxis(t, green) === axis));
      clocks.push({ green, t, axis, junction, expected });
      return expected;
    });
    for (let start = 0; start < 2 * green; start++) {
      assert.ok(allowed.slice(start, start + 2 * green).some(Boolean));
      clockWindows++;
    }
  }
}

const projectedAge = (s, k) => s.pos[k] >= 0 ? s.wait[k] : 0;

function inspect(net, before, opts, keepExample = false) {
  const { want, go } = previewMoves(net, before, opts);
  const after = halfStep(net, before, opts);
  const available = Array.from(want, (q) => q === EXIT || (q >= 0 && before.occ[q] < 0) ? q : -3);
  const grants = new Map();
  for (const [k, q] of available.entries()) {
    assert.equal(Boolean(go[k]), after.last[k] === before.t);
    if (!go[k]) continue;
    assert.ok(q >= 0 || q === EXIT);
    if (q === EXIT) continue;
    assert.ok(!grants.has(q));
    grants.set(q, k);
    assert.equal(after.pos[k], q);
    assert.equal(after.wait[k], 0);
  }
  assert.equal(after.moved, go.reduce((sum, yes) => sum + yes, 0));

  let losses = 0;
  let revisions = 0;
  for (const [k, q] of available.entries()) {
    const age = projectedAge(before, k);
    const nextAge = projectedAge(after, k);
    assert.ok(age >= 0 && nextAge >= 0 && nextAge <= age + 1);
    if (want[k] !== -3 && want[k] !== before.next[k]) revisions++;
    if (go[k]) continue;
    assert.ok(nextAge >= age);
    if (q === -3) continue;
    assert.ok(q >= 0, 'a ready exit must be granted');
    const winner = grants.get(q);
    assert.ok(winner !== undefined && winner !== k);
    const priority = projectedAge(before, winner);
    assert.ok(priority > age || (priority === age && winner < k));
    assert.equal(nextAge, age + 1);
    losses++;
  }
  if (keepExample || losses)
    merges.push({ age: Array.from(before.pos, (_, k) => projectedAge(before, k)), available, expected: Array.from(go, Boolean) });
  return { after, available, go, losses, revisions };
}

for (let cars = 1; cars <= 16; cars++) for (let gap = 1; gap <= 16; gap++)
  deadlines.push({ cars, gap, expected: cars * gap * (gap + 1) });

for (let cars = 1; cars <= 8; cars++) for (let delay = 1; delay <= 8; delay++) {
  let bound = BigInt(cars * delay * (delay + 1));
  for (let rank = 0; rank <= 4; rank++) {
    rankDeadlines.push({ cars, delay, rank, expected: bound.toString() });
    const gap = bound + BigInt(delay);
    bound = BigInt(cars) * gap * (gap + 1n);
  }
}

// A tie at a shared vacancy resets the winning age. Its rival is granted
// the next genuine attempt after the target has drained.
const mergeNet = network({
  W: 3, H: 1, road: Uint8Array.of(1, 1, 1), exit: Uint8Array.of(0, 1, 0),
  edges: [[0, 1, 0, 0], [2, 1, 0, Math.PI]],
});
const waiting = fromGrid(mergeNet, [[1, 0, 1]]);
waiting.species.fill(0);
waiting.wait.fill(8);
waiting.next.fill(1);
const drain = { ...classic, respawnDelay: 512 };
const mergeTrace = [];
let waitingState = waiting;
for (let t = 0; t < 5; t++) {
  const step = inspect(mergeNet, waitingState, drain, true);
  mergeTrace.push(step);
  waitingState = step.after;
}
assert.deepEqual([...mergeTrace[0].go], [1, 0]);
assert.deepEqual(mergeTrace.flatMap(({ available }, t) => available[1] >= 0 ? [t] : []), [0, 4]);
assert.equal(mergeTrace[4].go[1], 1);
const younger = fromGrid(mergeNet, [[1, 0, 1]]);
younger.species.fill(0);
younger.next.fill(1);
younger.wait.set([7, 8]);
assert.deepEqual([...inspect(mergeNet, younger, drain, true).go], [0, 1]);

// The first revision selects a free vertical hop while its signal is red.
// It retains that route until the first usable phase.
const heldNet = network({
  W: 2, H: 2, road: Uint8Array.of(1, 1, 0, 1), exit: Uint8Array.of(0, 1, 0, 0),
  edges: [[0, 1, 0, 0], [3, 1, 0, -Math.PI / 2], [3, 3, 0, 0]],
});
let held = fromGrid(heldNet, [[0, 0], [0, 1]]);
held.species[0] = 0;
held.next[0] = 3;
assert.deepEqual([...trapSet(heldNet, held, classic, routing)], [0]);
const heldMoves = [];
for (let t = 0; t < 8; t++) {
  const step = inspect(heldNet, held, { ...drain, green: 6 }, true);
  if (step.go[0]) heldMoves.push(t);
  else assert.equal(step.after.next[0], 1);
  held = step.after;
}
assert.deepEqual(heldMoves, [7]);
assert.equal(held.pos[0], 1);

// A returning tag can use the vacancy before the first mover is served.
// This run uses a full no-event cycle, then moves in the extra cycle.
const returningNet = network({
  W: 2, H: 2, road: Uint8Array.of(1, 1, 1, 1), exit: Uint8Array.of(1, 0, 0, 0), entries: [1],
  edges: [[3, 1, 0, -Math.PI / 2], [0, 1, 0, 0], [1, 0, 0, Math.PI], [2, 0, 0, -Math.PI / 2]],
});
const returningOpts = { ...classic, green: 6 };
let returning = fromGrid(returningNet, [[1, 0], [0, 2]]);
returning.t = 12;
returning.species.fill(0);
returning.next[1] = 1;
returning = tow(returning, 0, 6);
assert.equal(safeCells(returningNet, returningOpts).count, 4);
const pending = returning.pos.filter((cell) => cell < 0).length;
const cycle = 2 * returningOpts.green;
const admitted = [];
const budget = (pending + 1) * cycle;
let firstHop = null;
for (let t = 0; t < budget; t++) {
  const step = inspect(returningNet, returning, returningOpts, t % 6 === 0);
  if (step.after.moved) {
    firstHop = t;
    break;
  }
  assert.ok(trapSet(returningNet, returning, returningOpts, routing).every((member) => !member));
  if (returning.pos[0] < 0 && step.after.pos[0] >= 0) admitted.push(t);
  returning = step.after;
}
assert.deepEqual(admitted, [6]);
assert.equal(firstHop, cycle);

// The lower cell really becomes empty, but its vacancies occur on the
// opposite movement phase. The follower has zero arbitration attempts.
const delayed = network({
  W: 2, H: 1, road: Uint8Array.of(1, 1), exit: Uint8Array.of(0, 1), entries: [1],
  edges: [[0, 1, 0, 0], [1, 1, 0, 0]],
});
let phased = fromGrid(delayed, [[1, 1]]);
phased.species.fill(0);
phased.next.set([1, EXIT]);
phased.prev.set([-1, 0]);
let wrongPhaseVacancies = 0;
for (let t = 0; t < 64; t++) {
  if (phased.occ[1] < 0) wrongPhaseVacancies++;
  const step = inspect(delayed, phased, { ...classic, respawnDelay: 1 }, t < 4);
  assert.equal(step.available[0], -3);
  assert.equal(step.go[0], 0);
  phased = step.after;
}
assert.equal(wrongPhaseVacancies, 32);

const data = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const horizon = 128;
const maps = [];
for (const { id, roads } of data.places) {
  const net = rasterize(roads, { ...WINDOW, drive: PLACES.find((p) => p.id === id).drive });
  for (const law of LAWS.filter((law) => !law.box)) {
    const opts = { ...classic, ...law, respawnDelay: horizon + 1 };
    const { count, roadCells } = safeCells(net, opts);
    assert.equal(count, roadCells);
    let state = init(net, Math.ceil(roadCells * 0.4), 17, opts);
    const active = [];
    let losses = 0;
    let revisions = 0;
    let quiet = 0;
    for (let t = 0; t < horizon; t++) {
      const onStreet = state.pos.some((p) => p >= 0);
      const step = inspect(net, state, opts, t % 16 === 0);
      if (onStreet && !step.after.moved) {
        if (quiet === 0) assert.ok(trapSet(net, state, opts, routing).every((member) => !member));
        assert.deepEqual(step.after.occ, state.occ);
        quiet++;
      } else {
        quiet = 0;
      }
      active.push({ onStreet, moved: step.after.moved });
      losses += step.losses;
      revisions += step.revisions;
      state = step.after;
    }
    let activityWindows = 0;
    let next = horizon;
    for (let t = horizon - 1; t >= 0; t--) {
      if (active[t].moved) next = t;
      if (active[t].onStreet && t + 2 * opts.green <= horizon) {
        assert.ok(next < t + 2 * opts.green, `${id} ${law.name}: no movement in the signal cycle`);
        activityWindows++;
      }
    }
    maps.push({ id, law: law.name, activityWindows, losses, revisions });
  }
}
assert.equal(maps.length, 12);
assert.ok(maps.every((m) => m.activityWindows > 0));
assert.ok(maps.some((m) => m.losses > 0 && m.revisions > 0));

const [leanVerifier, artifactDirectory] = process.argv.slice(2);
let lean = null;
if (leanVerifier) {
  const path = join(artifactDirectory, 'r2-service-cases.json');
  writeFileSync(path, JSON.stringify({ clocks, merges, deadlines, rankDeadlines }) + '\n');
  const result = spawnSync(leanVerifier, ['--service', path], { encoding: 'utf8', timeout: 120000 });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, result.stderr);
  lean = result.stdout.trim();
}
console.log(JSON.stringify({
  clockCases: clocks.length, clockWindows, mergeCases: merges.length, deadlines: deadlines.length,
  rankDeadlines: rankDeadlines.length,
  mergeAttempts: [0, 4], heldMove: heldMoves[0], wrongPhaseVacancies, maps, lean,
  admissionDelay: { pending, admitted, cycle, firstHop, budget },
}));
