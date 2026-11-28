import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { network, rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { CLASSIC, DEFAULTS, EXIT, fromGrid, halfStep, init, LAWS, previewMoves, TRAIN, tow, turnOptions } from '../src/sim.js';

// The mathematical wire uses exactly -1 for outside/EXIT. The production
// simulator's request sentinels -2 and -3 never cross that wire unchanged.
const wireTarget = (q) => q === EXIT ? -1 : q;
const cases = [];
const invalidWire = [];
const histories = [];
const kinds = new Set();
let productionEvents = 0;

function productionCase(net, before, opts, id, expectedValid = true) {
  assert.ok(before.species.every((v) => v === 0), 'these controls use roaming lane-graph tags');
  const { want, go } = previewMoves(net, before, opts);
  const after = halfStep(net, before, opts);
  const events = Array.from(before.pos, (source, k) => {
    const target = after.pos[k];
    assert.equal(Boolean(go[k]), after.last[k] === before.t, 'preview grant must match the real halfStep event');
    if (go[k]) {
      assert.ok(source >= 0);
      if (want[k] === EXIT)
        return { kind: target < 0 ? 'exit' : 'exit_admit', source, target };
      assert.equal(target, want[k]);
      return { kind: 'hop', source, target };
    }
    if (source < 0 && target >= 0) return { kind: 'admit', source: -1, target };
    assert.equal(target, source);
    return { kind: 'stay', source, target };
  });
  const routes = [];
  for (let k = 0; k < before.pos.length; k++) {
    const cell = before.pos[k];
    if (cell < 0) continue;
    // Match realflow's snapshot menu: the existing commitment remains
    // legal even when older heading context omits it from re-routing.
    // This is a per-batch snapshot table, not a claim of a fixed route
    // function throughout every production execution.
    const targets = [...new Set([before.next[k], ...turnOptions(net, cell, before.prev[k], opts).cells])].map(wireTarget);
    routes.push({ prev: before.prev[k], cell, targets });
  }
  const entries = Array.from(net.road, (road, q) => Boolean(road && net.outStart[q + 1] > net.outStart[q] &&
    (!net.entries.length || net.entries.includes(q))));
  const expectedMoved = events.map((e) => ['hop', 'exit', 'exit_admit'].includes(e.kind));
  const expectedAdmitted = events.map((e) => ['admit', 'exit_admit'].includes(e.kind));
  assert.equal(expectedMoved.filter(Boolean).length, after.moved);
  assert.equal(events.filter((e) => ['exit', 'exit_admit'].includes(e.kind)).length, after.exited - before.exited);
  const arrivals = events.filter((e) => ['hop', 'admit', 'exit_admit'].includes(e.kind));
  const fenced = arrivals.every((e) => before.occ[e.target] < 0);
  assert.equal(fenced, expectedValid, `${id}: expected fence result`);
  const result = {
    id,
    provenance: `simulation; previewMoves want/go + halfStep events; t=${before.t}; rule=${opts.rule}; source=app/src/sim.js`,
    cells: net.W * net.H,
    cars: before.pos.length,
    pos: [...before.pos],
    prev: Array.from(before.pos, (p, k) => p < 0 ? -1 : before.prev[k]),
    routes, entries, events, expectedValid,
    expectedPos: [...after.pos],
    expectedPrev: Array.from(after.pos, (p, k) => p < 0 ? -1 : after.prev[k]),
    expectedOcc: [...after.occ], expectedMoved, expectedAdmitted,
  };
  events.forEach((e) => kinds.add(e.kind));
  productionEvents += events.length;
  cases.push(result);
  return { after, result };
}

const classic = { ...DEFAULTS, rule: CLASSIC, box: false, reroute: true, respawnDelay: 1000 };
const source = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url), 'utf8'));
let presetCases = 0;
for (const { id, roads } of source.places) {
  const net = rasterize(roads, { ...WINDOW, drive: PLACES.find((p) => p.id === id).drive });
  for (const law of LAWS.filter((law) => !law.box)) {
    const opts = { ...classic, ...law };
    let state = init(net, Math.min(24, Math.ceil(net.roadCells * 0.05)), 17, opts);
    for (let frame = 0; frame < 2; frame++) {
      state = productionCase(net, state, opts, `${id}/${law.name}/${frame}`).after;
      presetCases++;
    }
  }
}
assert.equal(presetCases, 24);

// Unit-edge square: the same observed endpoints can arise from a hop or
// an exit+admission. The production grant stream distinguishes them.
const square = network({
  W: 2, H: 2, road: Uint8Array.of(1, 1, 1, 1), exit: Uint8Array.of(1, 0, 0, 0), entries: [1],
  edges: [[0, 1, 0, 0], [1, 3, 0, Math.PI / 2], [3, 2, 0, Math.PI], [2, 0, 0, -Math.PI / 2]],
});
const initial = () => {
  const s = fromGrid(square, [[1, 0], [0, 0]]);
  s.species.fill(0);
  s.next[0] = 1;
  return s;
};
const hopCase = productionCase(square, initial(), classic, 'explicit-hop').result;
const leave = initial(); leave.next[0] = EXIT;
const exitCase = productionCase(square, leave, classic, 'explicit-exit').result;
const combined = productionCase(square, leave, { ...classic, respawnDelay: 0 }, 'explicit-exit-admit').result;
assert.deepEqual(hopCase.expectedPos, combined.expectedPos);
assert.notDeepEqual(hopCase.expectedAdmitted, combined.expectedAdmitted);
assert.deepEqual(exitCase.expectedMoved, [true]);
const admitted = productionCase(square, tow(initial(), 0, 0), { ...classic, respawnDelay: 0 }, 'explicit-admission').result;
assert.deepEqual(admitted.expectedMoved, [false]);
assert.deepEqual(admitted.expectedAdmitted, [true]);
const stopped = initial(); stopped.t = 1;
productionCase(square, stopped, classic, 'wrong-phase-stay');

// Actual legacy immediate refill is rejected by the model's explicit
// source-vacancy fence. This demonstrates a semantic boundary, not a
// modification to production halfStep or a claimed correspondence there.
const refillNet = network({ W: 2, H: 1, road: Uint8Array.of(1, 1),
  exit: Uint8Array.of(0, 1), entries: [1], edges: [[0, 1, 0, 0], [1, 0, 0, Math.PI]] });
const refill = fromGrid(refillNet, [[1, 1]]);
refill.species.fill(0); refill.next.set([1, EXIT]); refill.prev.set([-1, 0]);
const refillCase = productionCase(refillNet, refill, { ...classic, respawnDelay: 0 }, 'production-source-refill', false).result;
assert.equal(refillCase.events[1].kind, 'exit_admit');
assert.equal(refillCase.events[1].source, refillCase.events[1].target);

// TRAIN relay enters a preoccupied source; the finite checker intentionally
// implements the CLASSIC pre-vacancy model and must reject this real trace.
const relayNet = network({ W: 3, H: 1, road: Uint8Array.of(1, 1, 1),
  exit: Uint8Array.of(0, 0, 1), edges: [[0, 1, 0, 0], [1, 2, 0, 0], [2, 1, 0, Math.PI]] });
const relay = fromGrid(relayNet, [[1, 1, 0]]);
relay.species.fill(0); relay.next.set([1, 2]); relay.prev.set([-1, 0]);
productionCase(relayNet, relay, { ...classic, rule: TRAIN }, 'production-train-relay', false);

function rejection(base, id, mutate) {
  const c = structuredClone(base);
  c.id = id; c.provenance = 'synthetic adversarial semantic control'; c.expectedValid = false;
  mutate(c);
  cases.push(c);
  return c;
}
rejection(hopCase, 'stale-source', (c) => { c.events[0].source = 2; });
rejection(hopCase, 'illegal-route', (c) => { c.events[0].target = 3; });
rejection(exitCase, 'exit-without-legal-exit', (c) => { c.routes[0].targets = [1]; });
rejection(admitted, 'admission-at-unregistered-entry', (c) => { c.events[0].target = 3; });
const duplicate = rejection(hopCase, 'two-vehicles-one-target', (c) => {
  c.cars = 2; c.pos = [0, 2]; c.prev = [-1, -1];
  c.routes.push({ prev: -1, cell: 2, targets: [1] });
  c.events.push({ kind: 'hop', source: 2, target: 1 });
});
rejection(duplicate, 'duplicate-prestate-occupancy', (c) => {
  c.pos = [0, 0]; c.events = [{ kind: 'stay', source: 0, target: 0 }, { kind: 'stay', source: 0, target: 0 }];
});

function malformed(id, mutate) {
  const c = structuredClone(hopCase);
  c.id = id; c.provenance = 'synthetic malformed wire control';
  mutate(c); invalidWire.push(c);
}
malformed('unknown-position-is-not-outside', (c) => { c.pos[0] = -2; });
malformed('out-of-range-source', (c) => { c.events[0].source = c.cells; });
malformed('out-of-range-target', (c) => { c.events[0].target = c.cells; });
malformed('unknown-event-kind', (c) => { c.events[0].kind = 'inferred-vanish'; });
malformed('stay-cannot-change-endpoints', (c) => { c.events[0].kind = 'stay'; });
malformed('duplicate-route-key', (c) => { c.routes.push(structuredClone(c.routes[0])); });
malformed('bad-tag-array-size', (c) => { c.pos.push(-1); });
malformed('bad-entry-array-size', (c) => { c.entries.pop(); });
malformed('bad-route-cell', (c) => { c.routes[0].cell = c.cells; });
malformed('unknown-route-context', (c) => { c.routes[0].prev = -3; });
malformed('bad-route-sentinel', (c) => { c.routes[0].targets.push(-2); });
malformed('fractional-cell', (c) => { c.pos[0] = 0.5; });
malformed('missing-provenance', (c) => { c.provenance = ''; });
malformed('missing-events', (c) => { delete c.events; });
malformed('bad-expected-size', (c) => { c.expectedMoved = []; });
malformed('admit-claim-with-onstreet-source', (c) => { c.events[0].kind = 'admit'; });

// A real production prefix, with one fixed finite table containing its
// visited arrival contexts, is checked both as a whole and at every prefix.
const prefixFrames = [];
let prefixState = initial();
for (let i = 0; i < 8; i++) {
  const frame = productionCase(square, prefixState, classic, `finite-prefix-${i}`);
  prefixFrames.push(frame.result); prefixState = frame.after;
}
const model = structuredClone(prefixFrames[0]);
const table = new Map();
for (const c of prefixFrames) for (const row of c.routes) {
  const key = `${row.prev}:${row.cell}`;
  if (!table.has(key)) table.set(key, structuredClone(row));
  else table.get(key).targets = [...new Set([...table.get(key).targets, ...row.targets])];
}
model.routes = [...table.values()];
histories.push({ id: 'production-eight-step-prefix', model,
  batches: prefixFrames.map((c) => c.events), expectedValid: true,
  expectedPrefixes: [model.pos, ...prefixFrames.map((c) => c.expectedPos)] });
const badHistory = structuredClone(histories[0]);
badHistory.id = 'invalid-middle-batch-rejects-history'; badHistory.expectedValid = false;
badHistory.batches[3][0].source = 0; badHistory.batches[3][0].target = 0; badHistory.batches[3][0].kind = 'stay';
badHistory.expectedPrefixes = [];
histories.push(badHistory);

assert.deepEqual([...kinds].sort(), ['admit', 'exit', 'exit_admit', 'hop', 'stay']);
const packet = { cases, invalidWire, histories };
const [leanVerifier, artifactDirectory] = process.argv.slice(2);
let lean = null;
if (leanVerifier) {
  assert.ok(artifactDirectory, 'an artifact directory is required with the Lean checker');
  mkdirSync(artifactDirectory, { recursive: true });
  const path = join(artifactDirectory, 'traffic-events-cases.json');
  writeFileSync(path, JSON.stringify(packet) + '\n');
  const checked = spawnSync(leanVerifier, ['--events', path], { encoding: 'utf8', timeout: 120000 });
  if (checked.error) throw checked.error;
  assert.equal(checked.status, 0, checked.stderr || checked.stdout);
  lean = checked.stdout.trim();
}
console.log(JSON.stringify({ presetCases, productionEvents,
  acceptedBatches: cases.filter((c) => c.expectedValid).length,
  rejectedBatches: cases.filter((c) => !c.expectedValid).length,
  malformedWire: invalidWire.length, finiteHistories: histories.length,
  eventKinds: [...kinds].sort(), lean,
  scope: 'finite simulation event correspondence; no field calibration or phase-service theorem' }));
