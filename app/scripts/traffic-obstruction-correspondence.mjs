import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { network } from '../src/raster.js';
import { CLASSIC, DEFAULTS, EXIT, fromGrid, halfStep, previewMoves, turnOptions } from '../src/sim.js';
import { safeCells, trapSet } from '../src/realflow.js';

// This script observes real halfStep events in a constructed simulator
// graph. It is not field evidence and does not prove all-time JS execution.
// The corresponding all-time *model* orbit is BML.TrafficObstruction.run.
const rules = { ...DEFAULTS, rule: CLASSIC, box: false, reroute: true, green: 1, slow: 0, respawnDelay: 1 };
const routes = [-1, 0, 1].flatMap((prev) => [
  { prev, cell: 0, targets: [1] },
  { prev, cell: 1, targets: [1, -1] },
]);

const makeNetwork = () => network({
  W: 2, H: 1, road: Uint8Array.of(1, 1), exit: Uint8Array.of(0, 1), entries: [1],
  edges: [[0, 1, 0, 0], [1, 1, 0, 0]],
});

const initialState = (net, seed) => {
  const state = fromGrid(net, [[1, 1]]);
  state.species.fill(0);
  state.next.set([1, EXIT]);
  state.prev.fill(-1);
  state.seed = seed;
  return state;
};

const requestAge = (t) => Math.floor((t + 1) / 2);
const orbitPositions = (t) => [0, t % 2 === 0 ? 1 : -1];
const orbitEvents = (t) => [
  { kind: 'stay', source: 0, target: 0 },
  t % 2 === 0 ? { kind: 'exit', source: 1, target: -1 } : { kind: 'admit', source: -1, target: 1 },
];

export function obstructionControls({ seeds = 8, steps = 128 } = {}) {
  assert.ok(Number.isSafeInteger(seeds) && seeds > 0);
  assert.ok(Number.isSafeInteger(steps) && steps >= 64 && steps % 2 === 0 && steps < 2 ** 31 - 2);
  const net = makeNetwork();
  assert.deepEqual(safeCells(net, rules).ranks, [1, 0]);
  // These are the actual arrival-indexed legal menus, including the
  // self-hop that CLASSIC can never grant at its occupied source.
  for (const prev of [-1, 0, 1]) {
    assert.deepEqual(turnOptions(net, 0, prev, rules).cells, [1]);
    assert.deepEqual(turnOptions(net, 1, prev, rules).cells, [1, EXIT]);
  }
  const cases = [], histories = [];
  let wrongPhaseVacancies = 0, blockedRequests = 0, departures = 0, admissions = 0;
  let respawnSelfChoices = 0, respawnExitChoices = 0;
  for (let seed = 1; seed <= seeds; seed++) {
    let state = initialState(net, seed);
    const frames = [];
    for (let t = 0; t < steps; t++) {
      const even = t % 2 === 0;
      assert.equal(state.t, t);
      assert.deepEqual([...state.pos], orbitPositions(t));
      assert.deepEqual([...state.occ], orbitPositions(t));
      assert.deepEqual([...state.prev], [-1, -1]);
      assert.equal(state.wait[0], requestAge(t));
      assert.equal(state.wait[1], 0);
      assert.deepEqual([...trapSet(net, state, rules, { reroute: true })], [0, 0]);
      const { want, go } = previewMoves(net, state, rules);
      assert.deepEqual([...go], [0, Number(even)]);
      assert.equal(want[0], even ? 1 : -3);
      assert.equal(want[1], even ? EXIT : -3);
      const jointOpportunity = state.occ[1] < 0 && t % 2 === 0;
      assert.equal(jointOpportunity, false);
      const genuineAttempt = want[0] === EXIT || (want[0] >= 0 && state.occ[want[0]] < 0);
      assert.equal(genuineAttempt, false);
      if (state.occ[1] < 0) wrongPhaseVacancies++;
      if (want[0] !== -3) blockedRequests++;

      const after = halfStep(net, state, rules);
      const observedEvents = Array.from(state.pos, (source, k) => {
        const target = after.pos[k];
        assert.equal(Boolean(go[k]), after.last[k] === state.t);
        if (go[k]) {
          if (want[k] === EXIT) return { kind: target < 0 ? 'exit' : 'exit_admit', source, target };
          return { kind: 'hop', source, target };
        }
        return source < 0 && target >= 0 ? { kind: 'admit', source: -1, target } :
          { kind: 'stay', source, target };
      });
      assert.deepEqual(observedEvents, orbitEvents(t));
      assert.deepEqual([...after.pos], orbitPositions(t + 1));
      assert.deepEqual([...after.occ], orbitPositions(t + 1));
      assert.deepEqual([...after.prev], [-1, -1]);
      assert.equal(after.wait[0], requestAge(t + 1));
      assert.equal(after.wait[1], 0);
      assert.equal(after.last[0], -1);
      assert.equal(after.moved, Number(even));
      assert.equal(after.exited - state.exited, Number(even));
      if (even) {
        assert.equal(after.occ[1], -1, 'the departure must leave a vacant checkpoint');
        departures++;
      } else {
        assert.ok(after.next[1] === 1 || after.next[1] === EXIT);
        if (after.next[1] === 1) respawnSelfChoices++;
        else respawnExitChoices++;
        admissions++;
      }
      const frame = {
        id: `wrong-phase-orbit/seed-${seed}/step-${t}`,
        provenance: `simulation; app/src/sim.js previewMoves and halfStep; initial seed=${seed}; t=${t}; natural-time orbit only finitely compared`,
        cells: 2, cars: 2, pos: [...state.pos], prev: [...state.prev], routes,
        entries: [false, true], events: observedEvents, expectedValid: true,
        expectedPos: [...after.pos], expectedPrev: [...after.prev], expectedOcc: [...after.occ],
        expectedMoved: [false, even], expectedAdmitted: [false, !even],
      };
      cases.push(frame);
      frames.push(frame);
      state = after;
    }
    histories.push({
      id: `production-wrong-phase-orbit/seed-${seed}/${steps}-half-steps`,
      model: frames[0], batches: frames.map((frame) => frame.events), expectedValid: true,
      expectedPrefixes: [frames[0].pos, ...frames.map((frame) => frame.expectedPos)],
    });
  }
  assert.equal(wrongPhaseVacancies, seeds * steps / 2);
  assert.equal(departures, seeds * steps / 2);
  assert.equal(admissions, seeds * steps / 2);
  assert.ok(respawnSelfChoices > 0 && respawnExitChoices > 0, 'both actual random route outcomes must be covered');

  // The native event checker must reject a proposed CLASSIC hop into the
  // occupied target, even though that target's current occupant exits.
  const occupiedHop = structuredClone(cases[0]);
  occupiedHop.id = 'rejected-focal-hop-into-departing-source';
  occupiedHop.provenance = 'synthetic adversarial mutation of a production batch';
  occupiedHop.expectedValid = false;
  occupiedHop.events[0] = { kind: 'hop', source: 0, target: 1 };
  cases.push(occupiedHop);

  const malformed = structuredClone(cases[0]);
  malformed.id = 'rejected-unknown-position-sentinel';
  malformed.provenance = 'synthetic malformed wire control';
  malformed.pos[0] = -2; // -1 means known outside; -2 is not another spelling.

  const invalidHistory = structuredClone(histories[0]);
  invalidHistory.id = 'rejected-history-containing-occupied-hop';
  invalidHistory.expectedValid = false;
  invalidHistory.expectedPrefixes = [];
  invalidHistory.batches[0][0] = { kind: 'hop', source: 0, target: 1 };
  histories.push(invalidHistory);

  return {
    packet: { cases, invalidWire: [malformed], histories },
    summary: {
      seeds, halfStepsPerSeed: steps, productionHalfSteps: seeds * steps,
      productionEvents: 2 * seeds * steps,
      wrongPhaseVacancies, blockedRequests, departures, admissions,
      respawnSelfChoices, respawnExitChoices,
      focalMovements: 0, focalGenuineAttempts: 0, ranks: [1, 0],
      acceptedBatches: cases.filter((row) => row.expectedValid).length,
      rejectedBatches: 1, malformedWire: 1,
      acceptedHistories: seeds, rejectedHistories: 1,
      prefixCheckpoints: seeds * (steps + 1),
      scope: 'finite production simulation correspondence to the proved alternating model orbit; no field observation or all-time JS/PRNG claim',
    },
  };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const { packet, summary } = obstructionControls();
  const [leanVerifier, artifactDirectory] = process.argv.slice(2);
  let lean = null;
  if (leanVerifier) {
    assert.ok(artifactDirectory, 'artifact directory required with native checker');
    mkdirSync(artifactDirectory, { recursive: true });
    const path = join(artifactDirectory, 'traffic-obstruction-cases.json');
    writeFileSync(path, JSON.stringify(packet) + '\n');
    const result = spawnSync(leanVerifier, ['--events', path], { encoding: 'utf8', timeout: 120000 });
    if (result.error) throw result.error;
    assert.equal(result.status, 0, result.stderr || result.stdout);
    lean = result.stdout.trim();
  }
  console.log(JSON.stringify({ ...summary, lean }));
}
