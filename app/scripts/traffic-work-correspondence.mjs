import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { replay } from './r2-amortized-reference.mjs';

const outside = (cell) => cell < 0 ? null : cell;
const movement = (event) => ['hop', 'exit', 'exit_admit'].includes(event.kind);
const admission = (event) => ['admit', 'exit_admit'].includes(event.kind);

/** Decode actual reference grants and admissions, not inferred position
 * changes alone: exit+admit must remain two events even for one recycled tag.
 * These model tags do not establish physical vehicle or trip continuity. */
function eventFor(before, transition, k) {
  const source = outside(before.p[k]);
  const target = outside(transition.next.p[k]);
  const want = transition.want[k];
  if (source !== null && want !== -2) {
    if (want === -1) return { kind: target === null ? 'exit' : 'exit_admit', source, target };
    assert.equal(target, want);
    return { kind: 'hop', source, target };
  }
  if (source === null && target !== null) return { kind: 'admit', source, target };
  assert.equal(target, source);
  return { kind: 'stay', source, target };
}

export function collectWorkCases({ openHorizon = 64, maxMerges = 12 } = {}) {
  assert.ok(Number.isInteger(openHorizon) && openHorizon > 0);
  const cases = new Map();
  let combinedEvents = 0;
  let emptyContinuationFrames = 0;
  const referenceSummary = replay({ maxMerges, onFrame(record) {
    if (record.open && record.before.t >= openHorizon) return;
    const id = `${record.geometric ? 'unit-grid' : 'same-axis'}-${record.merges}-${record.open ? 'open' : 'closed'}`;
    if (!cases.has(id)) cases.set(id, {
      id, mode: record.open ? 'open' : 'closed', geometric: record.geometric,
      merges: record.merges, heights: [...record.heights],
      menus: record.targets.map((q) => [outside(q)]), entries: [...record.entries],
      initial: record.before.p.map(outside), Q: 2, focal: record.focal,
      enforcedQuota: record.open ? null : 0, prospective: !record.open, frames: [],
      strongerPolicyNegativeAt: record.geometric && record.merges === 2 && record.open ? 11 : null,
    });
    const events = record.before.p.map((_, k) => eventFor(record.before, record.transition, k));
    const moves = events.filter(movement).length;
    const admits = events.filter(admission).length;
    assert.equal(moves, record.transition.moves);
    assert.equal(admits, record.transition.admissions);
    combinedEvents += events.filter((e) => e.kind === 'exit_admit').length;
    if (record.emptyContinuation) emptyContinuationFrames++;
    cases.get(id).frames.push({ t: record.before.t,
      before: record.before.p.map(outside), after: record.transition.next.p.map(outside),
      ageBefore: [...record.before.a], ageAfter: [...record.transition.next.a],
      owners: record.transition.owners.map((entry) => [...entry]),
      events, reportedMovements: moves, reportedAdmissions: admits,
    });
  } });
  const accepted = [...cases.values()];
  assert.equal(accepted.length, 4 * maxMerges);
  assert.ok(combinedEvents > 0);
  assert.ok(emptyContinuationFrames > 0);
  for (const c of accepted) {
    assert.deepEqual(c.initial, c.frames[0].before);
    for (let t = 0; t < c.frames.length; t++) {
      assert.equal(c.frames[t].t, t);
      if (t) assert.deepEqual(c.frames[t].before, c.frames[t - 1].after);
    }
    if (c.mode === 'closed') {
      assert.ok(c.frames.at(-1).after.every((p) => p === null));
      const work = c.initial.reduce((sum, p) => sum + (p === null ? 0 : c.heights[p]), 0);
      assert.equal(c.frames.length, c.Q * work);
    }
  }

  const rejected = [];
  const copy = (c, suffix) => ({ ...structuredClone(c), id: `${c.id}-${suffix}` });
  // The exit remains a safe-rank witness, but a newly admitted return edge
  // creates a legal cycle. A certificate for *all* legal hops must reject it.
  const cycle = copy(accepted.find((c) => c.id === 'same-axis-1-closed'), 'cycle-with-exit-witness');
  cycle.menus[1].push(0);
  rejected.push({ candidate: cycle, expectedError: 'DAG certificate' });

  // The observed count is finite, but an open controller has not enforced
  // that number as a future quota. An accurate hindsight count is not a token rule.
  const hindsight = copy(accepted.find((c) => c.mode === 'open' && c.frames.some((f) => f.reportedAdmissions)),
    'observed-count-is-not-enforcement');
  hindsight.enforcedQuota = hindsight.frames.reduce((sum, f) => sum + f.reportedAdmissions, 0);
  hindsight.prospective = true;
  rejected.push({ candidate: hindsight, expectedError: 'prospective quota' });

  const noQuota = copy(hindsight, 'admissions-exceed-zero-quota');
  noQuota.mode = 'closed';
  noQuota.enforcedQuota = 0;
  rejected.push({ candidate: noQuota, expectedError: 'admission quota' });

  const combined = copy(accepted.find((c) => c.frames.some((f) => f.events.some((e) => e.kind === 'exit_admit'))),
    'combined-admission-undercounted');
  combined.frames.find((f) => f.events.some((e) => e.kind === 'exit_admit')).reportedAdmissions--;
  rejected.push({ candidate: combined, expectedError: 'reported admissions' });

  const missingSource = copy(accepted[0], 'event-source-substitution');
  missingSource.frames[0].events.find((e) => e.kind === 'exit').source = 0;
  rejected.push({ candidate: missingSource, expectedError: 'invalid event batch' });

  const idle = copy(accepted[0], 'eligible-exit-withheld');
  const first = idle.frames[0];
  first.after = [...first.before];
  first.events = first.before.map((p) => ({ kind: 'stay', source: p, target: p }));
  first.ageAfter = first.ageBefore.map((age, k) => first.before[k] === null ? 0 : age + 1);
  first.reportedMovements = 0;
  first.reportedAdmissions = 0;
  rejected.push({ candidate: idle, expectedError: 'owner work conservation' });

  const frozen = copy(accepted.find((c) => c.id === 'same-axis-1-closed'), 'wrong-phase-age-frozen');
  const quiet = frozen.frames.find((f) => f.t % 2 === 1 && f.reportedMovements === 0 &&
    f.reportedAdmissions === 0 && f.before.some((p) => p !== null));
  assert.ok(quiet);
  quiet.ageAfter = [...quiet.ageBefore];
  rejected.push({ candidate: frozen, expectedError: 'full stopped aging' });

  const wrongPhase = copy(accepted.find((c) => c.id === 'same-axis-1-closed'), 'wrong-phase-hop-granted');
  const wrongFrame = wrongPhase.frames[1];
  const occupied = new Set(wrongFrame.before.filter((p) => p !== null));
  const mover = wrongFrame.before.findIndex((p) => p !== null &&
    wrongPhase.menus[p].some((q) => q !== null && !occupied.has(q)));
  assert.ok(mover >= 0);
  const target = wrongPhase.menus[wrongFrame.before[mover]].find((q) => q !== null && !occupied.has(q));
  wrongFrame.events[mover] = { kind: 'hop', source: wrongFrame.before[mover], target };
  wrongFrame.after[mover] = target;
  wrongFrame.ageAfter[mover] = 0;
  wrongFrame.reportedMovements++;
  rejected.push({ candidate: wrongPhase, expectedError: 'signal permission' });

  const priority = copy(accepted.find((c) => c.id === 'same-axis-1-closed'), 'owner-tie-substitution');
  assert.deepEqual(priority.frames[1].owners, [[1, 0]]);
  priority.frames[1].owners[0][1] = 1;
  rejected.push({ candidate: priority, expectedError: 'owner table' });

  const sourceSha256 = createHash('sha256').update(readFileSync(new URL('./r2-amortized-reference.mjs', import.meta.url))).digest('hex');
  return {
    payload: { scope: 'independent-pr46-reference', sourceSha256, cases: accepted, rejected },
    summary: {
      scope: 'Actual transitions of the independent PR #46 reference scheduler; no production-policy or field-data claim.',
      sourceSha256, cases: accepted.length, rejectedCases: rejected.length,
      frames: accepted.reduce((sum, c) => sum + c.frames.length, 0),
      tagEvents: accepted.reduce((sum, c) => sum + c.frames.length * c.initial.length, 0),
      combinedExitAdmissionEvents: combinedEvents, emptyContinuationFrames,
      referenceFrames: referenceSummary.frames, referenceWorkChecks: referenceSummary.workChecks,
      referenceScheduleChecks: referenceSummary.scheduleChecks,
    },
  };
}

export function runWorkCorrespondence(leanVerifier = null, artifactDirectory = null) {
  const { payload, summary } = collectWorkCases();
  if (leanVerifier) {
    assert.ok(artifactDirectory, 'an artifact directory is required with the Lean verifier');
    mkdirSync(artifactDirectory, { recursive: true });
    const path = join(artifactDirectory, 'traffic-work-cases.json');
    writeFileSync(path, JSON.stringify(payload) + '\n');
    const result = spawnSync(leanVerifier, ['--work', path], { encoding: 'utf8', timeout: 120000 });
    if (result.error) throw result.error;
    assert.equal(result.status, 0, result.stderr || result.stdout);
    summary.lean = result.stdout.trim();
  }
  return summary;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runWorkCorrespondence(...process.argv.slice(2)), null, 2));
