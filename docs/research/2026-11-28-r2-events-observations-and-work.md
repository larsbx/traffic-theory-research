# R2: events, observations, and derived work bounds

This increment continues the proof bank from PR #44 and the signal/merge and
shared-work developments in PRs #45–46, on the checked-out main revision
`7154c36`. It connects mathematical objects to actual source rows and simulator
events, and closes the event-accounting and controller-progress gaps for the
specified strengthened policy. The production simulator remains unchanged.

There are three distinct evidence layers:

| Layer | Objects | What establishes the claim |
| --- | --- | --- |
| Recorded observations | Source-scoped vehicle IDs, frames, timestamps, coordinates, speeds, lane labels, and row references | Pinned input bytes; exact-decimal parsing; independent Lean classification of the complete supplied tracks |
| Traffic model | Finite tags, cells, arrival contexts, legal options, named movements and admissions | Lean's checked event kernel and proofs about every accepted run |
| Implementation correspondence | Actual `previewMoves`/`halfStep` events, and the separate PR #46 reference scheduler | Explicit finite cases evaluated by the native Lean checker, with positive and rejection controls |

A sampled trajectory is not automatically a complete traffic state. A model
tag reused after admission is not automatically the same physical trip.
Neither distinction is erased by a successful numerical replay.

## 1. The original service assumption is false without a joint opportunity

`BML/TrafficObstruction.lean` constructs an infinite accepted two-cell,
two-tag run. The upstream tag stays in cell 0 and its only non-self option is
the horizontal hop into cell 1. The downstream tag exits on even steps and
is admitted back into cell 1 on odd steps.

| Checkpoint | Cell 1 | Upstream phase eligibility | Event during that step |
| --- | --- | --- | --- |
| Even | Occupied | Horizontal phase is available | Downstream tag exits; upstream request fails |
| Odd | Vacant | Horizontal phase is unavailable | Downstream tag is admitted into the vacancy |

Every two-checkpoint window contains a vacancy, but there is never a joint
vacancy and upstream movement phase. Every departure leaves a vacant next
checkpoint. The graph has a valid safe-cell rank certificate, and its greatest
structural trap is empty at every checkpoint. Nevertheless, the focal tag
never moves. Lean proves failure of `OpportunityFair` and of every finite
`BoundedService (2*K) K` cap. The legacy request counter follows
`requestAge(t) = (t+1)/2`, not elapsed stopped time.

The corresponding production example has a self option and EXIT at cell 1.
After admission, either choice gives the same projected orbit: a self
commitment is occupied at the next even checkpoint, so re-routing chooses
the only clear alternative, EXIT. Odd-step readmission precedes the next
horizontal opportunity. This explains why the finite replay is independent
of the observed self/EXIT routing choices. The all-time Lean theorem concerns
the checked event model; no general JavaScript or PRNG semantics theorem is
claimed.

`traffic-obstruction-correspondence.mjs` runs the real production functions
for eight seeds and 128 steps each. It checks the state projection, explicit
grants, admission events, and the request-age recurrence, then submits the
complete histories and every prefix to Lean. A separate production control
in `traffic-events-correspondence.mjs` shows that immediate respawn can refill
a start-occupied departure cell. That case is correctly rejected by the
stronger model's admission fence.

Thus independent bounds on departure, vacancy frequency, and signal frequency
do not imply service. Their useful intersection and actual grants must be
established. Increasing a counter cannot create a missing opportunity.

## 2. A checked event kernel supplies the missing state semantics

`BML/TrafficEvents.lean` defines the event of each finite tag as one of:

| Constructor | Before | After | Movement count | Admission count |
| --- | --- | --- | ---: | ---: |
| `stay p` | `p` | `p` | 0 | 0 |
| `hop p q` | Cell `p` | Cell `q` | 1 | 0 |
| `exit p` | Cell `p` | Outside | 1 | 0 |
| `admit q` | Outside | Cell `q` | 0 | 1 |
| `exitAdmit p q` | Cell `p` | Cell `q` | 1 | 1 |

The last row is essential: a hop and an exit followed by admission can have
identical endpoint positions but different injected work. The theorem
`endpoints_do_not_determine_admissions` proves that ambiguity directly.

For each batch the executable kernel checks exclusive initial positions,
the claimed source of every event, the legal arrival-indexed route or entry,
vacancy at the **start** of the batch for every arrival, and exclusive final
positions. It computes both the next positions and arrival contexts.
In particular, an admission cannot consume a cell occupied at the start,
even if a departure frees it earlier in the same JavaScript half-step.

The proved consequences include source vacancy after departures, preservation
of a stationary tag's position and arrival context, and an exact bridge to
`RouteProgress.Trace`. `replay?_iff` identifies executable success with an
inductive history of those checked, computed transitions. Prefix and append
theorems make the finite-history contract explicit.

`BML/TrafficHistory.lean` proves that every accepted finite history embeds in
an infinite event run that simply stays after its endpoint. `extend_checked_policy`
transfers replay-matched states, event batches, and finite local controller checks
to `ProtectedPrefix`. The idle suffix is a mathematical extension for applying
the finite theorem, not a forecast or an assumption that the controller follows
the policy after the checked horizon.

The `--events` wire uses only `-1` for known outside/EXIT; the separate
`--work` wire uses JSON `null` decoded to `Option`. Production request sentinels
such as `-2` and `-3` are decoded by meaning; they cannot silently become
outside positions. Unknown observations belong to a different type.

## 3. Local controller rules derive a progress window

`BML/TrafficPolicy.lean` makes the joint controller requirement local and
executable. It checks full stopped-half-step aging, fixed arrival-indexed
legal menus, oldest-claimant ownership before phase filtering, actual signal
permission for each movement, and **some actual hop or exit** when a protected
owner's clear legal option is jointly eligible. This sufficient shared-work
contract does not require that particular owner to move when another movement
already supplies progress; it does not characterize the full scheduler.
Admissions obey the start-vacancy fence and the separate quota; this work bound
does not additionally require excluding every admission from an owned vacancy.
Lower tag IDs break age ties. EXIT is a
legal movement option with its arrival axis, not a vacant street cell.

The proof assumes a positive green duration `G`, protection threshold `L`,
productive menus (every arrival context offers EXIT or a non-self hop), and
a positive height that decreases on every legal non-self hop. These are
separately checked conditions. The production simulator's unsuccessful-request
counter does not establish the aging condition.

The progress argument is derived as follows:

1. If a block has neither movements nor admissions, the event constructors
   force every event to be `stay`. Positions, arrival contexts, legal menus,
   and vacancies therefore remain fixed.
2. Every present tag ages by the same elapsed number of half-steps. After
   `L` steps they are protected. The legal claimant sets and age/tie ordering
   remain fixed, so an oldest owner remains the owner through a quiet suffix.
3. A minimum-height occupied cell has a clear legal non-self option or EXIT.
   Otherwise its lower-height target would contain a still smaller occupied
   height, a contradiction.
4. Select the protected owner of that clear option. The existing exact clock
   theorem supplies a jointly permitted phase/signal slot in fewer than `2G`
   steps. The local service rule forces an actual movement, contradicting
   the supposedly quiet block.

Consequently every nonempty block of length

\[
Q=L+2G
\]

contains a movement or admission. `BlockProgress` is a conclusion of the
controller proof, not a renamed hypothesis. The direct quota and evacuation
corollaries use this conclusion.

`ProtectedPrefix` and `checkProtectedPrefix_sound` restrict the controller
checks to the certified horizon. Their progress, quota and evacuation theorems
need no controller assumption beyond that horizon; the advertised deadline
must fit within it. This is the appropriate contract for finite exported data.

A stronger rule requiring movement whenever **any** protected eligible
claimant exists is also exposed as a distinct predicate. It is not equivalent
to pre-phase ownership: the PR #46 reference can reserve a vacancy for an
older horizontal tag during a vertical phase. The correspondence controls
retain such a frame as valid under ownership and invalid under the stronger
predicate. This distinction prevents a convenient abstraction from silently
changing the policy being checked.

## 4. Actual events imply work accounting and the deadline

Let `h(c)` be a positive integer height bounded by `D`, decreasing on every
actual legal non-self hop. Define `Phi(t)` as the sum of heights over on-street
tags. Hops and exits consume at least one unit; admissions inject at most `D`.
The event kernel and the all-hop height certificate prove, batch by batch,

\[
\Phi(t+1)+m_t\leq\Phi(t)+D a_t.
\]

`BML/TrafficWork.lean` sums those inequalities, proving for every interval

\[
\Phi(s+n)+M[s,s+n)\leq\Phi(s)+D A[s,s+n).
\]

The sums are derived from event constructors, including both contributions
of `exitAdmit`. There is no imported assertion that the desired global
inequality happens to hold.

If a focal tag remains at cell `c`, its contribution `h(c)` remains in the
potential and cannot pay for other tags' movements. With at most `A` admissions
in the relevant interval, the number of movements plus admissions is at most

\[
B=\Phi(s)-h(c)+(D+1)A.
\]

Every nonempty `Q`-block needs an event. Therefore a focal next movement must
occur at an offset strictly less than

\[
\boxed{Q\,[\Phi(s)-h(c)+(D+1)A+1]}.
\]

The finite block-count contradiction, retained focal credit, telescoping,
and concrete event-to-ledger bridge are all Lean proofs. For a closed DAG,
the analogous whole-region theorem proves evacuation by `Q*Phi(s)` steps.

### The exact PR #44 service interface is derived

`BML/TrafficServiceBridge.lean` connects the work theorem to the original
recurrence's actual predicates. With `N` finite tags and initial token count
`A = R(0)`, define the uniform cap

\[
K=(L+2G)\,[ND+(D+1)A+1].
\]

Lean proves `Phi(s) <= N*D`, `R(s) <= R(0)`, and that every applicable focal
work deadline is at most `K`. A strictly ordered selection of `K` checkpoints
needs a window of length at least `K`. Continued waiting over such a window
contradicts the derived movement deadline, independently of how its clear
checkpoints were selected. Therefore `protected_bounded_service` proves the
original `Trace.BoundedService horizon K` predicate.

`protected_joint_guarantee` pairs that service theorem with the event kernel's
derived `LeavesVacancy`. `protected_moves_before_rank_bound` then instantiates
the existing recurrence `B(0)=K`, `B(r+1)=K*(B(r)+1)`, given its checked rank and
arrival-menu certificate and enough certified horizon. The sharper shared-work
deadline is normally preferable; the recurrence bridge closes the original API
obligation without assuming a separate joint service guarantee. Its scope is
still the explicit productive DAG, local policy and nonrenewing admission budget.

### A prospective quota is an enforced rule

`AdmissionBudget` supplies a remaining-token function with the local debit
condition

\[
R(t+1)+a_t\leq R(t).
\]

Lean derives `A[s,s+n) <= R(s)`. The prospective bound uses the token count
available at the start and this future-enforced transition rule. Counting
admissions in an already observed future window gives only a retrospective
conditional certificate. The native controls reject promotion of an open
reference run's observed admission count into an enforced quota.

This is a sufficient repair for a productive DAG with controlled admissions;
it is not a theorem of minimality over all possible controllers. It needs no
unproved per-tag fairness premise: finite available work bounds all interfering
events. With unrestricted replenishment, the alternating counterexample
remains admissible. With cycles, a single decreasing safe-rank witness is
insufficient: every actual legal non-self hop must decrease the work height.

## 5. Mathematical objects in the actual Lankershim records

The observation adapter uses the three pinned CSV byte streams already
specified by `data/lankershim-field-replay/result.json`. A source identity
commits to the query and all input hashes. A vehicle identity is the pair
`(source, vehicle_id)`, not a globally unique bare number or a CSV filename.
An identity can continue across partition boundaries.

`BML/FieldObservation.lean` defines unit-typed exact quantities: feet and feet
per second are different types, with positive denominators checked at decoding.
A sample contains that identity, frame, millisecond timestamp, longitudinal
front-center coordinate, speed, lane/section/intersection labels, and source
SHA/CSV-row provenance. Decimal lexemes remain available in the evidence file.

For samples `a,b` and virtual cut `c`, the accepted nominal crossing predicate is

\[
\begin{aligned}
\operatorname{sameIdentity}(a,b)&,\\
b.\mathrm{frame}&=a.\mathrm{frame}+1,\\
b.\mathrm{timeMs}&=a.\mathrm{timeMs}+100,\\
a.y&<c\leq b.y.
\end{aligned}
\]

The kernel proves this exact characterization, the 100-ms reporting window,
rejection under identity or either clock mismatch, exclusion of gap candidates,
and exclusion of counting both sides of one shared sample as successive forward
crossings. A crossing has a nominal window `(a.timeMs,b.timeMs]`; the downstream
timestamp is a reporting endpoint, not an observed instantaneous crossing time.

The native checker reconstructs consecutive pairs independently for each
recorded source/vehicle track and requires the supplied pair inventory to match.
Duplicate, omitted, and unordered records are rejection controls. It then
evaluates every Lean classification against the Python adapter's result using
exact integers. The CSV parser, source hashing, and the native compiler remain
explicit implementation trust boundaries; they are not kernel proofs of CSV
semantics or physical measurement accuracy. The adapter hashes and parses the
same byte buffer, with a replacement-between-read-and-parse regression control.

### Actual observations and results

| Quantity | Result | Evidence type |
| --- | ---: | --- |
| Source rows | 100,667 | Pinned byte streams and parsed inventory |
| Source-scoped vehicle IDs | 330 | Recorded identifiers |
| Consecutive pairs | 100,337 | Independent native inventory check |
| Adjacent in both clocks | 100,323 | Lean classification |
| Uncertain intervening trajectories | 14 | Lean classification, not inferred exits |
| Recorded lane-code changes | 18 | Lean classification |
| First accepted brackets at 330 / 340 / 350 ft | 322 / 254 / 252 | 301,011 native pair/cut classifications |
| Gap candidates at 340 ft | 6 | Explicitly unaccepted candidates |
| Sustained upstream slow proxies | 9 | Python aggregation; not a Lean queue-causation theorem |

The original 22 time-bin counts and downstream-lane counts also match the
pinned baseline. First crossing means first accepted bracket for that identity
at that cut; it does not count every later recrossing as a new vehicle.

Concrete row-backed examples from `part0.csv`:

| Recorded object | Samples | Correct mathematical interpretation |
| --- | --- | --- |
| Vehicle 307, rows 6078 and 6101 | Frames 2694→2695, times 1118936969300→1118936969400 ms, 349.993→351.04 ft, lane 2 | Accepted nominal bracket at 350 ft |
| Vehicle 372, rows 7286 and 7321 | Frames 2751→2753, times 1118936975000→1118936975200 ms, 338.229→344.341 ft | Unaccepted gap candidate at 340 ft |
| Vehicle 481, rows 8135 and 8148 | Frames 2810→2811, 271.305→272.9 ft, lane 1→2 | Recorded lane-code change; no invented cell hop |

### Unknown occupancy and physical signal claims

The observation type distinguishes three cases: unknown; positively known
outside; positively assigned to a cell. Lean proves that a missing sample is
compatible with either an occupied or an unoccupied state. Vacancy follows
from no observed occupant only if observations are complete over the entire
relevant population and the cell mapping is sound. Completeness over the 330
filtered IDs alone is not completeness over all road users.

Physical signal comparison additionally needs independently registered stop-line
geometry, controller clock alignment, and spatial error bounds. A robust spatial
envelope must put the earlier position below every allowed stop-line coordinate
and the later position at or beyond every allowed coordinate. Lean proves the
corresponding implication under the stated error bounds.

For a time window `(lo,hi]`, offset interval `[offsetLo,offsetHi]`, and controller
phase `[phaseLo,phaseHi)`, the robust clock test requires

\[
phaseLo\leq lo+offsetLo,\qquad hi+offsetHi<phaseHi,
\]

along with nonempty window/phase and ordered offset bounds. Its theorem covers
all rational sub-millisecond times and offsets, not just integer sample ticks.
The registration predicate rejects virtual cuts, candidate clock alignments,
missing spatial bounds, and nominal-only brackets.

The current data supplies none of those physical registrations, a complete
lane-to-cell occupancy mapping, or an enforced admission policy. Consequently
the field checker makes **zero model-transition claims and zero physical phase
claims**. Applying the waiting theorem in seconds would require those mappings,
controller invariants, and a justified duration for a model half-step.

## 6. Verification and reproduction

The native executable has distinct `--events`, `--work`, and `--field` input
contracts. Samples cannot be decoded as traffic events. The axiom audit checks
all new proof modules, decoders, and the executable entry point, allowing only
the existing standard Lean axioms `propext`, `Quot.sound`, and `Classical.choice`.
No `sorry`, new axiom, or `native_decide` proof certificate is accepted.

From the repository root:

```sh
cd formal/lean
lake build BML traffic_evidence_check
lake env lean TrafficEvidenceAudit.lean
cd ../..
node app/scripts/traffic-events-correspondence.mjs formal/lean/.lake/build/bin/traffic_evidence_check .artifacts/events
node app/scripts/traffic-work-correspondence.mjs formal/lean/.lake/build/bin/traffic_evidence_check .artifacts/work
node app/scripts/traffic-obstruction-correspondence.mjs formal/lean/.lake/build/bin/traffic_evidence_check .artifacts/obstruction
python3 scripts/check_formal.py --artifacts .artifacts/formal
python3 scripts/check_field_observations.py --lean-executable formal/lean/.lake/build/bin/traffic_evidence_check --artifacts .artifacts/field --parts /tmp/part0.csv /tmp/part1.csv /tmp/part2.csv
```

The ordinary formal gate runs synthetic observation controls offline. Full field
execution is separately opt-in, requires the exact pinned source parts, and
records all source, executable, input and output hashes. Omitting `--parts`
records observed data as `not_run`; a passed synthetic control is never reported
as real-data validation. Receipts reject source changes during execution.

The PR #46 reference's default numerical summary remains unchanged. Its export
hook supplies actual transition objects for independent Lean checks of local
work accounting, policy premises, cumulative counts, focal deadlines and drain
states. Open traces retain their admission scope; closed traces run real empty
continuation steps through the full certified evacuation horizon.

## Remaining boundaries

The event kernel and controller are specified mathematical models. Finite
production correspondence does not prove the entire JavaScript simulator
refines them, particularly for unrestricted re-routing history, box behavior,
breakdowns, TRAIN relays, or legacy immediate refill. The default simulator
has not been silently changed to satisfy the stronger rules.

The old rank-based waiting recurrence now receives a derived joint service cap
under the productive DAG and enforced-budget conditions above; those conditions
have not been established for unrestricted legacy production runs or field data.
The shared-work bound gives the sharper deadline in that scope. A universal sealed
subregion projection still needs a boundary/identity mapping and proof of its
closure. The saturated binary-merge schedule remains finite reference evidence
through depth 12, not an infinite schedule induction. These are stated limits,
not assumptions extracted from the measured crossings.

The work is local and reviewable. No remote branch, pull request, deployment,
or publication is part of this increment.
