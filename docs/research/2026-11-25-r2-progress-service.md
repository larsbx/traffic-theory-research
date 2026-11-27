# R2 waiting time under re-routing and service

PR #42 certifies the greatest structural trap and the least safe-cell set.
The empty trap alone puts no finite bound on waiting time, even on an
entirely ranked map. This note gives a conditional next-move theorem and
checks its premises against finite traces of Gridlock City.

## What can prevent progress

There is a one-cell trace with one parked car and an explicit exit.
The cell is rank zero and the greatest trap is empty at every checkpoint.
The trace can stay still indefinitely. In the simulator, a finite
breakdown can keep the car still through any selected interval within the
stall counter's range. Each observed snapshot remains trap-free.

A second example shows why a departed vehicle's cell must be visible as
vacant, even with service. On a two-cell corridor the front cell is an exit
and the entry for a returning vehicle. It has rank zero and its follower
has rank one. The front car exits every even half-step and immediately
respawns at the exit cell. The follower's target is occupied at every
start-of-step observation. The greatest trap stays empty, and the front
car records actual exits. The rear car waits forever. Both examples are
formalized in [Lean](../../formal/lean/BML/RouteProgress.lean).

Delaying the returning car by one half-step gives the follower a
visible vacancy every odd step. Its horizontal move is active on even
steps, when the front cell is occupied. The front car exits on even
steps and is admitted through the entry after the following odd step,
restoring the original occupancy. This repeating schedule satisfies
the departure vacancy premise and violates opportunity fairness.

## Conditional bounds

Use the checked R2 rank and the arrival menu for every on-street vehicle.
Assume CLASSIC vacancy and a single-cell destination or an exit for each
certified option. The vehicle keeps its position and arrival menu while
waiting. Require every recorded hop or exit to leave the source vacant at
the next checkpoint. Ordinary CLASSIC entry observes pre-step occupancy.
Same-step respawn into a departed vehicle's source must also be excluded
or separately accounted for.

A destination is **clear** when its cell is vacant before a half-step.
An exit is always clear in this occupancy sense. Clearance says nothing
by itself about the green phase, arbitration, driver hesitation or repair.
An observed **service cap** \(K \ge 1\) says that during a waiting interval
within the claimed horizon, a fixed legal option cannot be clear at \(K\)
distinct checkpoints without the vehicle recording a hop or exit. The
actual movement can use any of its options.

For a vehicle at rank \(r\), the next movement occurs at an offset strictly
less than \(B(r)\), in half-steps, provided the window of that length fits
inside the service horizon.

\[
B(0)=K,\qquad B(r+1)=K\bigl(B(r)+1\bigr).
\]

At rank zero the witness for the actual arrival is an exit. The service
condition gives a move in the first \(K\) half-steps. At rank \(r+1\), take an
exit or one lower-ranked destination from that arrival. Divide the waiting
window into \(K\) disjoint blocks of length \(B(r)+1\). If the witness is a
cell and starts a block occupied, its occupant moves within its lower rank
budget, at most \(B(r)\) half-steps. The source is then vacant at a
checkpoint still inside the block. A vacant initial cell or an exit gives
a checkpoint immediately. A vehicle that waited throughout the window
would therefore accumulate \(K\) clear checkpoints for a single option,
contradicting the service cap.

The qualitative theorem uses opportunity fairness in place of a cap.
If a waiting vehicle's legal option is clear arbitrarily late, the
vehicle eventually moves. Rank induction gives recurring vacancy for a
lower-ranked witness by applying the induction hypothesis to its
occupant at any later checkpoint. This excludes permanent fixation of a
ranked car under that fairness and the same vacancy premise. The result
concerns the next movement. A continuing queue can serve vehicles without
emptying, and general re-routing can send a vehicle to a higher rank.

## Partial re-routing

For a waiting vehicle and a fixed legal option, group successive
occupancy-clear checkpoints into groups of \(g\ge1\). Suppose that
conditional on the history at the start of the wait and just after each
completely unserved group, the chance of missing another full group
before any movement is at most \(1-p\) for some \(p>0\). This is a
bound on the joint service outcome. It can include blocks of adverse
signal phases and contention, as well as the driver's choice to revise.

The conditional probability multiplication rule gives a tail of
\((1-p)^m\) for missing \(m\) full groups. It allows dependent trials.
Across a horizon of \(H\) half-steps, at most \(N\) tags and \(D\)
destinations including the exit, there are at most \(HND\) possible
starting time, tag and destination triples. A violation of cap \(gm\)
contains \(m\) unserved groups for one such triple. The union bound gives
probability at most \(\min(1,HND(1-p)^m)\) of any such violation. With the vacancy
and rank premises in force, the same bound applies to any missed
rank deadline \(B(r)\) that fits in that horizon. On an infinite trace,
countably many starting checkpoints and tags, together with the same
conditional tail, give opportunity fairness almost surely.

This probabilistic corollary is a prose argument. The
[signal and merge follow-up](2026-11-27-r2-signal-merge-service.md) derives
deterministic service from bounded gaps between genuine attempts. It
also derives a conditional waiting tail from a joint probability of
getting an attempt. Deciding to re-route still gives no lower bound on
movement while signals or occupied cells can veto that decision.

## Executable controls

The [replay](../../app/scripts/r2-progress.mjs) uses the production
half-step and its actual movement event. It records missed clear
checkpoints for each legal arrival option during a single waiting
episode. One more than the largest missed count is a cap for that
observed trace. The replay checks vacancy after every departure in the
positive cases. It rejects the applicability of the bound on the
immediate-refill control even though that trace has cap two. The
one-half-step delay control records 32 observable vacancies and zero
follower movements in 64 half-steps.

The positive controls include a five-cell drainage corridor and a
192-half-step replay on each of the six presets under both no-box laws.
In the preset windows every initial vehicle starts on the street and exits
cannot respawn within the window. All 12 runs had windows long enough to
check the rank bound. The checker compares the recurrence in Lean and
JavaScript and tests the actual next movement in each of those windows.
These retrospectively measured caps apply to the specified finite runs.
Field use requires independently observing a departed cell's vacancy,
arrival-specific legal turns and actual service after clear checkpoints
at the relevant sampling cadence. The [Lankershim field baseline](../../data/lankershim-field-replay/README.md)
counts crossings at a virtual screenline. Its open stop-line and
controller-video alignment steps are needed before scoring
phase-specific service against that sample.
