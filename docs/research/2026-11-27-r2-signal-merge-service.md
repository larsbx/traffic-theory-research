# R2 service from signal timing and merge priority

PR #44 shows that a safe-cell rank does not bound waiting without
service. The Gridlock City rules supply a network activity bound under
quiescent occupancy and an individual bound from gaps between genuine
attempts. A vehicle's actual hop may use any legal option.

## Signal timing and network activity

At a half-step \(t\), a hop on axis \(a\) can be requested only when
\(t\bmod 2=a\). A junction destination also needs
\(\lfloor t/G\rfloor\bmod 2=a\), where \(G\) is the integer green
duration. The simultaneous predicate is periodic with period \(2G\).
Axis zero passes at residue zero. Axis one passes at the first odd
residue at or above \(G\), which lies in the second green. Hence every
window of \(2G\) half-steps contains a permitted slot for either axis.
An exit only needs its movement phase.

Suppose a nonempty CLASSIC snapshot has an empty greatest trap, the
box rule is off, all on-street vehicles can re-route, and dawdling and
breakdown stalls are absent. Assume occupancy can change only through hop or exit
events in the window. This excludes interventions and entries from
off-street tags during a silent prefix. There is a vehicle with at
least one currently clear option. Otherwise the entire on-street
population would be a trap. The resolver keeps its existing clear
commitment or chooses a clear turn or exit. If no movement occurs,
the occupancy remains fixed and re-routing retains the selected clear
option. At its next permitted phase the request is eligible. A ready
exit is granted, and a CLASSIC merge at a vacancy grants one eligible
request. Either way the network records a move within \(2G\) half-steps.

The closed simulator may admit off-street tags while the network is
otherwise silent. Start on a nonempty, fully ranked map with \(R\)
tags off-street, with the same CLASSIC and readiness premises and
without external interventions. A silent cycle must contain an
admission. If it contained none, the preceding argument would give
a hop or exit. Each already off-street tag can enter at most once
before the first hop or exit. The Lean admission bound therefore
gives network movement within \(2G(R+1)\) half-steps. In the replay,
one returning tag enters in half-step offset 6 and the first hop
occurs at offset 12 under \(G=6\).

This bound applies to a network-wide pause. The grant can go to a
different vehicle from the one whose clear option supplied the crossing.

## Individual service at a merge

A genuine attempt is a request that passed the phase, signal, stall
and dawdling gates and targets a pre-step vacancy or an exit. A blocked
request can increase the simulator's wait counter, while only a
genuine attempt participates in arbitration. At a vacant destination,
maximum wait age wins, with ties to the lower tag. A losing contender
adds one to its age. A winner entering the destination resets its
age. The proof takes off-street age to be zero and uses traces within
the integer wait counter's range.

Consider a window of \(W\) half-steps starting with the waiting car's
age at least \(W\). If a competitor defeats it, that winner's age starts
again at zero. The rival can add at most one per step, so it cannot
match the waiting car's age again within the window. This holds even
if subsequent competitions use different destinations. With \(N\)
tags there are only \(N-1\) other winners. Therefore \(N\) genuine
attempts in such a window suffice for the car to move.

Suppose each successive block of \(L\) half-steps contains a genuine
attempt if the tag is still waiting throughout that block. First
allow \(NL\) blocks to accumulate an age of at least \(NL\). In the
next \(N\) blocks, which last \(NL\) half-steps, a winning tag cannot
repeat. Thus the car moves within

\[
M L = N L(L+1), \qquad M=NL+N .
\]

The [Lean proofs](../../formal/lean/BML/RouteService.lean) cover the clock,
the maximum-priority selection rule and both merge deadlines. The
individual bound needs an attempt in each block. A target can be empty
at every odd step and occupied at every even step. A horizontal car
then gets no attempt despite recurring observed vacancy. The
simulator replay exhibits that pattern with a one-step respawn delay.

## From safe-cell ranks to a tagged deadline

Let \(A\ge 1\) bound the delay from a clear legal option to a
genuine attempt, if the vehicle stays parked. Any legal attempt
suffices. Use the R2 premise that a departing vehicle leaves its
source vacant at the next checkpoint. Write
\(M_N(L)=NL(L+1)\) for the merge deadline.

The rank-zero witness is an exit, so a still-waiting vehicle gets
an attempt within \(A\) steps of each checkpoint. At a higher rank,
the chosen lower-rank cell is clear already or its current occupant
moves within its deadline. The next checkpoint supplies clearance.
Add \(A\) steps to reach a genuine attempt. Rank induction in Lean
gives a next-move bound for each window that fits in the accepted
horizon.

\[
D(0)=M_N(A),\qquad D(r+1)=M_N\bigl(D(r)+A\bigr).
\]

The recursion is a sufficient bound. Applying it to the current
simulator or a field trace requires evidence for the clearance
response \(A\). The signal period alone cannot supply that response
when vacancies occur only on the wrong phase.

## Partial re-routing and the remaining premise

In an ideal randomized policy, suppose a ready vehicle with a blocked
commitment and a free alternative revises with conditional probability
at least \(p\) at the first checkpoint of a quiet, trap-free window.
With the fixed occupancy and other conditions above, a successful
revision gives network activity within \(2G\) steps. The chance of
continued network silence through \(m\) successive cycles is at most
\((1-p)^m\) when the premises persist. The argument applies to a
model with this conditional revision law. Gridlock City's seeded stream
gives a deterministic replay for a supplied seed.

For individual waiting, assume that from every history of a parked
tag there is conditional probability at least \(\theta\) that the
next \(L\) steps contain an actual move or a genuine attempt. Apply
the bound to \(M=NL+N\) blocks. The probability that all blocks
give an attempt or the tag has already moved is at least
\(\theta^M\), by conditioning successively on their histories. A
tag waiting past all \(M\) successful blocks would violate the merge
theorem. The tail over \(m\) windows of length \(ML\) is therefore at
most \((1-\theta^M)^m\). This elementary probability corollary allows
dependent choices.

This replaces a joint *grant* assumption with a joint *attempt*
assumption, since the merge rule supplies the remaining service.
Establishing the attempt probability for a concrete phase plan,
turn policy and vacancy process remains open. A chance to revise on
its own covers the choice. A genuine attempt requires the vacancy
and legal phase to coincide. The [Lankershim field baseline](../../data/lankershim-field-replay/README.md)
will need independently aligned signal and occupancy observations
before it can test that premise.

## Executable checks

The [service replay](../../app/scripts/r2-service.mjs) uses the request
resolver shared with the production half-step. It checks the clock on
both axes, the event and counter updates of each observed contest,
and actual network activity windows on six presets under both no-box
laws with respawning delayed. A toy vertical route selected on red
is retained until its first permitted half-step. A two-tag merge
exercises the age reset and tie rule. The admission control delays
the first event by a full cycle. In the wrong-phase control the
follower sees 32 vacancies in 64 half-steps and makes no genuine attempt.

The formal gate compares those clock decisions and sampled
arbitration frames against Lean, and compares exact merge and rank
deadline arithmetic. These are finite implementation checks of the
identified rules and premises.
