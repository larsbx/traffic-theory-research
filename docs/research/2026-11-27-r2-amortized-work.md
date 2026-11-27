# R2: shared work and replenished merge obstruction (2026-11-27)

Follow-up to [PR #44](https://github.com/larsbx/traffic-theory-research/pull/44) and [PR #45](https://github.com/larsbx/traffic-theory-research/pull/45). Main already has kernel-checked clock and merge results from #45; this increment does not modify their production simulator or formal gate.

**Status:** mathematical argument under the proposed protected-service policy, plus an executable independent reference replay. Not a Lean-verified production-transition theorem. The earlier unpublished policy, arrival and compression prototypes are not silently assumed to be present on main.

## Policy and scope

A healthy CLASSIC, no-box, single-hop, finite-tag reference policy: every stopped on-street half-step increases age, and a hop/exit/new admission resets age. At age >= L a tag is protected. Every start-vacant cell is owned by its oldest protected legal claimant (lower tag ID breaks ties); younger requests and admissions cannot take it. A protected tag must choose an owned eligible destination, or an eligible exit, whenever its eligible menu is nonempty. It may choose any such destination. Actual movement, not merely a request, is mandatory. No same-step refill of a start-occupied cell. Ordinary hesitation and random choices are unrestricted subject to those guards. Fixed arrival menus while a vehicle remains stationary, fixed signal law, no external interventions or active breakdowns. This is stronger than the baseline policy; the correspondence to production is open.

The previous unpublished analysis derives a local rank bound, a cell/arrival-specific bound, and an affine dependency compression: exclusive non-admitting links charge only a signal gap, while contested destinations may multiply a lower-rank bound by their distinct predecessor capacity. Those are conditional mathematical certificates, not results of this PR's production formal gate.

## Shared work

For an acyclic region containing all actual legal non-self hops, let h(c) be a positive integer height that strictly decreases on each legal hop. Every arrival menu must contain a non-self move or EXIT; otherwise a nonmoving sink invalidates the argument. Self-loops cannot be granted under CLASSIC. Set D = max h, Phi = sum of h over on-street tags in the region. Each actual hop/exit consumes >=1 unit and each admission injects <=D units. Cumulative movements M and admissions A satisfy
    Phi(t) + M(t) <= Phi(0) + D A(t).
This also counts a tag which exits and is admitted elsewhere in the same step as one movement and one admission.

Suppose a fixed focal tag remains at c. Its contribution h(c) cannot be spent. Let Q=L+P, where P bounds the gap to joint phase/signal eligibility for every fixed legal target (2G suffices for the present two-phase signal law and G>=1). Any Q consecutive steps of a nonempty waiting window contain a movement or an admission. Otherwise every present tag matures during the first L steps. A minimum-height occupied cell has a vacant lower-height legal destination or an exit. A protected owner of that vacancy remains stationary until service, so the next eligible checkpoint within P steps forces movement, contradiction. The owner need not be the minimum-height occupant; it is still in the region for a sealed witness.

With an enforced upper bound A on all admissions into the region in the certified horizon, there are at most Phi(0)-h(c)+(D+1)A events in a no-focal-movement window. Partition into that many plus one blocks of length Q. Therefore a focal next movement occurs at offset strictly less than

    Q * [Phi(0)-h(c)+(D+1)A+1].

The bound is prospective only if the admission cap is enforced independently; actual observed admissions give a retrospective conditional certificate. With A=0 this is O(N D Q). For a whole non-admitting DAG, a nonempty final state implies Phi>=1 throughout; Q*Phi(0) steps suffice for evacuation. A sealed downstream region can use A=0 even while external traffic circulates, provided the region is forward-closed for all legal hops, has no inbound links or admission sites except at the occupied focal root, and no external interventions. Outside cars cannot use a clear downstream witness because that would violate the closure assumption.

The proof does not extend to cycles simply by choosing a rank witness: height must decrease on every actual movement, not only the witness. The finite-work bound does not establish throughput or trip completion when admissions are continually replenished.

## Saturated binary merge obstruction

Use m consecutive binary merges, with a trunk c_0,...,c_m, an exclusive side feeder s_j -> c_j at each j=1,...,m, trunk edge c_(j-1)->c_j, and EXIT at c_m. All cells are initially occupied, with side tags having smaller IDs than trunk tags. L=0, G=1. The only route is forward. Refill empty side feeders from off-street tags at admissible checkpoints, never in a step whose start had the feeder occupied. The admission oracle is an adversarial allowed choice schedule, not a claimed seed of the production PRNG. The tag count and occupied road cells are both 2m+1.

In the abstract same-axis model, the terminal trunk exits at offsets 0,4,8,...; the terminal vacant cell is filled at offsets 2,6,10,..., alternately by side and trunk (side first). For a destination whose fill schedule starts at alpha with period p, alternate fills select the trunk at alpha+p, alpha+3p, ... . The predecessor's first refill occurs two steps after its first departure, so upstream fill starts at alpha+p+2 and has period 2p. This yields the first focal offset 4*2^m+2m-4 if the alternating refill invariant persists. The tie/age reasoning is that after the side is served its replacement is younger than the waiting trunk; after the trunk is served the side is already waiting while the trunk must be refilled. For the two-row unit-grid variant, vertical feeders and horizontal trunk use their respective parities, and exits use the arrival parity; sink departure period 3, first upstream trunk departure 4, period 6. The upstream start recurrence adds one previous period plus 2 and doubles the period, giving 3*2^m+2m-4. Full induction over all scheduling invariants remains a formal obligation; the replay checks every trunk departure against these schedules for m=1..12.

Thus the finite-work and replenished cases behave very differently. The formulas give a candidate exponential lower-bound family under the oracle, with exact finite evidence through depth 12. They are not a proof that the production stochastic admission mechanism realizes every infinite schedule. A general polynomial guarantee for the proposed policy with unrestricted replenishment would need to rule out these schedules, or change admission/service policy. A natural next experiment is enforceable admission epochs: open for a bounded quota, then close until a certified shared-work drain deadline.

## Reproduce

Run from the repository root:
    node app/scripts/r2-amortized-reference.mjs

The self-contained script checks both abstract horizontal and unit-grid-equivalent mixed-axis families through 12 merges, verifies each trunk departure, asserts collision freedom and departure vacancy, then disables admissions and checks work decrease, two-step event progress, focal bound and evacuation. It uses a reference scheduler, not app/src/sim.js. Local JavaScript execution of the exact replay function: 57,570 open frames, 32,854 schedule checks, 1,248 closed work checks. At m=12: horizontal first move 16,404, mixed-axis 12,308; closed first movement 72 and 70 respectively, work deadline 338, drain at 97 and 95 half-steps. No production workflow result is implied by these local results.

## Formal closure obligations

1. Refine actual production transitions (routing, priority, signal, admissions) to the protected-service premises or provide an explicit opt-in implementation; avoid equating PR #45's different service premises with this policy.
2. Kernel-check the shared-work telescoping inequality, finite block-event contradiction, sealed region closure, and evacuation corollary in the existing Lean proof bank.
3. Formalize the saturated merge schedule by induction, including admission feasibility, age/tie invariants, and geometric parity. Arithmetic alone does not establish the schedule.
4. Run exact-revision production correspondence and all existing gates before promoting this reference evidence to a production theorem. Keep the local uncompiled Lean drafts outside the accepted formal gate until they compile.
