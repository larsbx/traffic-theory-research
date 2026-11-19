import BML.Counting
import BML.FreeFlowConditions
import BML.Rigid
import BML.Encounters
import BML.FreeFlowNecessity

/-!
The CLASSIC free-flow characterization on every positive rectangular torus.
The static conditions imply actual movement in both successive phases and
are preserved by the resulting full round.
-/
namespace BML

/-- Decide CLASSIC full movement by enumerating the actual positions. -/
instance torusAllMoveDecidable (east north : Direction (Position w h))
    (s : Config (Position w h)) : Decidable (AllMove east north s) := by
  letI (P : Position w h → Prop) [DecidablePred P] : Decidable (∀ p, P p) :=
    decidable_of_iff (∀ p ∈ positions w h, P p)
      ⟨fun hp p => hp p (mem_positions w h p), fun hp p _ => hp p⟩
  unfold AllMove
  infer_instance

/-- Cyclic successor is injective on canonical residue representatives. -/
private theorem residue_succ_injective (g a b : Nat) (hg : 0 < g)
    (ha : a < g) (hb : b < g) (he : (a + 1) % g = (b + 1) % g) : a = b := by
  have hf : cyclicNext g hg ⟨a, ha⟩ = cyclicNext g hg ⟨b, hb⟩ := by
    apply Fin.ext
    simpa only [cyclicNext_val] using he
  have hi := congrArg (cyclicPrev g hg) hf
  have hab : (⟨a, ha⟩ : Fin g) = ⟨b, hb⟩ := by
    simpa only [cyclicPrev_next] using hi
  exact congrArg Fin.val hab

/-- The static adjacency and phase-class conditions make every car eligible,
with north eligibility evaluated after the east phase. -/
theorem staticFree_allMove (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    AllMove (eastDirection w h hw) (northDirection w h hh) s := by
  let E := eastDirection w h hw
  let N := northDirection w h hh
  have he : ∀ p, s p = .east → CanMove E .east s p := by
    intro p hp
    refine ⟨hp, ?_⟩
    cases hc : s (E.next p) with
    | empty => rfl
    | east => exact False.elim (hs.1 p hp hc)
    | north =>
        exact False.elim ((hs.2.2 p (E.next p) hp hc).2
          (phaseClass_east w h hw p))
  refine ⟨he, ?_⟩
  intro p hp
  have hn : s p = .north :=
    (other_species_unchanged E .east s p .north (by decide) (by decide)).mp hp
  refine ⟨hp, ?_⟩
  cases hc : halfStep E .east s (N.next p) with
  | empty => rfl
  | north =>
      have hnext : s (N.next p) = .north :=
        (other_species_unchanged E .east s (N.next p) .north
          (by decide) (by decide)).mp hc
      exact False.elim (hs.2.1 p hn hnext)
  | east =>
      have hsource : s (E.prev (N.next p)) = .east :=
        (halfStep_rigid E .east s he (N.next p)).mp hc
      exact False.elim ((hs.2.2 (E.prev (N.next p)) p hsource hn).1
        (phaseClass_eastPrev_northNext w h hw hh p).symm)

/-- A fully moving round preserves all three static free-flow conditions. -/
theorem staticFree_step (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    StaticFree w h hw hh (torusStep w h hw hh s) := by
  let E := eastDirection w h hw
  let N := northDirection w h hh
  have hm := staticFree_allMove w h hw hh s hs
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hnext
    have hsource := (allMove_step_east_iff E N s hm p).mp hp
    have htarget := (allMove_step_east_iff E N s hm (E.next p)).mp hnext
    apply hs.1 (E.prev p) hsource
    change s (E.next (E.prev p)) = .east
    rw [E.next_prev]
    simpa only [E.prev_next] using htarget
  · intro p hp hnext
    have hsource := (allMove_step_north_iff E N s hm p).mp hp
    have htarget := (allMove_step_north_iff E N s hm (N.next p)).mp hnext
    apply hs.2.1 (N.prev p) hsource
    change s (N.next (N.prev p)) = .north
    rw [N.next_prev]
    simpa only [N.prev_next] using htarget
  · intro e q he hn
    have he0 := (allMove_step_east_iff E N s hm e).mp he
    have hn0 := (allMove_step_north_iff E N s hm q).mp hn
    have hsep := hs.2.2 (E.prev e) (N.prev q) he0 hn0
    have hE : phaseClass w h e =
        (phaseClass w h (E.prev e) + 1) % Nat.gcd w h := by
      have ht := phaseClass_east w h hw (E.prev e)
      change phaseClass w h (E.next (E.prev e)) = _ at ht
      rw [E.next_prev] at ht
      exact ht
    have hN : phaseClass w h q =
        (phaseClass w h (N.prev q) + 1) % Nat.gcd w h := by
      have ht := phaseClass_north w h hh (N.prev q)
      change phaseClass w h (N.next (N.prev q)) = _ at ht
      rw [N.next_prev] at ht
      exact ht
    have hg : 0 < Nat.gcd w h := Nat.gcd_pos_of_pos_left h hw
    constructor
    · intro heq
      apply hsep.1
      apply residue_succ_injective (Nat.gcd w h) _ _ hg
        (phaseClass_lt w h hw (N.prev q)) (phaseClass_lt w h hw (E.prev e))
      rw [← hN, ← hE]
      exact heq
    · intro heq
      apply hsep.2
      apply residue_succ_injective (Nat.gcd w h) _ _ hg
        (phaseClass_lt w h hw (N.prev q)) (Nat.mod_lt _ hg)
      rw [← hN, heq, hE]

/-- The static condition is an invariant of the actual CLASSIC full step. -/
theorem staticFree_iterate (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) (t : Nat) :
    StaticFree w h hw hh (iterate (torusStep w h hw hh) t s) := by
  induction t with
  | zero => exact hs
  | succ t ih => exact staticFree_step w h hw hh _ ih

/-- Every static-free board has full movement at every natural time. -/
theorem staticFree_perpetual_allMove (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    ∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s) := by
  intro t
  exact staticFree_allMove w h hw hh _ (staticFree_iterate w h hw hh s hs t)

/-- Lemma R: the static conditions are equivalent to full movement in every
round of the actual CLASSIC orbit, starting at time zero. -/
theorem lemmaR (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    StaticFree w h hw hh s ↔
      ∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s) := by
  constructor
  · exact staticFree_perpetual_allMove w h hw hh s
  · intro hm
    exact staticFree_of_allMove_before_lcm w h hw hh s (fun t _ => hm t)

/-- Exactly one half-open lcm window of fully moving rounds suffices. -/
theorem lemmaR_finite_lt (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    (∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s)) ↔
    (∀ t, t < Nat.lcm w h →
      AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s)) := by
  constructor
  · exact fun hm t _ => hm t
  · intro hm
    exact (lemmaR w h hw hh s).mp (staticFree_of_allMove_before_lcm w h hw hh s hm)

/-- The inclusive time-window formulation from the proof blueprint. -/
theorem lemmaR_finite (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    (∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s)) ↔
    (∀ t, t ≤ Nat.lcm w h →
      AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s)) := by
  constructor
  · exact fun hm t _ => hm t
  · intro hm
    exact (lemmaR_finite_lt w h hw hh s).mpr (fun t ht => hm t (Nat.le_of_lt ht))

/-- Direct equivalence of the static predicate and its finite moving window. -/
theorem lemmaR_window (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    StaticFree w h hw hh s ↔
      ∀ t, t < Nat.lcm w h →
        AllMove (eastDirection w h hw) (northDirection w h hh)
          (iterate (torusStep w h hw hh) t s) :=
  (lemmaR w h hw hh s).trans (lemmaR_finite_lt w h hw hh s)

/-- Failing any static condition forces a blocked car within the first lcm
rounds; this is a finite witness of failure of perpetual free flow. -/
theorem not_staticFree_iff_blocked_before_lcm (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    ¬ StaticFree w h hw hh s ↔
      ∃ t, t < Nat.lcm w h ∧
        ¬ AllMove (eastDirection w h hw) (northDirection w h hh)
          (iterate (torusStep w h hw hh) t s) := by
  classical
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hmissing
    apply hn
    apply (lemmaR_window w h hw hh s).mpr
    intro t ht
    apply Classical.byContradiction
    intro hblocked
    exact hmissing ⟨t, ht, hblocked⟩
  · rintro ⟨t, ht, hblocked⟩ hs
    exact hblocked ((lemmaR_window w h hw hh s).mp hs t ht)

/-- A static-free configuration returns after lcm(W,H) full rounds. Its least
configuration period can be smaller, for example for the empty board. -/
theorem freeFlow_returns_lcm (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    iterate (torusStep w h hw hh) (Nat.lcm w h) s = s := by
  have hm := staticFree_perpetual_allMove w h hw hh s hs
  have hprefix : ∀ u < Nat.lcm w h,
      AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) u s) := fun u _ => hm u
  funext p
  have he := allMove_iterate_east_at (eastDirection w h hw) (northDirection w h hh)
    s (Nat.lcm w h) hprefix p
  have hn := allMove_iterate_north_at (eastDirection w h hw) (northDirection w h hh)
    s (Nat.lcm w h) hprefix p
  rw [iterate_east_lcm] at he
  rw [iterate_north_lcm] at hn
  change (iterate (torusStep w h hw hh) (Nat.lcm w h) s p = .east ↔ s p = .east) at he
  change (iterate (torusStep w h hw hh) (Nat.lcm w h) s p = .north ↔ s p = .north) at hn
  cases hfinal : iterate (torusStep w h hw hh) (Nat.lcm w h) s p <;>
    cases hinitial : s p <;> simp_all

/-- The lcm return propagates to every later time on a static-free orbit. -/
theorem freeFlow_periodic (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) (t : Nat) :
    iterate (torusStep w h hw hh) (t + Nat.lcm w h) s =
      iterate (torusStep w h hw hh) t s := by
  rw [Nat.add_comm t (Nat.lcm w h), iterate_add, freeFlow_returns_lcm w h hw hh s hs]

/-- Eventual permanent full movement is exactly eventual entry into the
static-free set. This gives no uniform bound on the entry time. -/
theorem eventually_allMove_iff_reaches_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    (∃ T, ∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) (T + t) s)) ↔
    (∃ T, StaticFree w h hw hh (iterate (torusStep w h hw hh) T s)) := by
  constructor
  · rintro ⟨T, hm⟩
    refine ⟨T, (lemmaR w h hw hh _).mpr ?_⟩
    intro t
    simpa only [iterate_add] using hm t
  · rintro ⟨T, hs⟩
    refine ⟨T, ?_⟩
    intro t
    simpa only [iterate_add] using (lemmaR w h hw hh _).mp hs t

end BML
