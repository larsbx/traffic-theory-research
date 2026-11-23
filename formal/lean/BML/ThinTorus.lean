import BML.FiniteCycle
import BML.Fixation

/-!
On a one-row or one-column CLASSIC torus, a car on the singleton axis
never moves. It is an obstacle on the only cyclic lane of the other species.
A jammed orbit with an initial hole must have such an obstacle.
-/
namespace BML

private theorem stopped_by_coordinate_obstacle {α : Type}
    (east north : Direction α) (sp : Species) (s : Config α) (p : α)
    (hp : s p = sp.cell) {n : Nat} (hn : 0 < n) (coordinate : α → Fin n)
    (obstacle : Fin n)
    (advance : ∀ u q, RoundCanMove east north sp u q →
      coordinate (roundTransport east north sp u q) = cyclicNext n hn (coordinate q))
    (blocked : ∀ t, coordinate (carTrace east north sp s t p) = obstacle →
      ¬ RoundCanMove east north sp (iterate (step east north) t s)
        (carTrace east north sp s t p)) :
    TagEventuallyStopped east north sp s p := by
  let trace := fun t => carTrace east north sp s t p
  let orbit := fun t => iterate (step east north) t s
  let rank := fun t => cyclicDistance n (coordinate (trace t)) obstacle
  let moving := fun t => RoundCanMove east north sp (orbit t) (trace t)
  have balance (t : Nat) : rank (t+1) + (if moving t then 1 else 0) = rank t := by
    by_cases hm : moving t
    · have hnext : coordinate (trace (t+1)) = cyclicNext n hn (coordinate (trace t)) :=
        advance (orbit t) (trace t) hm
      have hne : coordinate (trace t) ≠ obstacle := fun h => blocked t h hm
      simpa only [rank, hnext, hm, ↓reduceIte] using
        cyclicDistance_next n hn (coordinate (trace t)) obstacle hne
    · have hstay : trace (t+1) = trace t :=
        roundTransport_eq_of_no_round_move east north sp (orbit t) (trace t) hm
      simp [rank, hstay, hm]
  obtain ⟨start, hstop⟩ := eventually_zero_cost rank (fun t => if moving t then 1 else 0) balance
  refine (tagEventuallyStopped_iff_finitely_many_moves east north sp s p hp).mpr ⟨start, ?_⟩
  intro t hm
  have hc : moving (start+t) := hm
  simpa [hc] using hstop t

private theorem cyclicNext_one (hn : 0 < 1) (p : Fin 1) : cyclicNext 1 hn p = p :=
  Subsingleton.elim _ _

private theorem blocked_by_self {α : Type} (d : Direction α) (sp : Species)
    (s : Config α) (p : α) (h : d.next p = p) : ¬ CanMove d sp s p := by
  intro hm
  exact sp.cell_ne_empty (hm.1.symm.trans (h ▸ hm.2))

theorem eventual_jam_of_north_on_single_row (w : Nat) (hw : 0 < w)
    (s : Config (Position w 1)) (q : Position w 1) (hq : s q = .north) :
    EventuallyJammed (eastDirection w 1 hw) (northDirection w 1 (by decide)) s := by
  let e := eastDirection w 1 hw
  let n := northDirection w 1 (by decide)
  have hfull : FullNorthColumn s q.1 := fun _ => by
    simpa only [Subsingleton.elim _ q.2] using hq
  apply eventuallyJammed_of_all_cars_stopped e n s _ ⟨q, by simp [hq]⟩
  intro sp p hp
  cases sp with
  | east =>
    apply stopped_by_coordinate_obstacle e n .east s p hp hw Prod.fst q.1
    · intro u r hm
      change CanMove e .east u r at hm
      simp only [roundTransport, transport, hm, ↓reduceIte]
      rfl
    · intro t hpos hm
      let r := carTrace e n .east s t p
      have hwall := fullNorthColumn_persists hw (by decide) s q.1 hfull t r.2
      have he : iterate (step e n) t s r = .east :=
        carTrace_preserves_car e n .east s p hp t
      have hpos' : r.1 = q.1 := hpos
      have hr : (q.1, r.2) = r := Prod.ext hpos'.symm rfl
      change iterate (step e n) t s (q.1, r.2) = .north at hwall
      rw [hr, he] at hwall
      cases hwall
  | north =>
    refine (tagEventuallyStopped_iff_finitely_many_moves e n .north s p hp).mpr ⟨0, ?_⟩
    intro t
    apply blocked_by_self
    exact Prod.ext rfl (cyclicNext_one _ _)

theorem eventual_jam_of_east_on_single_column (h : Nat) (hh : 0 < h)
    (s : Config (Position 1 h)) (q : Position 1 h) (hq : s q = .east) :
    EventuallyJammed (eastDirection 1 h (by decide)) (northDirection 1 h hh) s := by
  let e := eastDirection 1 h (by decide)
  let n := northDirection 1 h hh
  have hfull : FullEastRow s q.2 := fun _ => by
    simpa only [Subsingleton.elim _ q.1] using hq
  apply eventuallyJammed_of_all_cars_stopped e n s _ ⟨q, by simp [hq]⟩
  intro sp p hp
  cases sp with
  | east =>
    refine (tagEventuallyStopped_iff_finitely_many_moves e n .east s p hp).mpr ⟨0, ?_⟩
    intro t
    apply blocked_by_self
    exact Prod.ext (cyclicNext_one _ _) rfl
  | north =>
    apply stopped_by_coordinate_obstacle e n .north s p hp hh Prod.snd q.2
    · intro u r hm
      change CanMove n .north (halfStep e .east u) r at hm
      simp only [roundTransport, transport, hm, ↓reduceIte]
      rfl
    · intro t hpos hm
      let r := carTrace e n .north s t p
      have hwall := fullEastRow_persists (by decide) hh s q.2 hfull t r.1
      have hn' : iterate (step e n) t s r = .north :=
        carTrace_preserves_car e n .north s p hp t
      have hpos' : r.2 = q.2 := hpos
      have hr : (r.1, q.2) = r := Prod.ext rfl hpos'.symm
      change iterate (step e n) t s (r.1, q.2) = .east at hwall
      rw [hr, hn'] at hwall
      cases hwall

private theorem north_of_jamming_row_with_hole (w : Nat) (hw : 0 < w)
    (s : Config (Position w 1)) (hole : Position w 1) (hz : s hole = .empty)
    (hj : EventuallyJammed (eastDirection w 1 hw) (northDirection w 1 (by decide)) s) :
    ∃ q, s q = .north := by
  classical
  apply Classical.byContradiction
  intro hn
  obtain ⟨t, ht⟩ := hj
  obtain ⟨p, hp⟩ := (iterate_nonempty_iff _ _ s t).mp ht.1
  have he : s p = .east := by
    cases hc : s p with
    | empty => exact False.elim (hp hc)
    | east => rfl
    | north => exact False.elim (hn ⟨p, hc⟩)
  have hm : EastMixedRow w 1 s hole.2 :=
    ⟨fun q hq => hn ⟨q, hq⟩, ⟨p.1, by simpa only [Subsingleton.elim hole.2 p.2] using he⟩,
      ⟨hole.1, hz⟩⟩
  exact hm.never_jam w 1 hw (by decide) s hole.2 t ht

private theorem east_of_jamming_column_with_hole (h : Nat) (hh : 0 < h)
    (s : Config (Position 1 h)) (hole : Position 1 h) (hz : s hole = .empty)
    (hj : EventuallyJammed (eastDirection 1 h (by decide)) (northDirection 1 h hh) s) :
    ∃ q, s q = .east := by
  classical
  apply Classical.byContradiction
  intro he
  obtain ⟨t, ht⟩ := hj
  obtain ⟨p, hp⟩ := (iterate_nonempty_iff _ _ s t).mp ht.1
  have hn : s p = .north := by
    cases hc : s p with
    | empty => exact False.elim (hp hc)
    | east => exact False.elim (he ⟨p, hc⟩)
    | north => rfl
  have hm : NorthMixedColumn 1 h s hole.1 :=
    ⟨fun q hq => he ⟨q, hq⟩, ⟨p.2, by simpa only [Subsingleton.elim hole.1 p.1] using hn⟩,
      ⟨hole.2, hz⟩⟩
  exact hm.never_jam 1 h (by decide) hh s hole.1 t ht

/-- Filling one hole on a singleton side preserves eventual gridlock.
The proof permits any value at the modified hole. -/
theorem singleton_side_preserves_eventual_jam {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (hthin : w = 1 ∨ h = 1) {x y : Config (Position w h)} (p : Position w h)
    (hp : x p = .empty) (hsame : ∀ q, q ≠ p → y q = x q)
    (hx : EventuallyJammed (eastDirection w h hw) (northDirection w h hh) x) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) y := by
  rcases hthin with rfl | rfl
  · obtain ⟨q, hq⟩ := east_of_jamming_column_with_hole h hh x p hp hx
    have hne : q ≠ p := by rintro rfl; rw [hp] at hq; cases hq
    exact eventual_jam_of_east_on_single_column h hh y q ((hsame q hne).trans hq)
  · obtain ⟨q, hq⟩ := north_of_jamming_row_with_hole w hw x p hp hx
    have hne : q ≠ p := by rintro rfl; rw [hp] at hq; cases hq
    exact eventual_jam_of_north_on_single_row w hw y q ((hsame q hne).trans hq)

end BML
