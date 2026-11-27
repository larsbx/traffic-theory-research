import BML.ThinRigidity

/-!
On a one-row or one-column CLASSIC torus, a car on the singleton axis
never moves. It is a full lane, hence an obstacle on the only cyclic lane of
the other species (`ThinRigidity`). A jammed orbit with an initial hole must
have such an obstacle.
-/
namespace BML

theorem eventual_jam_of_north_on_single_row (w : Nat) (hw : 0 < w)
    (s : Config (Position w 1)) (q : Position w 1) (hq : s q = .north) :
    EventuallyJammed (eastDirection w 1 hw) (northDirection w 1 (by decide)) s := by
  have hfull : ∀ p : Position w 1, s p = .north → FullNorthColumn s p.1 := fun p hp _ => by
    simpa only [Subsingleton.elim _ p.2] using hp
  exact eventuallyJammed_of_north_in_full_columns hw (by decide) s q.1 (hfull q hq) hfull

theorem eventual_jam_of_east_on_single_column (h : Nat) (hh : 0 < h)
    (s : Config (Position 1 h)) (q : Position 1 h) (hq : s q = .east) :
    EventuallyJammed (eastDirection 1 h (by decide)) (northDirection 1 h hh) s := by
  have hfull : ∀ p : Position 1 h, s p = .east → FullEastRow s p.2 := fun p hp _ => by
    simpa only [Subsingleton.elim _ p.1] using hp
  exact eventuallyJammed_of_east_in_full_rows (by decide) hh s q.2 (hfull q hq) hfull

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
