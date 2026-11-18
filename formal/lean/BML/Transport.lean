import BML.Kernel

namespace BML

/-- Follow the identity of one car through its species' synchronous phase. -/
def transport (d : Direction α) (sp : Species) (s : Config α) (p : α) : α :=
  if CanMove d sp s p then d.next p else p

theorem transport_preserves_car (d : Direction α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    halfStep d sp s (transport d sp s p) = sp.cell := by
  unfold transport
  split
  · rename_i hm
    exact moving_destination_filled d sp s p hm
  · rename_i hm
    have hnext : s (d.next p) ≠ .empty := by
      intro he
      exact hm ⟨hp, he⟩
    simp [halfStep, hp, hnext]

/-- Two distinct cars cannot be transported to the same destination. -/
theorem transport_injective_on_cars (d : Direction α) (sp : Species)
    (s : Config α) (p q : α) (hp : s p = sp.cell) (hq : s q = sp.cell)
    (heq : transport d sp s p = transport d sp s q) : p = q := by
  by_cases hpm : CanMove d sp s p
  · by_cases hqm : CanMove d sp s q
    · have he : d.next p = d.next q := by simpa [transport, hpm, hqm] using heq
      have hi := congrArg d.prev he
      simpa [d.prev_next] using hi
    · have he : d.next p = q := by simpa [transport, hpm, hqm] using heq
      have he0 := hpm.2
      rw [he, hq] at he0
      exact False.elim (sp.cell_ne_empty he0)
  · by_cases hqm : CanMove d sp s q
    · have he : p = d.next q := by simpa [transport, hpm, hqm] using heq
      have he0 := hqm.2
      rw [← he, hp] at he0
      exact False.elim (sp.cell_ne_empty he0)
    · simpa [transport, hpm, hqm] using heq

/-- Every car after a phase has an original car as its unique source. -/
theorem transport_surjective_on_cars (d : Direction α) (sp : Species)
    (s : Config α) (q : α) (hq : halfStep d sp s q = sp.cell) :
    ∃ p, s p = sp.cell ∧ transport d sp s p = q := by
  by_cases hcar : s q = sp.cell
  · have hno : ¬ CanMove d sp s q := by
      intro hm
      have hz := moving_source_emptied d sp s q hm
      rw [hq] at hz
      exact sp.cell_ne_empty hz
    exact ⟨q, hcar, by simp [transport, hno]⟩
  · have hin : s q = .empty ∧ s (d.prev q) = sp.cell := by
      by_cases hn : s q = .empty ∧ s (d.prev q) = sp.cell
      · exact hn
      have hsame : halfStep d sp s q = s q := by simp [halfStep, hcar, hn]
      rw [hsame] at hq
      exact False.elim (hcar hq)
    have hm : CanMove d sp s (d.prev q) := by
      exact ⟨hin.2, by simpa [d.next_prev] using hin.1⟩
    exact ⟨d.prev q, hin.2, by simp [transport, hm, d.next_prev]⟩

/-- An explicit bijection of species-car sets; cardinality conservation follows on finite grids. -/
theorem transport_bijection (d : Direction α) (sp : Species) (s : Config α) :
    (∀ p, s p = sp.cell → halfStep d sp s (transport d sp s p) = sp.cell) ∧
    (∀ p q, s p = sp.cell → s q = sp.cell →
      transport d sp s p = transport d sp s q → p = q) ∧
    (∀ q, halfStep d sp s q = sp.cell →
      ∃ p, s p = sp.cell ∧ transport d sp s p = q) := by
  exact ⟨transport_preserves_car d sp s, transport_injective_on_cars d sp s,
    transport_surjective_on_cars d sp s⟩

theorem halfStep_nonempty_iff (d : Direction α) (sp : Species) (s : Config α) :
    Nonempty (halfStep d sp s) ↔ Nonempty s := by
  constructor
  · intro ⟨q, hq⟩
    by_cases hc : halfStep d sp s q = sp.cell
    · obtain ⟨p, hp, _⟩ := transport_surjective_on_cars d sp s q hc
      exact ⟨p, by rw [hp]; exact sp.cell_ne_empty⟩
    · have hs := (other_species_unchanged d sp s q (halfStep d sp s q) hq hc).mp rfl
      exact ⟨q, by rw [hs]; exact hq⟩
  · intro ⟨p, hp⟩
    by_cases hc : s p = sp.cell
    · exact ⟨transport d sp s p, by
        rw [transport_preserves_car d sp s p hc]
        exact sp.cell_ne_empty⟩
    · have hs := (other_species_unchanged d sp s p (s p) hp hc).mpr rfl
      exact ⟨p, by rw [hs]; exact hp⟩

theorem step_nonempty_iff (east north : Direction α) (s : Config α) :
    Nonempty (step east north s) ↔ Nonempty s := by
  simp only [step, halfStep_nonempty_iff]

theorem iterate_nonempty_iff (east north : Direction α) (s : Config α) (t : Nat) :
    Nonempty (iterate (step east north) t s) ↔ Nonempty s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate, step_nonempty_iff] using ih

end BML
