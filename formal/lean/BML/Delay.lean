import BML.Capture

/-!
# A queue obstruction to early permanent full movement

All statements use CLASSIC snapshot vacancy. An initial east run loses at
most one site from its front per complete round, whatever the exterior does.
The rear car therefore remains at its original site and blocked for the
specified number of rounds. Distinct sites are not needed for this kernel
argument; probability applications must separately arrange disjoint supports.
-/

namespace BML

/-- Consecutive east cars, starting at the rear coordinate `p`. -/
def eastRun (east : Direction α) (n : Nat) (p : α) (s : Config α) : Prop :=
  ∀ i, i < n → s (iterate east.next i p) = .east

theorem eastRun_mono (east : Direction α) (m n : Nat) (p : α) (s : Config α)
    (hmn : m ≤ n) (h : eastRun east n p s) : eastRun east m p s := by
  intro i hi
  exact h i (by omega)

theorem eastRun_head (east : Direction α) (n : Nat) (p : α) (s : Config α)
    (hn : 0 < n) (h : eastRun east n p s) : s p = .east :=
  h 0 hn

/-- The actual two-phase update preserves all but the front site of a run. -/
theorem eastRun_step (east north : Direction α) (n : Nat) (p : α) (s : Config α)
    (h : eastRun east (n + 1) p s) : eastRun east n p (step east north s) := by
  intro i hi
  have hp := h i (by omega)
  have hnext : s (east.next (iterate east.next i p)) = .east :=
    h (i + 1) (by omega)
  apply (other_species_unchanged north .north _ _ .east (by decide) (by decide)).mpr
  simp [halfStep, Species.cell, hp, hnext]

/-- A run of length `n+t` leaves its initial `n` sites occupied after `t` rounds. -/
theorem eastRun_iterate (east north : Direction α) (t n : Nat) (p : α) (s : Config α)
    (h : eastRun east (n + t) p s) :
    eastRun east n p (iterate (step east north) t s) := by
  induction t generalizing n with
  | zero => exact h
  | succ t ih =>
    have hstart : eastRun east ((n + 1) + t) p s := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 t] using h
    exact eastRun_step east north n p _ (ih (n + 1) hstart)

theorem eastRun_pair_blocked (east : Direction α) (p : α) (s : Config α)
    (h : eastRun east 2 p s) : s p = .east ∧ ¬ CanMove east .east s p := by
  have hp := h 0 (by decide)
  have hnext := h 1 (by decide)
  refine ⟨hp, ?_⟩
  intro hm
  have hf : Cell.east = .empty := hnext.symm.trans hm.2
  cases hf

/-- An initial `T+2` run keeps the rear car blocked in every round `t≤T`. -/
theorem eastRun_blocked_until (east north : Direction α) (T : Nat) (p : α)
    (s : Config α) (h : eastRun east (T + 2) p s) (t : Nat) (ht : t ≤ T) :
    iterate (step east north) t s p = .east ∧
      ¬ CanMove east .east (iterate (step east north) t s) p := by
  have hshort : eastRun east (2 + t) p s :=
    eastRun_mono east (2 + t) (T + 2) p s (by omega) h
  exact eastRun_pair_blocked east p _ (eastRun_iterate east north t 2 p s hshort)

/-- In particular, the run excludes full movement in the complete round `T`. -/
theorem eastRun_delay (east north : Direction α) (T : Nat) (p : α) (s : Config α)
    (h : eastRun east (T + 2) p s) :
    iterate (step east north) T s p = .east ∧
      ¬ CanMove east .east (iterate (step east north) T s) p :=
  eastRun_blocked_until east north T p s h T (Nat.le_refl T)

/-- The original rear identity stays at `p`, not merely some replacement car. -/
theorem eastRun_rear_trace (east north : Direction α) (T : Nat) (p : α) (s : Config α)
    (h : eastRun east (T + 2) p s) (t : Nat) (ht : t ≤ T + 1) :
    carTrace east north .east s t p = p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have htp : t ≤ T := by omega
    have htrace := ih (by omega)
    have hblocked := (eastRun_blocked_until east north T p s h t htp).2
    change transport east .east (iterate (step east north) t s)
      (carTrace east north .east s t p) = p
    rw [htrace]
    simp only [transport, ite_eq_right hblocked]

/-- Any permanent full-movement time must be strictly later than this delay. -/
theorem eastRun_settling_after (east north : Direction α) (T : Nat) (p : α)
    (s : Config α) (h : eastRun east (T + 2) p s) (U : Nat)
    (hfull : ∀ t, U ≤ t → ∀ q, iterate (step east north) t s q = .east →
      CanMove east .east (iterate (step east north) t s) q) : T < U := by
  have hb := eastRun_delay east north T p s h
  by_cases hUT : U ≤ T
  · exact False.elim (hb.2 (hfull T hUT p hb.1))
  · omega

theorem torus_eastRun_delay (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (T : Nat) (p : Position w h) (s : Config (Position w h))
    (hrun : eastRun (eastDirection w h hw) (T + 2) p s) :
    iterate (torusStep w h hw hh) T s p = .east ∧
      ¬ CanMove (eastDirection w h hw) .east (iterate (torusStep w h hw hh) T s) p :=
  eastRun_delay (eastDirection w h hw) (northDirection w h hh) T p s hrun

namespace DelayWitness

abbrev Pos := Position 4 4
abbrev east := eastDirection 4 4 (by decide)
abbrev north := northDirection 4 4 (by decide)
abbrev update := torusStep 4 4 (by decide) (by decide)

/-- Rows: `000E / 0ENN / 0E00 / NN0E`. -/
def before : Config Pos := decode 4 4 18626220

/-- The jammed staircase: `EN00 / 0EN0 / 00EN / N00E`. -/
def after : Config Pos := decode 4 4 15826840

def cutSite (i : Fin 8) : Pos :=
  match i.val with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 0)
  | 3 => (2, 3)
  | 4 => (2, 2)
  | 5 => (3, 2)
  | 6 => (0, 2)
  | _ => (0, 1)

def southeastNext (eastward : Bool) (p : Pos) : Pos :=
  if eastward then east.next p else north.prev p

def cutEastward (i : Fin 8) : Bool := decide (i.val % 4 < 2)

theorem cutSite_injective : ∀ i j : Fin 8, cutSite i = cutSite j → i = j := by
  decide

theorem cutSite_empty : ∀ i : Fin 8, before (cutSite i) = .empty := by
  decide

theorem cutSite_edge : ∀ i : Fin 8,
    southeastNext (cutEastward i) (cutSite i) = cutSite (cyclicNext 8 (by decide) i) := by
  decide

/-- Four east and four south edges give the displayed cut winding `(1,-1)`. -/
theorem cut_direction_counts :
    (List.finRange 8).countP cutEastward = 4 ∧
      (List.finRange 8).countP (fun i => !(cutEastward i)) = 4 := by
  decide

/-- A finite directed vacant east/south cycle; repeated vertices are allowed. -/
def HasVacantCycle (s : Config Pos) : Prop :=
  ∃ k, ∃ hk : 0 < k, ∃ site : Fin k → Pos,
    (∀ i, s (site i) = .empty) ∧
    ∀ i, ∃ eastward : Bool,
      southeastNext eastward (site i) = site (cyclicNext k hk i)

theorem before_has_vacant_cycle : HasVacantCycle before := by
  refine ⟨8, by decide, cutSite, cutSite_empty, ?_⟩
  exact fun i => ⟨cutEastward i, cutSite_edge i⟩

theorem before_to_after : update before = after := by
  funext p
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 4,
    update before (x, y) = after (x, y)) p.1 p.2

theorem after_fixed : update after = after := by
  funext p
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 4,
    update after (x, y) = after (x, y)) p.1 p.2

theorem after_is_jam : Jam east north after := by
  apply (jam_iff_nonempty_fixed east north after).mpr
  exact ⟨⟨(0, 0), by decide⟩, after_fixed⟩

theorem before_jams_in_one_round : Jam east north (update before) := by
  rw [before_to_after]
  exact after_is_jam

/-- In the next state no two successive east/south edges have all three
vertices vacant, so no directed vacant cycle of any length can survive. -/
theorem after_no_two_vacant_steps (p : Pos) (a b : Bool) :
    ¬ (after p = .empty ∧ after (southeastNext a p) = .empty ∧
      after (southeastNext b (southeastNext a p)) = .empty) := by
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 4, ∀ a b : Bool,
    ¬ (after (x, y) = .empty ∧ after (southeastNext a (x, y)) = .empty ∧
      after (southeastNext b (southeastNext a (x, y))) = .empty)) p.1 p.2 a b

theorem after_has_no_vacant_cycle : ¬ HasVacantCycle after := by
  rintro ⟨k, hk, site, hempty, hedge⟩
  let i : Fin k := ⟨0, hk⟩
  obtain ⟨a, ha⟩ := hedge i
  obtain ⟨b, hb⟩ := hedge (cyclicNext k hk i)
  apply after_no_two_vacant_steps (site i) a b
  refine ⟨hempty i, ?_, ?_⟩
  · rw [ha]
    exact hempty _
  · rw [ha, hb]
    exact hempty _

/-- An initially winding vacant cut can disappear while a genuine jam forms. -/
theorem vacant_cycle_does_not_prevent_jam :
    HasVacantCycle before ∧ ¬ HasVacantCycle (update before) ∧ Jam east north (update before) := by
  refine ⟨before_has_vacant_cycle, ?_, before_jams_in_one_round⟩
  rw [before_to_after]
  exact after_has_no_vacant_cycle

end DelayWitness

end BML
