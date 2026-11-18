import BML.Torus
import BML.Transport

/-!
Persistent blocking cores and finite capture in the classic BML kernel.

The mixed-winding capture mechanism is prior art: Angel--Holroyd--Martin,
Theorem 2.  This module uses explicit successor closure and route witnesses;
it does not assume a rank decrease in place of proving transport behavior.
-/
namespace BML

section General

variable {α : Type} {east north : Direction α} {s : Config α}

/-- An occupied set whose cars all point to another site in the set. -/
structure BlockingCore (east north : Direction α) (s : Config α) where
  sites : α → Prop
  occupied : ∀ p, sites p → s p ≠ .empty
  east_closed : ∀ p, sites p → s p = .east → sites (east.next p)
  north_closed : ∀ p, sites p → s p = .north → sites (north.next p)

def BlockingCore.Agrees (core : BlockingCore east north s) (u : Config α) : Prop :=
  ∀ p, core.sites p → u p = s p

theorem halfStep_agrees_on_core (d : Direction α) (sp : Species)
    (s u : Config α) (K : α → Prop)
    (hocc : ∀ p, K p → s p ≠ .empty)
    (hclosed : ∀ p, K p → s p = sp.cell → K (d.next p))
    (hagree : ∀ p, K p → u p = s p) :
    ∀ p, K p → halfStep d sp u p = s p := by
  intro p hp
  by_cases hc : s p = sp.cell
  · have hn := hclosed p hp hc
    have hne : u (d.next p) ≠ .empty := by
      rw [hagree _ hn]
      exact hocc _ hn
    simp [halfStep, hagree p hp, hc, hne]
  · simp [halfStep, hagree p hp, hc, hocc p hp]

theorem BlockingCore.east_agrees (core : BlockingCore east north s)
    (u : Config α) (h : core.Agrees u) :
    core.Agrees (halfStep east .east u) :=
  halfStep_agrees_on_core east .east s u core.sites core.occupied core.east_closed h

theorem BlockingCore.step_agrees (core : BlockingCore east north s)
    (u : Config α) (h : core.Agrees u) : core.Agrees (step east north u) := by
  exact halfStep_agrees_on_core north .north s _ core.sites core.occupied
    core.north_closed (core.east_agrees u h)

/-- The actual two-phase kernel preserves every car in a successor-closed core. -/
theorem BlockingCore.persists (core : BlockingCore east north s) (t : Nat) :
    core.Agrees (iterate (step east north) t s) := by
  induction t with
  | zero => intro p _; rfl
  | succ t ih => exact core.step_agrees _ ih

/-- A finite directed closed walk, given as a cyclic list; repeated sites are allowed. -/
structure BlockerCycle (east north : Direction α) (s : Config α) where
  length : Nat
  positive : 0 < length
  site : Fin length → α
  occupied : ∀ i, s (site i) ≠ .empty
  east_next : ∀ i, s (site i) = .east →
    east.next (site i) = site (cyclicNext length positive i)
  north_next : ∀ i, s (site i) = .north →
    north.next (site i) = site (cyclicNext length positive i)

def BlockerCycle.core (cycle : BlockerCycle east north s) : BlockingCore east north s where
  sites p := ∃ i, cycle.site i = p
  occupied p hp := by
    obtain ⟨i, rfl⟩ := hp
    exact cycle.occupied i
  east_closed p hp he := by
    obtain ⟨i, rfl⟩ := hp
    exact ⟨cyclicNext _ cycle.positive i, (cycle.east_next i he).symm⟩
  north_closed p hp hn := by
    obtain ⟨i, rfl⟩ := hp
    exact ⟨cyclicNext _ cycle.positive i, (cycle.north_next i hn).symm⟩

theorem BlockerCycle.persists (cycle : BlockerCycle east north s)
    (t : Nat) (i : Fin cycle.length) :
    iterate (step east north) t s (cycle.site i) = s (cycle.site i) :=
  cycle.core.persists t _ ⟨i, rfl⟩

/-- Follow a tagged car through a complete east-then-north round. -/
def roundTransport (east north : Direction α) (sp : Species)
    (s : Config α) (p : α) : α :=
  match sp with
  | .east => transport east .east s p
  | .north => transport north .north (halfStep east .east s) p

def RoundCanMove (east north : Direction α) (sp : Species)
    (s : Config α) (p : α) : Prop :=
  match sp with
  | .east => CanMove east .east s p
  | .north => CanMove north .north (halfStep east .east s) p

instance (east north : Direction α) (sp : Species) (s : Config α) (p : α) :
    Decidable (RoundCanMove east north sp s p) := by
  cases sp <;> unfold RoundCanMove <;> infer_instance

theorem roundTransport_preserves_car (east north : Direction α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    step east north s (roundTransport east north sp s p) = sp.cell := by
  cases sp with
  | east =>
    apply (other_species_unchanged north .north _ _ .east (by decide) (by decide)).mpr
    exact transport_preserves_car east .east s p hp
  | north =>
    apply transport_preserves_car north .north _ p
    exact (other_species_unchanged east .east s p .north (by decide) (by decide)).mpr hp

theorem roundTransport_surjective_on_cars (east north : Direction α) (sp : Species)
    (s : Config α) (q : α) (hq : step east north s q = sp.cell) :
    ∃ p, s p = sp.cell ∧ roundTransport east north sp s p = q := by
  cases sp with
  | east =>
    have hbefore := (other_species_unchanged north .north _ q .east
      (by decide) (by decide)).mp hq
    exact transport_surjective_on_cars east .east s q hbefore
  | north =>
    obtain ⟨p, hp, htransport⟩ := transport_surjective_on_cars north .north _ q hq
    refine ⟨p, ?_, htransport⟩
    exact (other_species_unchanged east .east s p .north
      (by decide) (by decide)).mp hp

theorem roundTransport_injective_on_cars (east north : Direction α) (sp : Species)
    (s : Config α) (p q : α) (hp : s p = sp.cell) (hq : s q = sp.cell)
    (heq : roundTransport east north sp s p = roundTransport east north sp s q) : p = q := by
  cases sp with
  | east => exact transport_injective_on_cars east .east s p q hp hq heq
  | north =>
    have hp' := (other_species_unchanged east .east s p .north (by decide) (by decide)).mpr hp
    have hq' := (other_species_unchanged east .east s q .north (by decide) (by decide)).mpr hq
    exact transport_injective_on_cars north .north _ p q hp' hq' heq

def carTrace (east north : Direction α) (sp : Species) (s : Config α) :
    Nat → α → α
  | 0, p => p
  | t+1, p => roundTransport east north sp (iterate (step east north) t s)
      (carTrace east north sp s t p)

theorem carTrace_preserves_car (east north : Direction α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) (t : Nat) :
    iterate (step east north) t s (carTrace east north sp s t p) = sp.cell := by
  induction t with
  | zero => exact hp
  | succ t ih => exact roundTransport_preserves_car east north sp _ _ ih

theorem carTrace_surjective_on_cars (east north : Direction α) (sp : Species)
    (s : Config α) (t : Nat) (q : α)
    (hq : iterate (step east north) t s q = sp.cell) :
    ∃ p, s p = sp.cell ∧ carTrace east north sp s t p = q := by
  induction t generalizing q with
  | zero => exact ⟨q, hq, rfl⟩
  | succ t ih =>
    obtain ⟨r, hr, hmove⟩ := roundTransport_surjective_on_cars east north sp _ q hq
    obtain ⟨p, hp, htrace⟩ := ih r hr
    exact ⟨p, hp, by simp only [carTrace, htrace]; exact hmove⟩

theorem carTrace_injective_on_cars (east north : Direction α) (sp : Species)
    (s : Config α) (t : Nat) (p q : α) (hp : s p = sp.cell) (hq : s q = sp.cell)
    (heq : carTrace east north sp s t p = carTrace east north sp s t q) : p = q := by
  induction t generalizing p q with
  | zero => exact heq
  | succ t ih =>
    have hprev := roundTransport_injective_on_cars east north sp _
      (carTrace east north sp s t p) (carTrace east north sp s t q)
      (carTrace_preserves_car east north sp s p hp t)
      (carTrace_preserves_car east north sp s q hq t) heq
    exact ih p q hp hq hprev

/-- Original tags and current species-car sites are in bijection at every round. -/
theorem carTrace_bijection (east north : Direction α) (sp : Species)
    (s : Config α) (t : Nat) :
    (∀ p, s p = sp.cell →
      iterate (step east north) t s (carTrace east north sp s t p) = sp.cell) ∧
    (∀ p q, s p = sp.cell → s q = sp.cell →
      carTrace east north sp s t p = carTrace east north sp s t q → p = q) ∧
    (∀ q, iterate (step east north) t s q = sp.cell →
      ∃ p, s p = sp.cell ∧ carTrace east north sp s t p = q) := by
  exact ⟨fun p hp => carTrace_preserves_car east north sp s p hp t,
    carTrace_injective_on_cars east north sp s t,
    carTrace_surjective_on_cars east north sp s t⟩

theorem BlockingCore.no_round_move (core : BlockingCore east north s)
    (u : Config α) (h : core.Agrees u) (sp : Species) (p : α)
    (hp : core.sites p) : ¬ RoundCanMove east north sp u p := by
  cases sp with
  | east =>
    intro hm
    have hc : s p = .east := by rw [← h p hp]; exact hm.1
    have hn := core.east_closed p hp hc
    have ho := core.occupied _ hn
    rw [← h _ hn] at ho
    exact ho hm.2
  | north =>
    intro hm
    have he := core.east_agrees u h
    have hc : s p = .north := by rw [← he p hp]; exact hm.1
    have hn := core.north_closed p hp hc
    have ho := core.occupied _ hn
    rw [← he _ hn] at ho
    exact ho hm.2

end General

/-- Explicit permanent obstacles on every horizontal and vertical route.
The geometric obligation is membership in the already proved persistent core. -/
structure RouteCover (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) where
  core : BlockingCore (eastDirection w h hw) (northDirection w h hh) s
  eastObstacle : Fin h → Fin w
  northObstacle : Fin w → Fin h
  east_mem : ∀ y, core.sites (eastObstacle y, y)
  north_mem : ∀ x, core.sites (x, northObstacle x)

variable {w h : Nat} {hw : 0 < w} {hh : 0 < h} {s : Config (Position w h)}

/-- Forward cyclic distance to a chosen obstacle, with zero at the obstacle. -/
def cyclicDistance (n : Nat) (x target : Fin n) : Nat :=
  if x.val ≤ target.val then target.val - x.val else n + target.val - x.val

theorem cyclicDistance_le (n : Nat) (x target : Fin n) :
    cyclicDistance n x target ≤ n - 1 := by
  have hx := x.isLt
  have ht := target.isLt
  unfold cyclicDistance
  split <;> omega

theorem cyclicDistance_next (n : Nat) (hn : 0 < n) (x target : Fin n)
    (hne : x ≠ target) :
    cyclicDistance n (cyclicNext n hn x) target + 1 = cyclicDistance n x target := by
  have hx := x.isLt
  have ht := target.isLt
  have hvals : x.val ≠ target.val := by
    intro he
    exact hne (Fin.ext he)
  simp only [cyclicDistance, cyclicNext]
  split <;> split <;> split <;> simp_all <;> omega

def RouteCover.distance (cover : RouteCover w h hw hh s) (sp : Species)
    (p : Position w h) : Nat :=
  match sp with
  | .east => cyclicDistance w p.1 (cover.eastObstacle p.2)
  | .north => cyclicDistance h p.2 (cover.northObstacle p.1)

def speciesRouteLength (w h : Nat) (sp : Species) : Nat :=
  match sp with
  | .east => w
  | .north => h

theorem RouteCover.distance_le (cover : RouteCover w h hw hh s) (sp : Species)
    (p : Position w h) : cover.distance sp p ≤ speciesRouteLength w h sp - 1 := by
  cases sp <;> apply cyclicDistance_le

/-- Each actual movement consumes exactly one unit of distance to a permanent obstacle. -/
theorem RouteCover.distance_roundTransport (cover : RouteCover w h hw hh s)
    (u : Config (Position w h)) (ha : cover.core.Agrees u) (sp : Species)
    (p : Position w h) :
    cover.distance sp (roundTransport (eastDirection w h hw) (northDirection w h hh) sp u p)
      + (if RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp u p then 1 else 0)
      = cover.distance sp p := by
  cases sp with
  | east =>
    by_cases hm : CanMove (eastDirection w h hw) .east u p
    · have hne : p.1 ≠ cover.eastObstacle p.2 := by
        intro he
        have hp : cover.core.sites p := by
          have hi := cover.east_mem p.2
          simpa only [← he] using hi
        exact cover.core.no_round_move u ha .east p hp hm
      simp only [roundTransport, transport, RoundCanMove, hm, ↓reduceIte]
      exact cyclicDistance_next w hw p.1 (cover.eastObstacle p.2) hne
    · simp [roundTransport, transport, hm, RoundCanMove]
  | north =>
    by_cases hm : CanMove (northDirection w h hh) .north (halfStep (eastDirection w h hw) .east u) p
    · have hne : p.2 ≠ cover.northObstacle p.1 := by
        intro he
        have hp : cover.core.sites p := by
          have hi := cover.north_mem p.1
          simpa only [← he] using hi
        exact cover.core.no_round_move u ha .north p hp hm
      simp only [roundTransport, transport, RoundCanMove, hm, ↓reduceIte]
      exact cyclicDistance_next h hh p.2 (cover.northObstacle p.1) hne
    · simp [roundTransport, transport, hm, RoundCanMove]

def RouteCover.carDistance (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) (p : Position w h) : Nat :=
  if s p = sp.cell then
    cover.distance sp (carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p)
  else 0

theorem RouteCover.carDistance_le (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) (p : Position w h) :
    cover.carDistance sp t p ≤
      (if s p = sp.cell then 1 else 0) * (speciesRouteLength w h sp - 1) := by
  unfold carDistance
  split
  · simpa using cover.distance_le sp
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p)
  · simp

theorem RouteCover.carDistance_mono (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) (p : Position w h) :
    cover.carDistance sp (t+1) p ≤ cover.carDistance sp t p := by
  unfold carDistance
  split
  · have hd := cover.distance_roundTransport
      (iterate (step (eastDirection w h hw) (northDirection w h hh)) t s)
      (cover.core.persists t) sp
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p)
    simp only [carTrace]
    omega
  · exact Nat.le_refl _

theorem RouteCover.carDistance_strict (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) (p : Position w h) (hp : s p = sp.cell)
    (hm : RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp
      (iterate (step (eastDirection w h hw) (northDirection w h hh)) t s)
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p)) :
    cover.carDistance sp (t+1) p < cover.carDistance sp t p := by
  have hd := cover.distance_roundTransport
    (iterate (step (eastDirection w h hw) (northDirection w h hh)) t s)
    (cover.core.persists t) sp
    (carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p)
  simp only [hm, ↓reduceIte] at hd
  simp only [carDistance, hp, ↓reduceIte, carTrace]
  omega

/-- Whether a specified original car moves in round `t`; empty and other-species tags contribute zero. -/
def RouteCover.carMoves (_cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) (p : Position w h) : Nat :=
  if s p = sp.cell then
    if RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp
      (iterate (torusStep w h hw hh) t s)
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p) then 1 else 0
  else 0

theorem RouteCover.carDistance_balance (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) (p : Position w h) :
    cover.carDistance sp (t+1) p + cover.carMoves sp t p = cover.carDistance sp t p := by
  by_cases hp : s p = sp.cell
  · simp only [carDistance, carMoves, hp, ↓reduceIte, carTrace, torusStep]
    exact cover.distance_roundTransport _ (cover.core.persists t) sp _
  · simp [carDistance, carMoves, hp]

theorem positions_contains (p : Position w h) : p ∈ positions w h := by
  apply List.mem_flatMap.mpr
  refine ⟨p.2, by simp, ?_⟩
  exact List.mem_map.mpr ⟨p.1, by simp, rfl⟩

theorem capture_sum_map_le {β : Type} (xs : List β) (f g : β → Nat)
    (hle : ∀ p ∈ xs, f p ≤ g p) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    have hp := hle p (by simp)
    have ht := ih (fun q hq => hle q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem capture_sum_map_lt {β : Type} (xs : List β) (f g : β → Nat)
    (hle : ∀ p ∈ xs, f p ≤ g p) (hlt : ∃ p ∈ xs, f p < g p) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => simp at hlt
  | cons p ps ih =>
    have hp := hle p (by simp)
    have hrest : ∀ q ∈ ps, f q ≤ g q := fun q hq => hle q (by simp [hq])
    obtain ⟨q, hq, hqstrict⟩ := hlt
    simp only [List.mem_cons] at hq
    simp only [List.map_cons, List.sum_cons]
    rcases hq with rfl | hq
    · have ht := capture_sum_map_le ps f g hrest
      omega
    · have ht := ih hrest ⟨q, hq, hqstrict⟩
      omega

theorem capture_sum_map_mul {β : Type} (xs : List β) (f : β → Nat) (m : Nat) :
    (xs.map fun p => f p * m).sum = (xs.map f).sum * m := by
  induction xs with
  | nil => simp
  | cons p ps ih => simp [ih, Nat.add_mul]

theorem capture_sum_map_add {β : Type} (xs : List β) (f g : β → Nat) :
    (xs.map fun p => f p + g p).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

def RouteCover.speciesRank (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) : Nat := ((positions w h).map (cover.carDistance sp t)).sum

def RouteCover.rank (cover : RouteCover w h hw hh s) (t : Nat) : Nat :=
  cover.speciesRank .east t + cover.speciesRank .north t

def RouteCover.speciesMoves (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) : Nat := ((positions w h).map (cover.carMoves sp t)).sum

/-- Aggregate actual moves counted through the original-car bijection. -/
def RouteCover.taggedMoves (cover : RouteCover w h hw hh s) (t : Nat) : Nat :=
  cover.speciesMoves .east t + cover.speciesMoves .north t

def RouteCover.movesThrough (cover : RouteCover w h hw hh s) : Nat → Nat
  | 0 => 0
  | t+1 => cover.movesThrough t + cover.taggedMoves t

def movementBudget (w h : Nat) (s : Config (Position w h)) : Nat :=
  speciesCount w h .east s * (w - 1) + speciesCount w h .north s * (h - 1)

theorem RouteCover.speciesRank_le (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) :
    cover.speciesRank sp t ≤ speciesCount w h sp s * (speciesRouteLength w h sp - 1) := by
  have hm := capture_sum_map_le (positions w h) (cover.carDistance sp t)
    (fun p => (if s p = sp.cell then 1 else 0) * (speciesRouteLength w h sp - 1))
    (fun p _ => cover.carDistance_le sp t p)
  rw [capture_sum_map_mul] at hm
  exact hm

theorem RouteCover.rank_le_budget (cover : RouteCover w h hw hh s) (t : Nat) :
    cover.rank t ≤ movementBudget w h s := by
  have he := cover.speciesRank_le .east t
  have hn := cover.speciesRank_le .north t
  unfold rank movementBudget
  exact Nat.add_le_add he hn

theorem RouteCover.speciesRank_balance (cover : RouteCover w h hw hh s)
    (sp : Species) (t : Nat) :
    cover.speciesRank sp (t+1) + cover.speciesMoves sp t = cover.speciesRank sp t := by
  have heq : (fun p => cover.carDistance sp (t+1) p + cover.carMoves sp t p) =
      cover.carDistance sp t := by
    funext p
    exact cover.carDistance_balance sp t p
  have hs := congrArg (fun f : Position w h → Nat => ((positions w h).map f).sum) heq
  rw [capture_sum_map_add] at hs
  exact hs

theorem RouteCover.rank_balance (cover : RouteCover w h hw hh s) (t : Nat) :
    cover.rank (t+1) + cover.taggedMoves t = cover.rank t := by
  have he := cover.speciesRank_balance .east t
  have hn := cover.speciesRank_balance .north t
  unfold rank taggedMoves
  omega

theorem RouteCover.rank_movesThrough (cover : RouteCover w h hw hh s) (t : Nat) :
    cover.rank t + cover.movesThrough t = cover.rank 0 := by
  induction t with
  | zero => simp [movesThrough]
  | succ t ih =>
    have hb := cover.rank_balance t
    simp only [movesThrough]
    omega

/-- Every finite prefix of actual tagged movement is bounded by the initial species-count budget. -/
theorem RouteCover.total_moves_le (cover : RouteCover w h hw hh s) (t : Nat) :
    cover.movesThrough t ≤ movementBudget w h s := by
  have hb := cover.rank_movesThrough t
  have hr := cover.rank_le_budget 0
  omega

theorem RouteCover.speciesRank_mono (cover : RouteCover w h hw hh s) (sp : Species)
    (t : Nat) : cover.speciesRank sp (t+1) ≤ cover.speciesRank sp t :=
  capture_sum_map_le (positions w h) _ _ (fun p _ => cover.carDistance_mono sp t p)

theorem roundCanMove_source_car (east north : Direction β) (sp : Species)
    (u : Config β) (p : β) (hm : RoundCanMove east north sp u p) : u p = sp.cell := by
  cases sp with
  | east => exact hm.1
  | north =>
    exact (other_species_unchanged east .east u p .north (by decide) (by decide)).mp hm.1

theorem exists_round_mover_of_not_frozen (east north : Direction β) (u : Config β)
    (hn : ¬ Frozen east north u) : ∃ sp p, RoundCanMove east north sp u p := by
  classical
  apply Classical.byContradiction
  intro hem
  apply hn
  apply (noMoves_iff_frozen east north u).mp
  constructor
  · intro p hm
    exact hem ⟨.east, p, hm⟩
  · intro p hm
    exact hem ⟨.north, p, hm⟩

/-- Strict decrease is derived from an actual eligible source and transport surjectivity. -/
theorem RouteCover.rank_strict_of_not_frozen (cover : RouteCover w h hw hh s)
    (t : Nat) (hn : ¬ Frozen (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s)) : cover.rank (t+1) < cover.rank t := by
  obtain ⟨sp, q, hm⟩ := exists_round_mover_of_not_frozen _ _ _ hn
  have hq := roundCanMove_source_car _ _ sp _ q hm
  obtain ⟨p, hp, htrace⟩ := carTrace_surjective_on_cars
    (eastDirection w h hw) (northDirection w h hh) sp s t q hq
  have hstrict := cover.carDistance_strict sp t p hp (by simpa only [torusStep, htrace] using hm)
  have hs := capture_sum_map_lt (positions w h)
    (cover.carDistance sp (t+1)) (cover.carDistance sp t)
    (fun p _ => cover.carDistance_mono sp t p)
    ⟨p, positions_contains p, hstrict⟩
  have he := cover.speciesRank_mono .east t
  have hno := cover.speciesRank_mono .north t
  change cover.speciesRank sp (t+1) < cover.speciesRank sp t at hs
  unfold rank
  cases sp <;> omega

theorem exists_within_decreasing_rank (P : Nat → Prop) (r : Nat → Nat)
    (hdecrease : ∀ t, ¬ P t → r (t+1) < r t) : ∃ t, t ≤ r 0 ∧ P t := by
  classical
  apply Classical.byContradiction
  intro hex
  have hnot : ∀ t, t ≤ r 0 → ¬ P t := by
    intro t ht hp
    exact hex ⟨t, ht, hp⟩
  have hbound : ∀ t, t ≤ r 0 + 1 → r t + t ≤ r 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hp : t ≤ r 0 := by omega
      have hi := ih (by omega)
      have hd := hdecrease t (hnot t hp)
      omega
  have hbad := hbound (r 0 + 1) (by omega)
  omega

/-- Universal classic-kernel capture from explicit route-cover witnesses. -/
theorem RouteCover.frozen_within_budget (cover : RouteCover w h hw hh s) :
    ∃ t, t ≤ movementBudget w h s ∧
      Frozen (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s) := by
  obtain ⟨t, ht, hf⟩ := exists_within_decreasing_rank
    (fun t => Frozen (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s)) cover.rank cover.rank_strict_of_not_frozen
  exact ⟨t, Nat.le_trans ht (cover.rank_le_budget 0), hf⟩

theorem RouteCover.nonempty (cover : RouteCover w h hw hh s) : Nonempty s := by
  let y : Fin h := ⟨0, hh⟩
  exact ⟨(cover.eastObstacle y, y), cover.core.occupied _ (cover.east_mem y)⟩

/-- The explicit movement budget also bounds the number of full rounds to a nonempty jam. -/
theorem RouteCover.jammed_by_movementBudget (cover : RouteCover w h hw hh s) :
    Jam (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) (movementBudget w h s) s) := by
  obtain ⟨t, ht, hf⟩ := cover.frozen_within_budget
  have hp := reached_frozen_persists (eastDirection w h hw) (northDirection w h hh)
    s t hf (movementBudget w h s - t)
  rw [Nat.add_sub_of_le ht] at hp
  constructor
  · exact (iterate_nonempty_iff (eastDirection w h hw) (northDirection w h hh)
      s (movementBudget w h s)).mpr cover.nonempty
  · simpa only [torusStep, hp] using hf

end BML
