import BML.SparseEquality

/-!
Actual movement totals and the original-car blockage counts. The north count
uses the east intermediate board. All correspondence identities hold without
a sparsity hypothesis; the final bounds apply B7's per-car block budget.
-/
namespace BML

section

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

local notation "E" => eastDirection w h hw
local notation "N" => northDirection w h hh
local notation "orbit" => iterate (torusStep w h hw hh)

/-- Actual Eulerian movements in one complete CLASSIC east-then-north round. -/
def roundMoveCount (s : Config (Position w h)) : Nat :=
  moveCount w h E .east s + moveCount w h N .north (halfStep E .east s)

/-- Actual movements in the complete rounds [0,T). -/
def cumulativeMoveCount (s : Config (Position w h)) (T : Nat) : Nat :=
  ((List.range T).map fun t => roundMoveCount hw hh (orbit t s)).sum

/-- Missed car-rounds in [0,T), using the initial conserved population and
the actual two-phase movement counts. -/
def missedMoveCount (s : Config (Position w h)) (T : Nat) : Nat :=
  ((List.range T).map fun t => carCount w h s - roundMoveCount hw hh (orbit t s)).sum

/-- Sum the blockage counts of every original east and north car exactly once. -/
def totalTagBlockCount (s : Config (Position w h)) (T : Nat) : Nat :=
  ((speciesCells w h .east s).map fun p => blockedTagCount hw hh s .east p T).sum +
  ((speciesCells w h .north s).map fun p => blockedTagCount hw hh s .north p T).sum

private theorem sum_filter_map_indicator (xs : List α) (P : α → Prop)
    [DecidablePred P] (f : α → Nat) :
    ((xs.filter fun x => decide (P x)).map f).sum =
      (xs.map fun x => if P x then f x else 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : P x <;> simp [hp, ih]

private theorem indicator_complement_sum (xs : List α) (P : α → Prop)
    [DecidablePred P] :
    (xs.map (fun x => if P x then 1 else 0)).sum +
      (xs.map (fun x => if ¬ P x then 1 else 0)).sum = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : P x <;> simp [hp] at * <;> omega

/-- At every time the actual species sites are a permutation of the original
species sites transported along their identity-preserving traces. -/
theorem speciesCells_carTrace_perm (s : Config (Position w h)) (sp : Species) (t : Nat) :
    (speciesCells w h sp (orbit t s)).Perm
      ((speciesCells w h sp s).map (carTrace E N sp s t)) := by
  have hmap : ((speciesCells w h sp s).map (carTrace E N sp s t)).Nodup := by
    apply List.pairwise_map.mpr
    apply (speciesCells_nodup w h sp s).imp_of_mem
    intro p q hp hq hpq heq
    exact hpq (carTrace_injective_on_cars E N sp s t p q
      ((mem_speciesCells w h sp s p).mp hp) ((mem_speciesCells w h sp s q).mp hq) heq)
  apply (List.perm_ext_iff_of_nodup (speciesCells_nodup w h sp _) hmap).mpr
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, heq⟩ := carTrace_surjective_on_cars E N sp s t q
      ((mem_speciesCells w h sp _ q).mp hq)
    exact List.mem_map.mpr ⟨p, (mem_speciesCells w h sp s p).mpr hp, heq⟩
  · intro hq
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
    rw [← heq]
    apply (mem_speciesCells w h sp _ _).mpr
    exact carTrace_preserves_car E N sp s p ((mem_speciesCells w h sp s p).mp hp) t

private theorem species_round_moves (s : Config (Position w h)) (sp : Species) :
    ((speciesCells w h sp s).map
      fun p => if RoundCanMove E N sp s p then 1 else 0).sum =
    ((positions w h).map fun p => if RoundCanMove E N sp s p then 1 else 0).sum := by
  rw [speciesCells, sum_filter_map_indicator]
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases hp : s p = sp.cell
  · simp [hp]
  · have hn : ¬ RoundCanMove E N sp s p :=
      fun hm => hp (roundCanMove_source_car E N sp s p hm)
    simp [hp, hn]

private theorem species_round_moves_eq_traces (s : Config (Position w h))
    (sp : Species) (t : Nat) :
    ((speciesCells w h sp (orbit t s)).map
      fun p => if RoundCanMove E N sp (orbit t s) p then 1 else 0).sum =
    ((speciesCells w h sp s).map
      fun p => if TraceCanMove hw hh s sp p t then 1 else 0).sum := by
  simpa only [List.map_map, Function.comp_def, TraceCanMove] using
    ((speciesCells_carTrace_perm hw hh s sp t).map
      (fun p => if RoundCanMove E N sp (orbit t s) p then 1 else 0)).sum_nat

/-- Eulerian movement counts equal the number of moving original car tags.
In particular north eligibility is read after the actual east half-step. -/
theorem roundMoveCount_eq_traced_moves (s : Config (Position w h)) (t : Nat) :
    roundMoveCount hw hh (orbit t s) =
      ((speciesCells w h .east s).map
        fun p => if TraceCanMove hw hh s .east p t then 1 else 0).sum +
      ((speciesCells w h .north s).map
        fun p => if TraceCanMove hw hh s .north p t then 1 else 0).sum := by
  have he := species_round_moves hw hh (orbit t s) .east
  have hn := species_round_moves hw hh (orbit t s) .north
  have he' := he.symm.trans (species_round_moves_eq_traces hw hh s .east t)
  have hn' := hn.symm.trans (species_round_moves_eq_traces hw hh s .north t)
  simp only [RoundCanMove] at he' hn'
  unfold roundMoveCount moveCount
  rw [he', hn']

private theorem round_moves_add_tagged_blocks (s : Config (Position w h)) (t : Nat) :
    roundMoveCount hw hh (orbit t s) +
      (((speciesCells w h .east s).map
        fun p => if ¬ TraceCanMove hw hh s .east p t then 1 else 0).sum +
      ((speciesCells w h .north s).map
        fun p => if ¬ TraceCanMove hw hh s .north p t then 1 else 0).sum) =
      carCount w h s := by
  rw [roundMoveCount_eq_traced_moves, carCount_eq_speciesCount,
    speciesCount_eq_length_speciesCells, speciesCount_eq_length_speciesCells]
  have he := indicator_complement_sum (speciesCells w h .east s)
    (fun p => TraceCanMove hw hh s .east p t)
  have hn := indicator_complement_sum (speciesCells w h .north s)
    (fun p => TraceCanMove hw hh s .north p t)
  omega

/-- No round moves more than the conserved initial population. -/
theorem roundMoveCount_le_initial_population (s : Config (Position w h)) (t : Nat) :
    roundMoveCount hw hh (orbit t s) ≤ carCount w h s := by
  have hb := round_moves_add_tagged_blocks hw hh s t
  omega

/-- The total Eulerian movement deficit equals the sum of all original-car
blockage counts, for every board and every finite horizon. -/
theorem missedMoveCount_eq_tag_blocks (s : Config (Position w h)) (T : Nat) :
    missedMoveCount hw hh s T = totalTagBlockCount hw hh s T := by
  have hround (t : Nat) :
      carCount w h s - roundMoveCount hw hh (orbit t s) =
        ((speciesCells w h .east s).map
          fun p => if ¬ TraceCanMove hw hh s .east p t then 1 else 0).sum +
        ((speciesCells w h .north s).map
          fun p => if ¬ TraceCanMove hw hh s .north p t then 1 else 0).sum := by
    have hb := round_moves_add_tagged_blocks hw hh s t
    omega
  unfold missedMoveCount
  simp only [hround]
  rw [list_sum_map_add]
  unfold totalTagBlockCount
  congr 1
  · rw [list_sum_map_swap]
    simp only [blockedTagCount, length_filter_eq_indicator_sum]
  · rw [list_sum_map_swap]
    simp only [blockedTagCount, length_filter_eq_indicator_sum]

/-- Any uniform per-original-car blockage bound controls the actual total
missed movements. This correspondence theorem does not assume sparsity. -/
theorem missedMoveCount_le_of_tag_bounds (s : Config (Position w h)) (T K : Nat)
    (hbound : ∀ sp p, s p = sp.cell → blockedTagCount hw hh s sp p T ≤ K) :
    missedMoveCount hw hh s T ≤ carCount w h s * K := by
  rw [missedMoveCount_eq_tag_blocks]
  have hs (sp : Species) :
      ((speciesCells w h sp s).map fun p => blockedTagCount hw hh s sp p T).sum ≤
        (speciesCells w h sp s).length * K := by
    calc
      _ ≤ ((speciesCells w h sp s).map fun _ => K).sum :=
        list_sum_map_le _ _ _ (fun p hp => hbound sp p ((mem_speciesCells w h sp s p).mp hp))
      _ = _ := by simp [List.map_const', List.sum_replicate_nat]
  have he := hs .east
  have hn := hs .north
  simp only [totalTagBlockCount]
  rw [carCount_eq_speciesCount, speciesCount_eq_length_speciesCells,
    speciesCount_eq_length_speciesCells, Nat.add_mul]
  exact Nat.add_le_add he hn

/-- B7's strict sparse budget bounds missed car-rounds, not only rounds
containing at least one blockage. -/
theorem low_density_missed_move_bound (s : Config (Position w h))
    (hm : 2 * carCount w h s < Nat.gcd w h) (T : Nat) :
    missedMoveCount hw hh s T ≤ carCount w h s * (Nat.gcd w h - 2) :=
  missedMoveCount_le_of_tag_bounds hw hh s T (Nat.gcd w h - 2)
    (fun sp p hp => low_density_tag_block_bound hw hh s hm sp p hp T)

/-- The same cumulative missed-movement budget holds at the inclusive
population threshold 2m≤gcd(w,h). -/
theorem low_density_missed_move_bound_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ Nat.gcd w h) (T : Nat) :
    missedMoveCount hw hh s T ≤ carCount w h s * (Nat.gcd w h - 2) :=
  missedMoveCount_le_of_tag_bounds hw hh s T (Nat.gcd w h - 2)
    (fun sp p hp => low_density_tag_block_bound_le hw hh s hm sp p hp T)

/-- Actual movements and missed movements partition all m*T opportunities. -/
theorem cumulativeMoveCount_add_missedMoveCount (s : Config (Position w h)) (T : Nat) :
    cumulativeMoveCount hw hh s T + missedMoveCount hw hh s T = carCount w h s * T := by
  unfold cumulativeMoveCount missedMoveCount
  rw [← list_sum_map_add]
  have he (t : Nat) :
      roundMoveCount hw hh (orbit t s) +
        (carCount w h s - roundMoveCount hw hh (orbit t s)) = carCount w h s := by
    have hb := roundMoveCount_le_initial_population hw hh s t
    omega
  simp only [he]
  simp [List.map_const', List.sum_replicate_nat, Nat.mul_comm]

/-- Finite cumulative speed bounds with no division by a possibly zero
population or horizon. -/
theorem low_density_movement_bounds (s : Config (Position w h))
    (hm : 2 * carCount w h s < Nat.gcd w h) (T : Nat) :
    carCount w h s * T - carCount w h s * (Nat.gcd w h - 2) ≤
        cumulativeMoveCount hw hh s T ∧
      cumulativeMoveCount hw hh s T ≤ carCount w h s * T := by
  have hb := low_density_missed_move_bound hw hh s hm T
  have he := cumulativeMoveCount_add_missedMoveCount hw hh s T
  omega

/-- Finite Eulerian movement bounds including equality 2m=gcd(w,h). -/
theorem low_density_movement_bounds_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ Nat.gcd w h) (T : Nat) :
    carCount w h s * T - carCount w h s * (Nat.gcd w h - 2) ≤
        cumulativeMoveCount hw hh s T ∧
      cumulativeMoveCount hw hh s T ≤ carCount w h s * T := by
  have hb := low_density_missed_move_bound_le hw hh s hm T
  have he := cumulativeMoveCount_add_missedMoveCount hw hh s T
  omega

private theorem routeCover_speciesMoves_eq_traces (s : Config (Position w h))
    (cover : RouteCover w h hw hh s) (sp : Species) (t : Nat) :
    cover.speciesMoves sp t =
      ((speciesCells w h sp s).map
        fun p => if TraceCanMove hw hh s sp p t then 1 else 0).sum := by
  rw [speciesCells, sum_filter_map_indicator]
  rfl

/-- The persistent-core capture proof's tagged movement aggregate is the
actual Eulerian movement count of the same CLASSIC round. -/
theorem RouteCover.taggedMoves_eq_roundMoveCount (s : Config (Position w h))
    (cover : RouteCover w h hw hh s) (t : Nat) :
    cover.taggedMoves t = roundMoveCount hw hh (orbit t s) := by
  rw [RouteCover.taggedMoves, routeCover_speciesMoves_eq_traces,
    routeCover_speciesMoves_eq_traces, roundMoveCount_eq_traced_moves]

/-- The capture proof's complete tagged movement history agrees with the
sum of actual two-phase movement counts at every horizon. -/
theorem RouteCover.movesThrough_eq_cumulativeMoveCount (s : Config (Position w h))
    (cover : RouteCover w h hw hh s) (T : Nat) :
    cover.movesThrough T = cumulativeMoveCount hw hh s T := by
  induction T with
  | zero => simp [RouteCover.movesThrough, cumulativeMoveCount]
  | succ T ih =>
    rw [RouteCover.movesThrough, ih,
      RouteCover.taggedMoves_eq_roundMoveCount hw hh s cover T]
    simp [cumulativeMoveCount, List.range_succ, List.map_append, List.sum_append]

/-- The route-cover movement budget also bounds the executable Eulerian
movement total, without a separate implementation-counting assumption. -/
theorem RouteCover.cumulativeMoveCount_le_budget (s : Config (Position w h))
    (cover : RouteCover w h hw hh s) (T : Nat) :
    cumulativeMoveCount hw hh s T ≤ movementBudget w h s := by
  rw [← RouteCover.movesThrough_eq_cumulativeMoveCount hw hh s cover T]
  exact cover.total_moves_le T

end

end BML
