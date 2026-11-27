import BML.NetMixed

/-!
# Capacity of the roundabout torus (Corollary RB-C)

Every intersection of the `w × h` torus is a roundabout and there are no link
cells. Then

* `undelayed_carCount_le`: a valid state in which nobody is delayed for even
  one tick has at most `w·h` cars, one per roundabout;
* `capacity_attained`: east cars on every east quadrant flow freely for ever,
  so the free-flow capacity is exactly `w·h`.

The upper bound uses one tick: junction cells occupied now are empty next
tick, and every car in a quadrant now is in a junction next tick.
-/
namespace BML.Net

section

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

/-- The roundabout torus. -/
abbrev rtorus : Layout (Position w h) := torus hw hh (fun _ => true) false

variable {hw hh}

theorem rtorus_gate (t : Nat) (k : Species) (c : Grid w h) : (mixed (rtorus hw hh)).gate t k c = true := by
  cases c <;> simp [mixed, rtorus, torus]

/-- Split a count by a second predicate. -/
theorem length_filter_split {β : Type} (l : List β) (p q : β → Bool) :
    (l.filter p).length = (l.filter fun x => p x && q x).length + (l.filter fun x => p x && !q x).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp [ih] <;> omega

def isJunction : Grid w h → Bool
  | .junction _ => true
  | _ => false

variable {s : Config (Grid w h) Species}

/-- In an undelayed tick with every gate open, an occupied cell empties. -/
theorem undelayed_vacates (hu : Undelayed (mixed (rtorus hw hh)) 0 s) (hx : Valid (mixed (rtorus hw hh)) s)
    {c : Grid w h} (hc : (s c).isSome = true) : step (mixed (rtorus hw hh)) 0 s c = none := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hx c k hk)
  have hwd := hu c k d hk hd (rtorus_gate 0 k d)
  have hwc : winner (mixed (rtorus hw hh)) 0 s c = none := by simp [winner, hk]
  simp [step, hwc, leaves, hk, hd, hwd]

/-- A valid car outside the junctions is in a quadrant, and its next cell is a junction. -/
theorem private_next {c : Grid w h} {k : Species} (hx : Valid (mixed (rtorus hw hh)) s)
    (hk : s c = some k) (hj : isJunction c = false) :
    ∃ q, (mixed (rtorus hw hh)).next k c = some (.junction q) := by
  have hv := hx c k hk
  cases c <;> cases k <;> simp_all [isJunction, mixed, Layout.next, rtorus, torus, Layout.outN]

/-- **RB-C, upper bound.** A valid state that is undelayed for one tick has at
most one car per roundabout. -/
theorem undelayed_carCount_le (hu : Undelayed (mixed (rtorus hw hh)) 0 s)
    (hx : Valid (mixed (rtorus hw hh)) s) : carCount s ≤ w * h := by
  let occ := fun (u : Config (Grid w h) Species) (c : Grid w h) => (u c).isSome
  let J := (allSites w h).filter fun c => occ s c && isJunction c
  let P := (allSites w h).filter fun c => occ s c && !isJunction c
  let J' := (allSites w h).filter fun c => occ (step (mixed (rtorus hw hh)) 0 s) c && isJunction c
  have hsplit : carCount s = J.length + P.length := length_filter_split _ _ _
  -- every car in a quadrant enters a junction
  have hPJ : P.length ≤ J'.length := by
    let target : Grid w h → Grid w h := fun c =>
      match s c with
      | some k => (((mixed (rtorus hw hh)).next k c).getD c)
      | none => c
    refine length_le_of_injOn P J' ((allSites_nodup w h).sublist List.filter_sublist) target ?_ ?_
    · intro a ha b hb hab
      obtain ⟨_, hpa⟩ := List.mem_filter.mp ha
      obtain ⟨_, hpb⟩ := List.mem_filter.mp hb
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, occ] at hpa hpb
      obtain ⟨ka, hka⟩ := Option.isSome_iff_exists.mp hpa.1
      obtain ⟨kb, hkb⟩ := Option.isSome_iff_exists.mp hpb.1
      obtain ⟨da, hda⟩ := Option.isSome_iff_exists.mp (hx a ka hka)
      obtain ⟨db, hdb⟩ := Option.isSome_iff_exists.mp (hx b kb hkb)
      simp only [target, hka, hkb, hda, hdb, Option.getD_some] at hab
      subst hab
      have hwa := hu a ka da hka hda (rtorus_gate 0 ka da)
      have hwb := hu b kb da hkb hdb (rtorus_gate 0 kb da)
      rw [hwa] at hwb
      cases Option.some.inj hwb
      have h1 := ((mixed (rtorus hw hh)).prev_iff ka a da).mpr hda
      have h2 := ((mixed (rtorus hw hh)).prev_iff ka b da).mpr hdb
      rw [h1] at h2
      exact Option.some.inj h2
    · intro a ha
      obtain ⟨_, hpa⟩ := List.mem_filter.mp ha
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, occ] at hpa
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hpa.1
      obtain ⟨q, hq⟩ := private_next hx hk hpa.2
      have hwin := hu a k _ hk hq (rtorus_gate 0 k _)
      refine List.mem_filter.mpr ⟨mem_allSites _, ?_⟩
      simp [target, hk, hq, occ, step, hwin, isJunction]
  -- a junction occupied now is empty next tick
  have hJJ : J.length + J'.length ≤ w * h := by
    have hdisj : (J ++ J').Nodup := by
      refine List.nodup_append.mpr ⟨(allSites_nodup w h).sublist List.filter_sublist,
        (allSites_nodup w h).sublist List.filter_sublist, ?_⟩
      intro a ha b hb hab
      subst hab
      have h1 := (List.mem_filter.mp ha).2
      have h2 := (List.mem_filter.mp hb).2
      simp only [Bool.and_eq_true, occ] at h1 h2
      rw [undelayed_vacates hu hx h1.1] at h2
      simp at h2
    have := length_le_of_injOn (J ++ J') ((positions w h).map Site.junction) hdisj id
      (fun _ _ _ _ h => h) (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc <;>
        · have := (List.mem_filter.mp hc).2
          simp only [Bool.and_eq_true] at this
          cases c with
          | junction p => exact List.mem_map.mpr ⟨p, mem_positions w h p, rfl⟩
          | _ => simp [isJunction] at this)
    simpa using this
  omega

/-- **RB-C, upper bound for free flow.** -/
theorem free_carCount_le (hf : Free (mixed (rtorus hw hh)) s) (hx : Valid (mixed (rtorus hw hh)) s) :
    carCount s ≤ w * h :=
  undelayed_carCount_le (hf 0) hx


/-! ### Attainment -/

/-- The intersection a cell belongs to. -/
def Site.where_ : Grid w h → Position w h
  | .junction p | .quadE p | .quadN p | .linkE p | .linkN p => p

/-- East cars on every east quadrant. -/
def eastQuads : Config (Grid w h) Species
  | .quadE _ => some .east
  | _ => none

/-- East cars on every junction. -/
def eastJunctions : Config (Grid w h) Species
  | .junction _ => some .east
  | _ => none

theorem eastQuads_step : step (mixed (rtorus hw hh)) 0 eastQuads = eastJunctions := by
  funext c
  cases c <;>
    simp [step, winner, leaves, wants, mixed, Layout.next, Layout.prev, rtorus, torus,
      Layout.fromE, Layout.lastN, eastQuads, eastJunctions, List.find?]

theorem eastJunctions_step : step (mixed (rtorus hw hh)) 1 eastJunctions = eastQuads := by
  funext c
  cases c <;>
    simp [step, winner, leaves, wants, mixed, Layout.next, Layout.prev, rtorus, torus,
      Layout.intoE, Layout.fromE, Layout.lastN, eastQuads, eastJunctions, List.find?]

theorem eastQuads_undelayed : Undelayed (mixed (rtorus hw hh)) 0 eastQuads := by
  intro p k c hp hn _
  cases p <;> simp [eastQuads] at hp
  subst hp
  simp only [mixed, Layout.next, rtorus, torus, ↓reduceIte, Option.some.injEq] at hn
  subst hn
  simp [winner, wants, mixed, Layout.prev, rtorus, torus, Layout.fromE, eastQuads]

theorem eastJunctions_undelayed : Undelayed (mixed (rtorus hw hh)) 1 eastJunctions := by
  intro p k c hp hn _
  cases p <;> simp [eastJunctions] at hp
  subst hp
  simp only [mixed, Layout.next, rtorus, torus, Bool.false_eq_true, ↓reduceIte, Layout.intoE,
    Option.some.injEq] at hn
  subst hn
  simp [winner, wants, mixed, Layout.prev, rtorus, torus, Layout.fromE, eastJunctions]

theorem eastQuads_free : Free (mixed (rtorus hw hh)) eastQuads := by
  have h1 : run (mixed (rtorus hw hh)) eastQuads 1 = eastJunctions := by
    simp [run, eastQuads_step]
  have h2 : run (mixed (rtorus hw hh)) eastQuads 2 = eastQuads := by
    simp only [run]
    rw [eastQuads_step, eastJunctions_step]
  refine free_of_recurrence (P := 1) (T0 := 0) (m := 2) (fun t k c => by
    rw [rtorus_gate, rtorus_gate]) (by decide) (by rw [show 0 + 1 * 2 = 2 from rfl, h2]; rfl) ?_
  intro t ht
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
  · exact eastQuads_undelayed
  · rw [h1]; exact eastJunctions_undelayed

theorem eastQuads_carCount : carCount (eastQuads : Config (Grid w h) Species) = w * h := by
  apply Nat.le_antisymm
  · have := length_le_of_injOn ((allSites w h).filter fun c => (eastQuads c).isSome)
      (positions w h) ((allSites_nodup w h).sublist List.filter_sublist)
      Site.where_
      (fun a ha b hb hab => by
        have h1 := (List.mem_filter.mp ha).2
        have h2 := (List.mem_filter.mp hb).2
        cases a <;> cases b <;> simp_all [eastQuads, Site.where_])
      (fun _ _ => mem_positions w h _)
    simpa [carCount] using this
  · have := length_le_of_injOn (positions w h) ((allSites w h).filter fun c => (eastQuads c).isSome)
      (positions_nodup w h) Site.quadE (fun a _ b _ hab => by simpa using hab)
      (fun p _ => List.mem_filter.mpr ⟨mem_allSites _, by simp [eastQuads]⟩)
    simpa [carCount] using this

/-- **RB-C.** The free-flow capacity of the roundabout torus is exactly `w·h`:
every valid free state has at most that many cars, and some free state has
exactly that many. -/
theorem capacity_attained :
    Free (mixed (rtorus hw hh)) eastQuads ∧ Valid (mixed (rtorus hw hh)) eastQuads ∧
      carCount (eastQuads : Config (Grid w h) Species) = w * h :=
  ⟨eastQuads_free, fun p k hp => by
    cases p <;> simp [eastQuads] at hp
    subst hp
    simp [mixed, Layout.next, rtorus, torus], eastQuads_carCount⟩

end

end BML.Net
