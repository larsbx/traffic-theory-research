import BML.Absorption
import BML.GatedTranspose
import BML.PackedKernel
import BML.ThinTorus
import BML.TorusTranslation

/-!
The four small CLASSIC tori. The finite certificate checks two facts:
a fixed point reached in 12 rounds was already fixed at 11, and each
addition to a board fixed by 11 either jams or reaches a cycle on
which only the added tag may move. Translations put the added car at
the origin. Both claims are transferred back through the CLASSIC kernel.
-/
namespace BML.Gated

open Packed

variable {w h : Nat}

private def paint (b : Board) (i : Nat) : Cell → Board
  | .empty => b
  | .east => ⟨b.east ||| 2^i, b.north⟩
  | .north => ⟨b.east, b.north ||| 2^i⟩

private theorem paint_read (b : Board) (i j : Nat) (c : Cell) (sp : Species) :
    ((paint b j c).mask sp).testBit i =
      ((b.mask sp).testBit i || (decide (j = i) && decide (c = sp.cell))) := by
  cases c <;> cases sp <;> simp [paint, Board.mask, Species.cell, Nat.testBit_two_pow]

/-- All assignments of sites 1 through n, with the origin kept as a hole. -/
private def allTail (check : Board → Bool) : Nat → Board → Bool
  | 0, b => check b
  | n+1, b =>
    allTail check n b && allTail check n (paint b (n+1) .east) &&
      allTail check n (paint b (n+1) .north)

private def fillTail (cells : Nat → Cell) : Nat → Board → Board
  | 0, b => b
  | n+1, b => fillTail cells n (paint b (n+1) (cells (n+1)))

private theorem allTail_complete (check : Board → Bool) (cells : Nat → Cell)
    (n : Nat) (b : Board) (hok : allTail check n b = true) :
    check (fillTail cells n b) = true := by
  induction n generalizing b with
  | zero => exact hok
  | succ n ih =>
    simp only [allTail, Bool.and_eq_true] at hok
    simp only [fillTail]
    cases hc : cells (n+1) with
    | empty => exact ih b hok.1.1
    | east => exact ih _ hok.1.2
    | north => exact ih _ hok.2

private theorem fillTail_read (cells : Nat → Cell) (n : Nat) (b : Board) (i : Nat) (sp : Species) :
    ((fillTail cells n b).mask sp).testBit i =
      ((b.mask sp).testBit i || (decide (0 < i ∧ i ≤ n) && decide (cells i = sp.cell))) := by
  induction n generalizing b with
  | zero =>
    have hn : ¬ (0 < i ∧ i ≤ 0) := by omega
    simp only [fillTail, hn, decide_false, Bool.false_and, Bool.or_false]
  | succ n ih =>
    rw [fillTail, ih, paint_read]
    by_cases hi : n+1 = i
    · subst i
      simp [show ¬ n + 1 ≤ n by omega]
    · have hbound : (0 < i ∧ i ≤ n+1) ↔ (0 < i ∧ i ≤ n) := by omega
      simp [hi, hbound]

private theorem rank_eq {hw : 0 < w} {p q : Position w h}
    (he : (rowMajorRank w h p).val = (rowMajorRank w h q).val) : p = q := by
  have h := congrArg (rowMajorPosition w h hw) (Fin.ext he)
  simpa only [rowMajorPosition_rank] using h

@[simp] private theorem rank_origin (hw : 0 < w) (hh : 0 < h) :
    (rowMajorRank w h (torusOrigin hw hh)).val = 0 := by simp

private theorem normalized_covered (hw : 0 < w) (hh : 0 < h)
    (test : Board → Bool) (s : Config (Position w h)) (h0 : s (torusOrigin hw hh) = .empty)
    (hcheck : allTail test (w*h-1) ⟨0, 0⟩ = true) :
    ∃ b, Represents b s ∧ test b = true := by
  let cells (i : Nat) := if hi : i < w*h then s (rowMajorPosition w h hw ⟨i, hi⟩) else .empty
  let b := fillTail cells (w*h-1) ⟨0, 0⟩
  refine ⟨b, ?_, allTail_complete test cells (w*h-1) ⟨0, 0⟩ hcheck⟩
  intro sp p
  let i := rowMajorRank w h p
  change ((fillTail cells (w*h-1) ⟨0, 0⟩).mask sp).testBit i.val = _
  rw [fillTail_read]
  have hz : (Board.mask ⟨0, 0⟩ sp).testBit i.val = false := by cases sp <;> simp [Board.mask]
  rw [hz]
  by_cases hzero : i.val = 0
  · have hp : p = torusOrigin hw hh := rank_eq (hw := hw) (hzero.trans (rank_origin hw hh).symm)
    rw [hp, h0]
    simp [hzero, Ne.symm sp.cell_ne_empty]
  · have hbound : 0 < i.val ∧ i.val ≤ w*h-1 := by have := i.isLt; omega
    have hc : cells i.val = s p := by
      simp only [cells, i.isLt, ↓reduceDIte]
      exact congrArg s (rowMajorPosition_rank w h hw p)
    simp [hbound, hc]

private theorem added_rep (hw : 0 < w) (hh : 0 < h)
    {x y : Config (Position w h)} {b : Board} (hb : Represents b x)
    (hz : x (torusOrigin hw hh) = .empty) (added : Species)
    (ha : y (torusOrigin hw hh) = added.cell)
    (hsame : ∀ p, p ≠ torusOrigin hw hh → y p = x p) :
    Represents (paint b 0 added.cell) y := by
  intro sp p
  rw [paint_read, hb sp p]
  by_cases hp : p = torusOrigin hw hh
  · subst p
    simp [hz, ha, Ne.symm sp.cell_ne_empty]
  · have hne : 0 ≠ (rowMajorRank w h p).val :=
      fun he => hp (rank_eq (hw := hw) (he.symm.trans (rank_origin hw hh).symm))
    simp only [hne, decide_false, Bool.false_and, Bool.or_false, hsame p hp]

private def movingMask (area : Nat) (r : Layout) (sp : Species) (b : Board) : Nat :=
  match sp with
  | .east => movers area r.eastPrev .east b
  | .north => movers area r.northPrev .north (eastPhase area r b)

private theorem movingMask_read {hw : 0 < w} {hh : 0 < h} {r : Layout} (hr : r.Valid hw hh)
    {b : Board} {s : Config (Position w h)} (hb : Represents b s) (sp : Species) (p : Position w h) :
    (movingMask (w*h) r sp b).testBit (rowMajorRank w h p).val =
      decide (RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp s p) := by
  cases sp
  · exact movers_read hr.eastPrev .east hb p
  · exact movers_read hr.northPrev .north (eastPhase_rep hr hb) p

private def packedTagStep (hw : 0 < w) (hh : 0 < h) (r : Layout)
    (sp : Species) (u : Board × Position w h) : Board × Position w h :=
  let (b, p) := u
  let q := if (movingMask (w*h) r sp b).testBit (rowMajorRank w h p).val then
    match sp with
    | .east => (eastDirection w h hw).next p
    | .north => (northDirection w h hh).next p
  else p
  (Packed.round (w*h) r b, q)

private def kernelTagStep (hw : 0 < w) (hh : 0 < h) (sp : Species)
    (u : Config (Position w h) × Position w h) : Config (Position w h) × Position w h :=
  (torusStep w h hw hh u.1, roundTransport (eastDirection w h hw) (northDirection w h hh) sp u.1 u.2)

private theorem packedTag_iterate {hw : 0 < w} {hh : 0 < h} {r : Layout} (hr : r.Valid hw hh)
    (sp : Species) {b : Board} {s : Config (Position w h)} (hb : Represents b s)
    (p : Position w h) (t : Nat) :
    let a := iterate (packedTagStep hw hh r sp) t (b, p)
    let c := iterate (kernelTagStep hw hh sp) t (s, p)
    Represents a.1 c.1 ∧ a.2 = c.2 := by
  induction t with
  | zero => exact ⟨hb, rfl⟩
  | succ t ih =>
    let a := iterate (packedTagStep hw hh r sp) t (b, p)
    let c := iterate (kernelTagStep hw hh sp) t (s, p)
    change Represents (packedTagStep hw hh r sp a).1 (kernelTagStep hw hh sp c).1 ∧
      (packedTagStep hw hh r sp a).2 = (kernelTagStep hw hh sp c).2
    have ha : Represents a.1 c.1 := ih.1
    have hp : a.2 = c.2 := ih.2
    refine ⟨round_rep hr ha, ?_⟩
    simp only [packedTagStep, kernelTagStep]
    rw [hp, movingMask_read hr ha]
    by_cases hm : RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp c.1 c.2
    · have hd := decide_eq_true hm
      rw [hd]
      cases sp <;> simp only [RoundCanMove] at hm <;>
        simp [roundTransport, transport, hm]
    · have hd := decide_eq_false hm
      rw [hd]
      cases sp <;> simp only [RoundCanMove] at hm <;>
        simp [roundTransport, transport, hm]

private theorem kernelTag_iterate (hw : 0 < w) (hh : 0 < h) (sp : Species)
    (s : Config (Position w h)) (p : Position w h) (t : Nat) :
    iterate (kernelTagStep hw hh sp) t (s, p) =
      (iterate (torusStep w h hw hh) t s,
        carTrace (eastDirection w h hw) (northDirection w h hh) sp s t p) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iterate, ih, kernelTagStep, carTrace]
    rfl

private def onlyTagMoves (r : Layout) (sp : Species) (u : Board × Position w h) : Bool :=
  ([.east, .north] : List Species).all fun observed =>
    let m := movingMask (w*h) r observed u.1
    m == 0 || m == (if observed = sp then 2^(rowMajorRank w h u.2).val else 0)

private theorem onlyTagMoves_sound {hw : 0 < w} {hh : 0 < h} {r : Layout}
    (hr : r.Valid hw hh) {b : Board} {s : Config (Position w h)} (hb : Represents b s)
    (sp : Species) (p : Position w h) (hc : onlyTagMoves r sp (b, p) = true)
    (observed : Species) (q : Position w h)
    (hm : RoundCanMove (eastDirection w h hw) (northDirection w h hh) observed s q) :
    observed = sp ∧ q = p := by
  have hbit : (movingMask (w*h) r observed b).testBit (rowMajorRank w h q).val = true := by
    rw [movingMask_read hr hb]
    exact decide_eq_true hm
  have hcheck := List.all_eq_true.mp hc observed (by cases observed <;> simp)
  simp only [Bool.or_eq_true, beq_iff_eq] at hcheck
  rcases hcheck with hh' | hh'
  · rw [hh', Nat.zero_testBit] at hbit
    cases hbit
  · by_cases he : observed = sp
    · subst observed
      simp at hh'
      rw [hh', Nat.testBit_two_pow, decide_eq_true_eq] at hbit
      exact ⟨rfl, rank_eq (hw := hw) hbit.symm⟩
    · simp only [he, ↓reduceIte] at hh'
      rw [hh', Nat.zero_testBit] at hbit
      cases hbit

private def packedFixed (area : Nat) (r : Layout) (b : Board) : Bool :=
  Packed.same area (Packed.round area r b) b

private theorem packedFixed_iff {hw : 0 < w} {hh : 0 < h} {r : Layout} (hr : r.Valid hw hh)
    {b : Board} {s : Config (Position w h)} (hb : Represents b s) :
    packedFixed (w*h) r b = true ↔ torusStep w h hw hh s = s :=
  Packed.same_iff hw (round_rep hr hb) hb

private def jamCutoff : Nat := 11
private def quietStart : Nat := 3
private def quietPeriod : Nat := 6

private def checkCycle (hw : 0 < w) (hh : 0 < h) (r : Layout) (sp : Species) (b : Board) : Bool :=
  let next := packedTagStep hw hh r sp
  let seed := iterate next quietStart (b, torusOrigin hw hh)
  let last := iterate next quietPeriod seed
  Packed.same (w*h) last.1 seed.1 && decide (last.2 = seed.2) &&
    (List.range quietPeriod).all (fun t => onlyTagMoves r sp (iterate next t seed))

private def checkAdded (hw : 0 < w) (hh : 0 < h) (r : Layout) (b : Board) (sp : Species) : Bool :=
  let y := paint b 0 sp.cell
  packedFixed (w*h) r (iterate (Packed.round (w*h) r) jamCutoff y) ||
    checkCycle hw hh r sp y

private def checkBoard (hw : 0 < w) (hh : 0 < h) (r : Layout) (b : Board) : Bool :=
  let next := Packed.round (w*h) r
  let cutoff := iterate next jamCutoff b
  if packedFixed (w*h) r cutoff then
    checkAdded hw hh r b .east && checkAdded hw hh r b .north
  else
    !(packedFixed (w*h) r (next cutoff))

-- The normalized enumeration covers all boards once the added site is fixed.
/-- Check the finite fixed-point and single-tag cycle certificates for this layout. -/
def unjammingExclusionCheck (hw : 0 < w) (hh : 0 < h) (r : Layout) : Bool :=
  allTail (checkBoard hw hh r) (w*h-1) ⟨0, 0⟩

private theorem quietPeriod_pos : 0 < quietPeriod := by decide
attribute [local irreducible] jamCutoff quietStart quietPeriod

private theorem periodic_remainder {α : Type} (f : α → α) (s : α) {k : Nat}
    (hret : iterate f k s = s) (t : Nat) :
    iterate f t s = iterate f (t % k) s := by
  calc
    iterate f t s = iterate f (k * (t / k) + t % k) s := by
      rw [Nat.add_comm (k * (t / k)), Nat.mod_add_div]
    _ = iterate f (t % k) s := by
      rw [iterate_add, Absorption.iterate_mul_of_return f s k hret (t / k)]

private theorem checkCycle_sound {hw : 0 < w} {hh : 0 < h} {r : Layout}
    (hr : r.Valid hw hh) {b : Board} {s : Config (Position w h)} (hb : Represents b s)
    (sp : Species) (hc : checkCycle hw hh r sp b = true) :
    ∀ t observed q,
      RoundCanMove (eastDirection w h hw) (northDirection w h hh) observed
        (iterate (torusStep w h hw hh) (quietStart+t) s) q →
      observed = sp ∧ q = carTrace (eastDirection w h hw) (northDirection w h hh)
        sp s (quietStart+t) (torusOrigin hw hh) := by
  let p := torusOrigin hw hh
  let fast := packedTagStep hw hh r sp
  let exactStep := kernelTagStep hw hh sp
  let seed := iterate fast quietStart (b, p)
  let seed' := iterate exactStep quietStart (s, p)
  let last := iterate fast quietPeriod seed
  have hseed : Represents seed.1 seed'.1 ∧ seed.2 = seed'.2 :=
    packedTag_iterate hr sp hb p quietStart
  have hshifted (t : Nat) :
      Represents (iterate fast t seed).1 (iterate exactStep t seed').1 ∧
        (iterate fast t seed).2 = (iterate exactStep t seed').2 := by
    have hseed' : (seed'.1, seed.2) = seed' := Prod.ext rfl hseed.2
    have he := packedTag_iterate hr sp hseed.1 seed.2 t
    change Represents (iterate fast t (seed.1, seed.2)).1
      (iterate exactStep t (seed'.1, seed.2)).1 ∧ _ at he
    simpa only [hseed'] using he
  change (Packed.same (w*h) last.1 seed.1 && decide (last.2 = seed.2) &&
    (List.range quietPeriod).all (fun t => onlyTagMoves r sp (iterate fast t seed))) = true at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hreturn : iterate exactStep quietPeriod seed' = seed' := Prod.ext
    ((Packed.same_iff hw (hshifted quietPeriod).1 hseed.1).mp hc.1.1)
    (((hshifted quietPeriod).2.symm.trans hc.1.2).trans hseed.2)
  intro t observed q hm
  let remainder := t % quietPeriod
  have hmem : remainder ∈ List.range quietPeriod :=
    List.mem_range.mpr (Nat.mod_lt _ quietPeriod_pos)
  have hquiet := List.all_eq_true.mp hc.2 remainder hmem
  have htime : iterate exactStep remainder seed' =
      (iterate (torusStep w h hw hh) (quietStart+t) s,
        carTrace (eastDirection w h hw) (northDirection w h hh) sp s (quietStart+t) p) := by
    rw [← periodic_remainder exactStep seed' hreturn t]
    change iterate exactStep t (iterate exactStep quietStart (s,p)) = _
    rw [← iterate_add]
    exact kernelTag_iterate hw hh sp s p (quietStart+t)
  have hactual : RoundCanMove (eastDirection w h hw) (northDirection w h hh) observed
      (iterate exactStep remainder seed').1 q := by
    rw [htime]
    exact hm
  obtain ⟨he, hq⟩ := onlyTagMoves_sound hr (hshifted remainder).1 sp _ hquiet observed q hactual
  exact ⟨he, hq.trans ((hshifted remainder).2.trans (congrArg Prod.snd htime))⟩

private theorem checkAdded_sound {hw : 0 < w} {hh : 0 < h} {r : Layout}
    (hr : r.Valid hw hh) {b : Board} {x y : Config (Position w h)}
    (hb : Represents b x) (hz : x (torusOrigin hw hh) = .empty)
    (sp : Species) (ha : y (torusOrigin hw hh) = sp.cell)
    (hsame : ∀ p, p ≠ torusOrigin hw hh → y p = x p)
    (hc : checkAdded hw hh r b sp = true) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) y ∨
    ∀ t observed q,
      RoundCanMove (eastDirection w h hw) (northDirection w h hh) observed
        (iterate (torusStep w h hw hh) (quietStart+t) y) q →
      observed = sp ∧ q = carTrace (eastDirection w h hw) (northDirection w h hh)
        sp y (quietStart+t) (torusOrigin hw hh) := by
  have hy := added_rep hw hh hb hz sp ha hsame
  simp only [checkAdded, Bool.or_eq_true] at hc
  rcases hc with hhit | hcycle
  · have hfixed := (packedFixed_iff hr (iterate_rep hr hy jamCutoff)).mp hhit
    have hne : Nonempty y := ⟨torusOrigin hw hh, fun he => sp.cell_ne_empty (ha.symm.trans he)⟩
    refine Or.inl ⟨jamCutoff, (jam_iff_nonempty_fixed _ _ _).mpr ⟨?_, hfixed⟩⟩
    exact (iterate_nonempty_iff _ _ y jamCutoff).mpr hne
  · exact Or.inr (checkCycle_sound hr hy sp hcycle)

private theorem checked_reflects_fixed {hw : 0 < w} {hh : 0 < h} {r : Layout}
    (hr : r.Valid hw hh) {b : Board} {s : Config (Position w h)} (hb : Represents b s)
    (hc : checkBoard hw hh r b = true)
    (hfixed : torusStep w h hw hh (iterate (torusStep w h hw hh) (jamCutoff+1) s) =
      iterate (torusStep w h hw hh) (jamCutoff+1) s) :
    torusStep w h hw hh (iterate (torusStep w h hw hh) jamCutoff s) =
      iterate (torusStep w h hw hh) jamCutoff s := by
  let atCutoff := iterate (Packed.round (w*h) r) jamCutoff b
  have rep := iterate_rep hr hb jamCutoff
  have hnext : packedFixed (w*h) r (Packed.round (w*h) r atCutoff) = true :=
    (packedFixed_iff hr (round_rep hr rep)).mpr hfixed
  cases he : packedFixed (w*h) r atCutoff with
  | true => exact (packedFixed_iff hr rep).mp he
  | false =>
    change (if packedFixed (w*h) r atCutoff then _ else
      !(packedFixed (w*h) r (Packed.round (w*h) r atCutoff))) = true at hc
    rw [he, hnext] at hc
    cases hc

private theorem cutoff_stable {hw : 0 < w} {hh : 0 < h} {r : Layout} (hr : r.Valid hw hh)
    (hchecked : allTail (checkBoard hw hh r) (w*h-1) ⟨0, 0⟩ = true) :
    let f := torusStep w h hw hh
    ∀ s, f (iterate f (jamCutoff+1) s) = iterate f (jamCutoff+1) s →
      f (iterate f jamCutoff s) = iterate f jamCutoff s := by
  classical
  dsimp only
  let f := torusStep w h hw hh
  intro s hfixed
  by_cases hhole : ∃ q, s q = .empty
  · obtain ⟨q, hq⟩ := hhole
    let translate := torusTranslate hw hh q
    have hz : (s ∘ translate) (torusOrigin hw hh) = .empty := by
      simp [translate, torusTranslate_origin, hq]
    obtain ⟨b, hb, hc⟩ := normalized_covered hw hh _ _ hz hchecked
    have hupper : f (iterate f (jamCutoff+1) (s ∘ translate)) =
        iterate f (jamCutoff+1) (s ∘ translate) := by
      change torusStep w h hw hh (iterate (torusStep w h hw hh) (jamCutoff+1) (s ∘ translate)) = _
      rw [torusIterate_translate]
      exact (translated_fixed_iff hw hh q _).mpr hfixed
    have hlower := checked_reflects_fixed hr hb hc hupper
    rw [torusIterate_translate] at hlower
    exact (translated_fixed_iff hw hh q _).mp hlower
  · have hf : f s = s := (step_eq_iff_frozen _ _ s).mpr
      (fully_occupied_frozen _ _ s (fun p hp => hhole ⟨p, hp⟩))
    change f (iterate f jamCutoff s) = iterate f jamCutoff s
    simpa only [iterate_eq_of_fixed f s hf jamCutoff] using hf

private theorem fixed_at_cutoff_of_later {α : Type} (f : α → α) (cutoff : Nat)
    (back : ∀ s, f (iterate f (cutoff+1) s) = iterate f (cutoff+1) s →
      f (iterate f cutoff s) = iterate f cutoff s)
    (s : α) (delay : Nat) (hfixed : f (iterate f (cutoff+delay) s) = iterate f (cutoff+delay) s) :
    f (iterate f cutoff s) = iterate f cutoff s := by
  induction delay with
  | zero => exact hfixed
  | succ d ih =>
    apply ih
    have hb := back (iterate f d s)
    rw [← iterate_add, ← iterate_add, show d + cutoff = cutoff + d by omega,
      show d + (cutoff+1) = cutoff + (d+1) by omega] at hb
    exact hb hfixed

theorem no_genuine_unjamming_of_check {hw : 0 < w} {hh : 0 < h} {r : Layout}
    (hr : r.Valid hw hh) (hchecked : unjammingExclusionCheck hw hh r = true)
    (x y : Config (Position w h)) : ¬ GenuineUnjamming hw hh x y := by
  let e := eastDirection w h hw
  let n := northDirection w h hh
  let f := torusStep w h hw hh
  rintro ⟨⟨a, added, ha, hay, hsame⟩, hx, hy, ⟨p, sp, hpx, hpy, hlate⟩⟩
  let translate := torusTranslate hw hh a
  let origin := torusOrigin hw hh
  let x' := x ∘ translate
  let y' := y ∘ translate
  have ht0 : translate origin = a := torusTranslate_origin hw hh a
  have h0x : x' origin = .empty := by simpa [x', ht0] using ha
  have h0y : y' origin = added.cell := by simpa [y', ht0] using hay
  have hs' : ∀ q, q ≠ origin → y' q = x' q := by
    intro q hq
    apply hsame
    intro heq
    exact hq (torusTranslate_injective hw hh a (heq.trans ht0.symm))
  obtain ⟨t, hj⟩ := hx
  have hfixed : f (iterate f (jamCutoff+t) x) = iterate f (jamCutoff+t) x := by
    change torusStep w h hw hh (iterate (torusStep w h hw hh) (jamCutoff+t) x) = _
    rw [Nat.add_comm jamCutoff t, iterate_add]
    have hf := (step_eq_iff_frozen e n (iterate f t x)).mpr hj.2
    have he := frozen_persists e n (iterate f t x) hj.2 jamCutoff
    change iterate (torusStep w h hw hh) jamCutoff (iterate f t x) = _ at he
    rwa [he]
  have hxFixed := fixed_at_cutoff_of_later f jamCutoff (cutoff_stable hr hchecked) x t hfixed
  have hx'Fixed : f (iterate f jamCutoff x') = iterate f jamCutoff x' := by
    change torusStep w h hw hh (iterate (torusStep w h hw hh) jamCutoff (x ∘ translate)) = _
    rw [torusIterate_translate]
    exact (translated_fixed_iff hw hh a _).mpr hxFixed
  obtain ⟨b, hb, hc⟩ := normalized_covered hw hh _ x' h0x hchecked
  have bh := (packedFixed_iff hr (iterate_rep hr hb jamCutoff)).mpr hx'Fixed
  simp only [checkBoard, bh, ↓reduceIte, Bool.and_eq_true] at hc
  have hc' : checkAdded hw hh r b added = true := by
    cases added
    · exact hc.1
    · exact hc.2
  rcases checkAdded_sound hr hb h0x added h0y hs' hc' with hj' | hquiet
  · obtain ⟨time, hs⟩ := hj'
    have hfixed' := (jam_iff_nonempty_fixed e n _).mp hs |>.2
    change f (iterate f time y') = iterate f time y' at hfixed'
    change torusStep w h hw hh (iterate (torusStep w h hw hh) time (y ∘ translate)) =
      iterate (torusStep w h hw hh) time (y ∘ translate) at hfixed'
    rw [torusIterate_translate] at hfixed'
    have horig := (translated_fixed_iff hw hh a _).mp hfixed'
    have hne : Nonempty y := ⟨a, fun h => added.cell_ne_empty (hay.symm.trans h)⟩
    exact hy time ((jam_iff_nonempty_fixed e n _).mpr
      ⟨(iterate_nonempty_iff e n y time).mpr hne, horig⟩)
  · obtain ⟨q, hq⟩ := torusTranslate_surjective hw hh a p
    change translate q = p at hq
    obtain ⟨time, ht, hm⟩ := hlate quietStart
    let delay := time - quietStart
    have htime : quietStart + delay = time := Nat.add_sub_of_le ht
    have hm' : RoundCanMove e n sp (iterate f time y') (carTrace e n sp y' time q) := by
      change RoundCanMove e n sp (iterate (torusStep w h hw hh) time (y ∘ translate)) _
      rw [torusIterate_translate]
      apply (translated_canMove_iff hw hh a sp _ _).mpr
      have htrace : translate (carTrace e n sp y' time q) = carTrace e n sp y time (translate q) :=
        torusTranslate_carTrace hw hh a sp y time q
      change RoundCanMove e n sp (iterate f time y) (translate (carTrace e n sp (y ∘ translate) time q))
      rw [htrace, hq]
      exact hm
    rw [← htime] at hm'
    obtain ⟨hrsp, hpos⟩ := hquiet delay sp _ hm'
    subst sp
    have hyq : y' q = added.cell := by simpa [y', hq] using hpy
    have heq := carTrace_injective_on_cars e n added y' (quietStart+delay) q origin hyq h0y hpos
    have hqa : q = origin := heq
    have hpqa : p = a := hq.symm.trans ((congrArg translate hqa).trans ht0)
    rw [hpqa, ha] at hpx
    exact added.cell_ne_empty hpx.symm


end BML.Gated
