import BML.Cosets
import BML.Capture

/-! Coordinate translations preserve the two CLASSIC phases and tagged motion. -/
namespace BML

variable {w h : Nat}

abbrev torusOrigin (hw : 0 < w) (hh : 0 < h) : Position w h :=
  (⟨0, hw⟩, ⟨0, hh⟩)

def torusTranslate (hw : 0 < w) (hh : 0 < h) (offset p : Position w h) : Position w h :=
  (cyclicShift w hw offset.1.val p.1, cyclicShift h hh offset.2.val p.2)

theorem torusTranslate_origin (hw : 0 < w) (hh : 0 < h) (offset : Position w h) :
    torusTranslate hw hh offset (torusOrigin hw hh) = offset := by
  have hzero {n : Nat} (hn : 0 < n) (i : Fin n) :
      cyclicShift n hn i.val ⟨0, hn⟩ = i := by
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [cyclicShift_val_int]
    simpa only [Int.natCast_zero, Int.zero_add] using
      (Int.emod_eq_of_lt (by omega : 0 ≤ (i.val : Int)) (by have := i.isLt; omega : (i.val : Int) < n))
  exact Prod.ext (hzero hw _) (hzero hh _)

theorem torusTranslate_surjective (hw : 0 < w) (hh : 0 < h) (offset : Position w h) :
    Function.Surjective (torusTranslate hw hh offset) := by
  intro p
  refine ⟨(cyclicShift w hw (-(offset.1.val : Int)) p.1,
    cyclicShift h hh (-(offset.2.val : Int)) p.2), ?_⟩
  have h0 (z : Int) : z + -z = 0 := by omega
  simp [torusTranslate, cyclicShift_add, h0]

theorem torusTranslate_injective (hw : 0 < w) (hh : 0 < h) (offset : Position w h) :
    Function.Injective (torusTranslate hw hh offset) := by
  intro p q he
  have undo {n : Nat} (hn : 0 < n) (a : Int) (p : Fin n) :
      cyclicShift n hn (-a) (cyclicShift n hn a p) = p := by
    rw [cyclicShift_add, show -a+a = 0 by omega, cyclicShift_zero]
  apply Prod.ext
  · have hv := congrArg (fun p : Position w h => cyclicShift w hw (-(offset.1.val : Int)) p.1) he
    simpa [torusTranslate, undo] using hv
  · have hv := congrArg (fun p : Position w h => cyclicShift h hh (-(offset.2.val : Int)) p.2) he
    simpa [torusTranslate, undo] using hv

private theorem cyclicShift_comm (n : Nat) (hn : 0 < n) (a b : Int) (i : Fin n) :
    cyclicShift n hn a (cyclicShift n hn b i) = cyclicShift n hn b (cyclicShift n hn a i) := by
  rw [cyclicShift_add, cyclicShift_add, Int.add_comm a b]

private theorem torusTranslate_east_next (hw : 0 < w) (hh : 0 < h) (a p : Position w h) :
    torusTranslate hw hh a ((eastDirection w h hw).next p) =
      (eastDirection w h hw).next (torusTranslate hw hh a p) := by
  exact Prod.ext (by simpa [torusTranslate, eastDirection] using cyclicShift_comm w hw a.1.val 1 p.1) rfl

private theorem torusTranslate_east_prev (hw : 0 < w) (hh : 0 < h) (a p : Position w h) :
    torusTranslate hw hh a ((eastDirection w h hw).prev p) =
      (eastDirection w h hw).prev (torusTranslate hw hh a p) := by
  exact Prod.ext (by simpa [torusTranslate, eastDirection] using cyclicShift_comm w hw a.1.val (-1) p.1) rfl

private theorem torusTranslate_north_next (hw : 0 < w) (hh : 0 < h) (a p : Position w h) :
    torusTranslate hw hh a ((northDirection w h hh).next p) =
      (northDirection w h hh).next (torusTranslate hw hh a p) := by
  exact Prod.ext rfl (by simpa [torusTranslate, northDirection] using cyclicShift_comm h hh a.2.val 1 p.2)

private theorem torusTranslate_north_prev (hw : 0 < w) (hh : 0 < h) (a p : Position w h) :
    torusTranslate hw hh a ((northDirection w h hh).prev p) =
      (northDirection w h hh).prev (torusTranslate hw hh a p) := by
  exact Prod.ext rfl (by simpa [torusTranslate, northDirection] using cyclicShift_comm h hh a.2.val (-1) p.2)

private theorem halfStep_comp {α : Type} (d : Direction α) (sp : Species)
    (s : Config α) (f : α → α)
    (next : ∀ p, f (d.next p) = d.next (f p))
    (prev : ∀ p, f (d.prev p) = d.prev (f p)) :
    halfStep d sp (s ∘ f) = halfStep d sp s ∘ f := by
  funext p
  simp [halfStep, next p, prev p]

private theorem eastPhase_translate (hw : 0 < w) (hh : 0 < h) (a : Position w h)
    (s : Config (Position w h)) :
    halfStep (eastDirection w h hw) .east (s ∘ torusTranslate hw hh a) =
      halfStep (eastDirection w h hw) .east s ∘ torusTranslate hw hh a :=
  halfStep_comp _ _ _ _ (torusTranslate_east_next hw hh a) (torusTranslate_east_prev hw hh a)

theorem torusStep_translate (hw : 0 < w) (hh : 0 < h) (a : Position w h)
    (s : Config (Position w h)) :
    torusStep w h hw hh (s ∘ torusTranslate hw hh a) =
      torusStep w h hw hh s ∘ torusTranslate hw hh a := by
  unfold torusStep step
  rw [eastPhase_translate]
  exact halfStep_comp _ _ _ _ (torusTranslate_north_next hw hh a) (torusTranslate_north_prev hw hh a)

theorem torusIterate_translate (hw : 0 < w) (hh : 0 < h) (a : Position w h)
    (s : Config (Position w h)) (t : Nat) :
    iterate (torusStep w h hw hh) t (s ∘ torusTranslate hw hh a) =
      iterate (torusStep w h hw hh) t s ∘ torusTranslate hw hh a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [iterate, ih, torusStep_translate]

theorem translated_fixed_iff (hw : 0 < w) (hh : 0 < h) (a : Position w h)
    (s : Config (Position w h)) :
    torusStep w h hw hh (s ∘ torusTranslate hw hh a) = s ∘ torusTranslate hw hh a ↔
      torusStep w h hw hh s = s := by
  rw [torusStep_translate]
  constructor
  · intro he
    funext p
    obtain ⟨q, rfl⟩ := torusTranslate_surjective hw hh a p
    exact congrFun he q
  · intro he
    rw [he]

theorem translated_canMove_iff (hw : 0 < w) (hh : 0 < h) (a : Position w h)
    (sp : Species) (s : Config (Position w h)) (p : Position w h) :
    RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp
      (s ∘ torusTranslate hw hh a) p ↔
    RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp s (torusTranslate hw hh a p) := by
  cases sp
  · simp [RoundCanMove, CanMove, torusTranslate_east_next hw hh a p]
  · simp only [RoundCanMove, eastPhase_translate, CanMove]
    simp [torusTranslate_north_next hw hh a p]

theorem torusTranslate_carTrace (hw : 0 < w) (hh : 0 < h) (a : Position w h)
    (sp : Species) (s : Config (Position w h)) (t : Nat) (p : Position w h) :
    let e := eastDirection w h hw
    let n := northDirection w h hh
    let f := torusTranslate hw hh a
    f (carTrace e n sp (s ∘ f) t p) = carTrace e n sp s t (f p) := by
  let e := eastDirection w h hw
  let n := northDirection w h hh
  let f := torusTranslate hw hh a
  change f (carTrace e n sp (s ∘ f) t p) = carTrace e n sp s t (f p)
  induction t with
  | zero => rfl
  | succ t ih =>
    let u := iterate (torusStep w h hw hh) t s
    let q := carTrace e n sp (s ∘ f) t p
    change f (roundTransport e n sp (iterate (torusStep w h hw hh) t (s ∘ f)) q) =
      roundTransport e n sp u (carTrace e n sp s t (f p))
    rw [torusIterate_translate, ← ih]
    change f (roundTransport e n sp (u ∘ f) q) = roundTransport e n sp u (f q)
    have hm : RoundCanMove e n sp (u ∘ f) q ↔ RoundCanMove e n sp u (f q) :=
      translated_canMove_iff hw hh a sp u q
    cases sp
    · simp only [RoundCanMove] at hm
      simp only [roundTransport, transport, hm]
      split
      · exact torusTranslate_east_next hw hh a q
      · rfl
    · simp only [RoundCanMove] at hm
      simp only [roundTransport, transport, hm]
      split
      · exact torusTranslate_north_next hw hh a q
      · rfl

end BML
