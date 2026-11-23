import BML.Torus
import BML.Arithmetic

/-!
The occupied blocker graph of the synchronous BML model. A frozen state keeps
every blocker iterate occupied. Every closed blocker walk has nonnegative
horizontal and vertical windings, so its positive length is at least min(W,H).
Cycle extraction and the bound by the number of occupied cells are separate.
-/
namespace BML

/-- Follow the car's direction. The empty-cell branch is irrelevant on a
frozen occupied orbit; choosing north makes this a total function. -/
def blocker (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (p : Position w h) : Position w h :=
  if s p = .east then (eastDirection w h hw).next p
  else (northDirection w h hh).next p

theorem blocker_preserves_occupied (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (p : Position w h) (hp : s p ≠ .empty) :
    s (blocker w h hw hh s p) ≠ .empty := by
  cases hc : s p with
  | empty => exact False.elim (hp hc)
  | east => simpa [blocker, hc] using hf.1 p hc
  | north => simpa [blocker, hc] using hf.2 p hc

theorem blocker_iterate_occupied (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (p : Position w h) (hp : s p ≠ .empty) (k : Nat) :
    s (iterate (blocker w h hw hh s) k p) ≠ .empty := by
  induction k with
  | zero => exact hp
  | succ k ih => exact blocker_preserves_occupied w h hw hh s hf _ ih

/-- Lift a blocker walk to the nonnegative lattice. `a` and `b` count east and
north steps; `u` and `v` count their respective crossings of the torus seam.
No occupancy assumption is needed for this geometric identity. -/
theorem blocker_walk_lift (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (p : Position w h) (k : Nat) :
    ∃ a b u v : Nat, a + b = k ∧
      p.1.val + a = (iterate (blocker w h hw hh s) k p).1.val + w * u ∧
      p.2.val + b = (iterate (blocker w h hw hh s) k p).2.val + h * v := by
  induction k with
  | zero => exact ⟨0, 0, 0, 0, by simp [iterate]⟩
  | succ k ih =>
    obtain ⟨a, b, u, v, hab, hx, hy⟩ := ih
    let q := iterate (blocker w h hw hh s) k p
    have hqx : q.1.val < w := q.1.isLt
    have hqy : q.2.val < h := q.2.isLt
    change p.1.val + a = q.1.val + w * u at hx
    change p.2.val + b = q.2.val + h * v at hy
    by_cases he : s q = .east
    · by_cases hwrap : q.1.val + 1 < w
      · refine ⟨a + 1, b, u, v, by omega, ?_, ?_⟩
        · change p.1.val + (a + 1) = (blocker w h hw hh s q).1.val + w * u
          simp [blocker, he, eastDirection, cyclicNext, hwrap]
          omega
        · change p.2.val + b = (blocker w h hw hh s q).2.val + h * v
          simpa [blocker, he, eastDirection] using hy
      · refine ⟨a + 1, b, u + 1, v, by omega, ?_, ?_⟩
        · change p.1.val + (a + 1) = (blocker w h hw hh s q).1.val + w * (u + 1)
          simp [blocker, he, eastDirection, cyclicNext, hwrap, Nat.mul_add]
          omega
        · change p.2.val + b = (blocker w h hw hh s q).2.val + h * v
          simpa [blocker, he, eastDirection] using hy
    · by_cases hwrap : q.2.val + 1 < h
      · refine ⟨a, b + 1, u, v, by omega, ?_, ?_⟩
        · change p.1.val + a = (blocker w h hw hh s q).1.val + w * u
          simpa [blocker, he, northDirection] using hx
        · change p.2.val + (b + 1) = (blocker w h hw hh s q).2.val + h * v
          simp [blocker, he, northDirection, cyclicNext, hwrap]
          omega
      · refine ⟨a, b + 1, u, v + 1, by omega, ?_, ?_⟩
        · change p.1.val + a = (blocker w h hw hh s q).1.val + w * u
          simpa [blocker, he, northDirection] using hx
        · change p.2.val + (b + 1) = (blocker w h hw hh s q).2.val + h * (v + 1)
          simp [blocker, he, northDirection, cyclicNext, hwrap, Nat.mul_add]
          omega

/-- A closed blocker walk winds an integral number of times in each direction. -/
theorem blocker_closed_winding (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (p : Position w h) (k : Nat)
    (hclose : iterate (blocker w h hw hh s) k p = p) :
    ∃ a b : Nat, a + b = k ∧ w ∣ a ∧ h ∣ b := by
  obtain ⟨a, b, u, v, hab, hx, hy⟩ := blocker_walk_lift w h hw hh s p k
  rw [hclose] at hx hy
  exact ⟨a, b, hab, ⟨u, by omega⟩, ⟨v, by omega⟩⟩

/-- Every positive closed blocker walk has at least the shorter side's length. -/
theorem blocker_closed_length_lower_bound (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (p : Position w h) (k : Nat)
    (hk : 0 < k) (hclose : iterate (blocker w h hw hh s) k p = p) :
    min w h ≤ k := by
  obtain ⟨a, b, hab, ha, hb⟩ := blocker_closed_winding w h hw hh s p k hclose
  have hbound := winding_length_lower_bound w h a b ha hb (by omega)
  omega

end BML
