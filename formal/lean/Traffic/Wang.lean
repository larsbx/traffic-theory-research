import Traffic.Core

/-!
# Exact finite Wang recoding of frozen BML configurations

A tile `(a,b,c)` has west/south color `a`, east color `b`, and north
color `c`.  Tile orientations are fixed.  Exhaustive kernel computation
establishes that precisely 21 distinct tiles obey the blocking rule.
-/

namespace Traffic.Wang

structure Tile where
  center : Cell
  east : Cell
  north : Cell
  deriving DecidableEq, Repr, Inhabited

def Tile.west (t : Tile) : Cell := t.center

def Tile.south (t : Tile) : Cell := t.center

def Allowed (t : Tile) : Prop :=
  (t.center = .east → t.east ≠ .empty) ∧
  (t.center = .north → t.north ≠ .empty)

instance (t : Tile) : Decidable (Allowed t) :=
  inferInstanceAs (Decidable
    ((t.center = .east → t.east ≠ .empty) ∧
     (t.center = .north → t.north ≠ .empty)))

def allTiles : List Tile :=
  allCells.flatMap fun a =>
    allCells.flatMap fun b =>
      allCells.map fun c => ⟨a, b, c⟩

def allowedTiles : List Tile :=
  allTiles.filter fun t => decide (Allowed t)

theorem allTiles_length : allTiles.length = 27 := by decide

theorem allTiles_nodup : allTiles.Nodup := by decide

theorem mem_allTiles (t : Tile) : t ∈ allTiles := by
  cases t with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

theorem allowedTiles_length : allowedTiles.length = 21 := by decide

theorem allowedTiles_nodup : allowedTiles.Nodup := by decide

theorem mem_allowedTiles_iff (t : Tile) : t ∈ allowedTiles ↔ Allowed t := by
  cases t with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- The count includes exhaustiveness and distinctness, not just list length. -/
theorem exactly_twenty_one :
    ∃ ts : List Tile, ts.Nodup ∧ ts.length = 21 ∧
      ∀ t, t ∈ ts ↔ Allowed t :=
  ⟨allowedTiles, allowedTiles_nodup, allowedTiles_length, mem_allowedTiles_iff⟩

theorem tile_ext {s t : Tile}
    (hc : s.center = t.center) (he : s.east = t.east)
    (hn : s.north = t.north) : s = t := by
  cases s
  cases t
  simp_all

universe u v

abbrev Tiling (V : Type u) := V → Tile

def Admissible (t : Tiling V) : Prop :=
  ∀ x, Allowed (t x)

def Matched (g : Grid V) (t : Tiling V) : Prop :=
  ∀ x, (t x).east = (t (g.next .east x)).center ∧
    (t x).north = (t (g.next .north x)).center

def Valid (g : Grid V) (t : Tiling V) : Prop :=
  Admissible t ∧ Matched g t

def encode (g : Grid V) (c : Config V) : Tiling V :=
  fun x => ⟨c x, c (g.next .east x), c (g.next .north x)⟩

def decode (t : Tiling V) : Config V :=
  fun x => (t x).center

theorem encode_matched (g : Grid V) (c : Config V) :
    Matched g (encode g c) := by
  intro x
  exact ⟨rfl, rfl⟩

theorem encode_admissible_iff_frozen (g : Grid V) (c : Config V) :
    Admissible (encode g c) ↔ Frozen g c := by
  rw [frozen_iff_east_north]
  constructor
  · intro h
    exact ⟨fun x => (h x).1, fun x => (h x).2⟩
  · rintro ⟨he, hn⟩ x
    exact ⟨he x, hn x⟩

theorem encode_valid_iff_frozen (g : Grid V) (c : Config V) :
    Valid g (encode g c) ↔ Frozen g c := by
  constructor
  · intro h
    exact (encode_admissible_iff_frozen g c).mp h.1
  · intro h
    exact ⟨(encode_admissible_iff_frozen g c).mpr h, encode_matched g c⟩

@[simp] theorem decode_encode (g : Grid V) (c : Config V) :
    decode (encode g c) = c := rfl

/-- Edge matching makes every outgoing color recoverable from its neighbor. -/
theorem encode_decode_of_matched (g : Grid V) (t : Tiling V)
    (h : Matched g t) : encode g (decode t) = t := by
  funext x
  apply tile_ext
  · rfl
  · exact (h x).1.symm
  · exact (h x).2.symm

theorem encode_decode_of_valid (g : Grid V) (t : Tiling V)
    (h : Valid g t) : encode g (decode t) = t :=
  encode_decode_of_matched g t h.2

theorem valid_decode_frozen (g : Grid V) (t : Tiling V)
    (h : Valid g t) : Frozen g (decode t) := by
  apply (encode_valid_iff_frozen g (decode t)).mp
  rw [encode_decode_of_valid g t h]
  exact h

/-- Every valid Wang field is the encoding of exactly one frozen traffic field. -/
theorem valid_iff_unique_frozen_encoding (g : Grid V) (t : Tiling V) :
    Valid g t ↔ ∃ c : Config V, Frozen g c ∧ encode g c = t ∧
      ∀ d : Config V, encode g d = t → d = c := by
  constructor
  · intro h
    refine ⟨decode t, valid_decode_frozen g t h, encode_decode_of_valid g t h, ?_⟩
    intro d hd
    have hdecode := congrArg decode hd
    simpa only [decode_encode] using hdecode
  · rintro ⟨c, hfreeze, hc, _⟩
    rw [← hc]
    exact (encode_valid_iff_frozen g c).mpr hfreeze

/-- Recoding commutes with any map preserving both forward neighbors. -/
theorem encode_pullback (gV : Grid V) (gW : Grid W) (f : W → V)
    (hf : ∀ p x, f (gW.next p x) = gV.next p (f x)) (c : Config V) :
    encode gW (fun x => c (f x)) = fun x => encode gV c (f x) := by
  funext x
  apply tile_ext
  · rfl
  · exact congrArg c (hf .east x)
  · exact congrArg c (hf .north x)

theorem decode_pullback (f : W → V) (t : Tiling V) :
    decode (fun x => t (f x)) = fun x => decode t (f x) := rfl

end Traffic.Wang
