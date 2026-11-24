import BML.Net

/-!
# Instances of the traffic net

* `bml`: the CLASSIC kernel. Its even and odd ticks are exactly the east and
  north half-steps of `BML.halfStep` (`bml_even`, `bml_odd`).
* `mixed`: a grid on which a chosen set of intersections are roundabouts and
  the rest keep the BML signal, with or without a link cell on every street
  segment. Its gridlock lemma MX-0 is the generic `stuck_iff` (`mixed_stuck_iff`).
-/
namespace BML.Net

variable {α : Type}

/-- BML as a net: both species go straight, the merge order is irrelevant
because the parity gates never admit both species in one tick. -/
def bml (east north : Direction α) : Net α Species where
  next k p := some (match k with | .east => east.next p | .north => north.next p)
  prev k c := some (match k with | .east => east.prev c | .north => north.prev c)
  prev_iff := by
    intro k p c
    cases k <;> simp only [Option.some.injEq] <;> constructor <;> intro h <;> subst h <;>
      simp [east.next_prev, east.prev_next, north.next_prev, north.prev_next]
  order _ := [.east, .north]
  gate t k _ := match k with | .east => t % 2 == 0 | .north => t % 2 == 1

/-- Forget the option wrapper: the board of `BML.Kernel`. -/
def encode (s : Config α Species) : BML.Config α := fun p =>
  match s p with
  | none => .empty
  | some k => k.cell

theorem bml_even (east north : Direction α) (t : Nat) (s : Config α Species) :
    encode (step (bml east north) (2 * t) s) = halfStep east .east (encode s) := by
  funext p
  cases hp : s p with
  | none =>
    cases hq : s (east.prev p) with
    | none => simp [encode, step, winner, leaves, wants, bml, halfStep, hp, hq, Species.cell]
    | some j => cases j <;>
        simp [encode, step, winner, leaves, wants, bml, halfStep, hp, hq, Species.cell]
  | some k =>
    cases k with
    | north => simp [encode, step, winner, leaves, bml, halfStep, hp, Species.cell]
    | east =>
      cases hn : s (east.next p) with
      | none =>
        simp [encode, step, winner, leaves, wants, bml, halfStep, hp, hn, Species.cell,
          east.prev_next]
      | some j => cases j <;>
          simp [encode, step, winner, leaves, bml, halfStep, hp, hn, Species.cell]

theorem bml_odd (east north : Direction α) (t : Nat) (s : Config α Species) :
    encode (step (bml east north) (2 * t + 1) s) = halfStep north .north (encode s) := by
  funext p
  cases hp : s p with
  | none =>
    cases hq : s (north.prev p) with
    | none => simp [encode, step, winner, leaves, wants, bml, halfStep, hp, hq, Species.cell]
    | some j => cases j <;>
        simp [encode, step, winner, leaves, wants, bml, halfStep, hp, hq, Species.cell]
  | some k =>
    cases k with
    | east => simp [encode, step, winner, leaves, bml, halfStep, hp, Species.cell]
    | north =>
      cases hn : s (north.next p) with
      | none =>
        simp [encode, step, winner, leaves, wants, bml, halfStep, hp, hn, Species.cell,
          north.prev_next]
      | some j => cases j <;>
          simp [encode, step, winner, leaves, bml, halfStep, hp, hn, Species.cell]

/-- Two ticks of the net are one full BML step. -/
theorem bml_round (east north : Direction α) (t : Nat) (s : Config α Species) :
    encode (step (bml east north) (2 * t + 1) (step (bml east north) (2 * t) s)) =
      BML.step east north (encode s) := by
  rw [bml_odd, bml_even]
  rfl

/-! ## Signals and roundabouts on one grid -/

/-- The cells of the mixed grid at intersection `p`: its junction cell, the
roundabout's two private quadrants, and the two links leaving it. Quadrants
are unused where there is no roundabout, links where the layout has none. -/
inductive Site (α : Type) where
  | junction (p : α) | quadE (p : α) | quadN (p : α) | linkE (p : α) | linkN (p : α)
  deriving DecidableEq

structure Layout (α : Type) where
  east : Direction α
  north : Direction α
  /-- Is this intersection a roundabout? -/
  ring : α → Bool
  /-- Is there a private link cell on every street segment? -/
  link : Bool

namespace Layout

variable (L : Layout α)

/-- First cell of an eastbound car arriving at intersection `q`. -/
def intoE (q : α) : Site α := if L.ring q then .quadE q else .junction q

/-- Cell behind `intoE q` on the east route. -/
def fromE (q : α) : Site α := if L.link then .linkE (L.east.prev q) else .junction (L.east.prev q)

/-- Cell after the junction (or the north quadrant) of `p` on the north route. -/
def outN (p : α) : Site α := if L.link then .linkN p else .junction (L.north.next p)

/-- Last cell of a northbound car at intersection `p`, before any link. -/
def lastN (p : α) : Site α := if L.ring p then .quadN p else .junction p

def next : Species → Site α → Option (Site α)
  | .east, .junction p => some (if L.link then .linkE p else L.intoE (L.east.next p))
  | .east, .linkE p => if L.link then some (L.intoE (L.east.next p)) else none
  | .east, .quadE p => if L.ring p then some (.junction p) else none
  | .north, .junction p => some (if L.ring p then .quadN p else L.outN p)
  | .north, .quadN p => if L.ring p then some (L.outN p) else none
  | .north, .linkN p => if L.link then some (.junction (L.north.next p)) else none
  | _, _ => none

def prev : Species → Site α → Option (Site α)
  | .east, .junction c => some (if L.ring c then .quadE c else L.fromE c)
  | .east, .quadE c => if L.ring c then some (L.fromE c) else none
  | .east, .linkE c => if L.link then some (.junction c) else none
  | .north, .junction c =>
      some (if L.link then .linkN (L.north.prev c) else L.lastN (L.north.prev c))
  | .north, .quadN c => if L.ring c then some (.junction c) else none
  | .north, .linkN c => if L.link then some (L.lastN c) else none
  | _, _ => none

theorem prev_iff (k : Species) (p c : Site α) : L.prev k c = some p ↔ L.next k p = some c := by
  have he : ∀ a b : α, L.east.prev a = b ↔ a = L.east.next b := fun a b =>
    ⟨fun h => by rw [← h, L.east.next_prev], fun h => by rw [h, L.east.prev_next]⟩
  have hn : ∀ a b : α, L.north.prev a = b ↔ a = L.north.next b := fun a b =>
    ⟨fun h => by rw [← h, L.north.next_prev], fun h => by rw [h, L.north.prev_next]⟩
  cases k <;> cases p <;> cases c <;>
    simp only [prev, next, intoE, fromE, outN, lastN] <;>
    (repeat' split) <;> (try simp_all)
  all_goals first
    | exact eq_comm
    | (intro h; subst h; simp_all [L.north.prev_next])
    | (constructor <;> intro h <;> subst h <;> simp_all)

end Layout

/-- The mixed grid as a net. A signal junction admits east cars on even ticks
and north cars on odd ticks; everything else is always open. At a roundabout
the circulating east car goes first (yield on entry). -/
def mixed (L : Layout α) : Net (Site α) Species where
  next := L.next
  prev := L.prev
  prev_iff := L.prev_iff
  order _ := [.east, .north]
  gate t k c :=
    match c with
    | .junction q => L.ring q || (match k with | .east => t % 2 == 0 | .north => t % 2 == 1)
    | _ => true

theorem mixed_complete (L : Layout α) : Complete (mixed L) := by
  intro k _ _ _
  cases k <;> simp [mixed]

theorem mixed_fair (L : Layout α) : Fair (mixed L) 2 := by
  intro t k c
  cases c with
  | junction q =>
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · cases k
      · exact ⟨0, by omega, by simp [mixed, h]⟩
      · exact ⟨1, by omega, by simp [mixed]; omega⟩
    · cases k
      · exact ⟨1, by omega, by simp [mixed]; omega⟩
      · exact ⟨0, by omega, by simp [mixed, h]⟩
  | _ => exact ⟨0, by omega, rfl⟩

/-- **Lemma MX-0, kernel-checked**, for every roundabout set and with or
without links: every car's next cell is occupied iff no car moves in two
consecutive ticks. -/
theorem mixed_stuck_iff (L : Layout α) (s : Config (Site α) Species) (t : Nat) :
    Stuck (mixed L) s ↔ step (mixed L) t s = s ∧ step (mixed L) (t + 1) s = s := by
  rw [stuck_iff (mixed_complete L) (by omega : 0 < 2) (mixed_fair L) t]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by omega), h 1 (by omega)⟩
  · intro h d hd
    have : d = 0 ∨ d = 1 := by omega
    rcases this with rfl | rfl
    · simpa using h.1
    · exact h.2

end BML.Net
