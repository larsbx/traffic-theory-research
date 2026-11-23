// CLASSIC bounded target probing. Every transition calls the actual BML kernel.
// Verdicts: 0=hit, 1=safe recurrent non-target, 2=unresolved.
// A safe recurrence certifies avoidance, not necessarily full movement.
module Absorption {
  import BML as Kernel from "./BML"

  pure val hit = 0
  pure val safe = 1
  pure val unresolved = 2

  pure def population(s: Kernel::State): int = Kernel::count(s, Kernel::east) + Kernel::count(s, Kernel::north)
  pure def jam(w: int, h: int, s: Kernel::State): bool =
    population(s) > 0 and Kernel::blocked(w, h, s)

  pure def orbit(w: int, h: int, initial: Kernel::State, cutoff: int): List[Kernel::State] =
    range(0, cutoff).foldl(List(initial), (history, _round) =>
      history.append(Kernel::step(w, h, history[history.length() - 1])))

  pure def verdict(w: int, h: int, history: List[Kernel::State]): int =
    if (history.length() == 0) unresolved
    else {
      val lastIndex = history.length() - 1
      val last = history[lastIndex]
      if (jam(w, h, last)) hit
      else if (history.indices().exists(i => i < lastIndex and history[i] == last)) safe
      else unresolved
    }

  // Check actual cells, including the east intermediate state. Encoding alone
  // would miss illegal aliases such as List(4,0) and the legal List(1,1).
  pure def stateCheck(w: int, h: int, s: Kernel::State): bool =
    if (not(Kernel::legal(w, h, s))) false
    else {
      val t = Kernel::transition(w, h, s)
      all {
        Kernel::legal(w, h, t.east), Kernel::legal(w, h, t.next),
        Kernel::count(t.east, Kernel::east) == Kernel::count(s, Kernel::east),
        Kernel::count(t.east, Kernel::north) == Kernel::count(s, Kernel::north),
        Kernel::count(t.east, Kernel::empty) == Kernel::count(s, Kernel::empty),
        Kernel::count(t.next, Kernel::east) == Kernel::count(s, Kernel::east),
        Kernel::count(t.next, Kernel::north) == Kernel::count(s, Kernel::north),
        Kernel::count(t.next, Kernel::empty) == Kernel::count(s, Kernel::empty),
        t.eastMoves >= 0, t.eastMoves <= Kernel::count(s, Kernel::east),
        t.northMoves >= 0, t.northMoves <= Kernel::count(s, Kernel::north),
        (t.eastMoves + t.northMoves == 0) == Kernel::blocked(w, h, s),
        (t.next == s) == Kernel::blocked(w, h, s),
        jam(w, h, s) == (population(s) > 0 and t.next == s),
        jam(w, h, s) == (population(s) > 0 and t.eastMoves + t.northMoves == 0),
        not(jam(w, h, s)) or jam(w, h, t.next),
      }
    }

  pure def orbitCheck(w: int, h: int, initial: Kernel::State,
                      history: List[Kernel::State], cutoff: int): bool =
    if (cutoff < 0 or history.length() != cutoff + 1 or not(Kernel::legal(w, h, initial))) false
    else all {
      history[0] == initial,
      history.indices().forall(i => stateCheck(w, h, history[i])),
      history.indices().forall(i =>
        Kernel::count(history[i], Kernel::east) == Kernel::count(initial, Kernel::east) and
        Kernel::count(history[i], Kernel::north) == Kernel::count(initial, Kernel::north)),
      range(0, cutoff).indices().forall(i => Kernel::step(w, h, history[i]) == history[i + 1]),
    }

  // The sixth field is an internal invariant flag. Adapters must require one
  // before exposing the five public fields.
  pure def checkedRow(w: int, h: int, index: int, cutoff: int): List[int] =
    if (w < 1 or h < 1 or index < 0 or index >= 3^(w*h) or cutoff < 0)
      List(index, cutoff, 0, unresolved, 0, 0)
    else {
      val initial = Kernel::decode(w, h, index)
      val history = orbit(w, h, initial, cutoff)
      List(index, cutoff, Kernel::encode(history[cutoff]), verdict(w, h, history), population(initial),
        if (orbitCheck(w, h, initial, history, cutoff)) 1 else 0)
    }

  pure def checkedRange(w: int, h: int, lo: int, hi: int, cutoff: int): List[List[int]] =
    range(lo, hi).foldl(List(), (out, index) => out.append(checkedRow(w, h, index, cutoff)))

  pure def checkedIndices(w: int, h: int, codes: List[int], cutoff: int): List[List[int]] =
    codes.foldl(List(), (out, index) => out.append(checkedRow(w, h, index, cutoff)))

  run cutoffZeroTest = assert(all {
    checkedRow(1, 1, 0, 0) == List(0, 0, 0, unresolved, 0, 1),
    checkedRow(1, 1, 1, 0) == List(1, 0, 1, hit, 1, 1),
  })

  run emptyRecurrenceTest = assert(all {
    checkedRow(2, 2, 0, 1) == List(0, 1, 0, safe, 0, 1),
    checkedRow(2, 2, 0, 3) == List(0, 3, 0, safe, 0, 1),
  })

  run initialJamTest = assert(all {
    checkedRow(2, 2, 80, 0) == List(80, 0, 80, hit, 4, 1),
    checkedRow(2, 2, 80, 4) == List(80, 4, 80, hit, 4, 1),
  })

  run lateJamTest = assert(all {
    checkedRow(4, 2, 3858, 1)[2] == 4312,
    checkedRow(4, 2, 3858, 1)[3] == unresolved,
    checkedRow(4, 2, 3858, 3)[2] == 2048,
    checkedRow(4, 2, 3858, 3)[3] == hit,
    checkedRow(4, 2, 3858, 4)[3] == hit,
  })

  run movingIntermediateTest = assert({
    val initial = Kernel::decode(4, 2, 3860)
    val t = Kernel::transition(4, 2, initial)
    all {
      checkedRow(4, 2, 3860, 1)[3] == unresolved,
      checkedRow(4, 2, 3860, 2)[2] == 3860,
      checkedRow(4, 2, 3860, 2)[3] == safe,
      t.eastMoves + t.northMoves > 0,
      t.eastMoves + t.northMoves < population(initial),
    }
  })

  run instantFreeIsUnresolvedTest = assert(all {
    checkedRow(3, 1, 1, 1) == List(1, 1, 3, unresolved, 1, 1),
    checkedRow(3, 1, 1, 3) == List(1, 3, 1, safe, 1, 1),
  })

  run malformedStatesTest = assert(all {
    Kernel::encode(List(4, 0)) == Kernel::encode(List(1, 1)),
    not(stateCheck(2, 1, List(4, 0))),
    not(orbitCheck(2, 1, List(4, 0), List(List(4, 0)), 0)),
    not(orbitCheck(2, 1, List(1), List(List(1)), 0)),
    not(orbitCheck(2, 1, List(1, 0), List(), 0)),
    checkedRow(2, 1, 9, 0)[5] == 0,
    checkedRow(2, 1, 0, -1)[5] == 0,
  })

  run cutoffMonotonicityTest = assert(0.to(80).forall(index =>
    0.to(3).forall(cutoff => {
      val a = checkedRow(2, 2, index, cutoff)[3]
      val b = checkedRow(2, 2, index, cutoff + 1)[3]
      (a == unresolved or a == b)
    })))

  run horizontalDelayTest = assert({
    val history = orbit(5, 1, List(Kernel::east, Kernel::east, Kernel::east, Kernel::empty, Kernel::empty), 1)
    history[1][0] == Kernel::east and history[1][1] == Kernel::east and
      not(Kernel::canMove(5, 1, history[1], Kernel::east, 0))
  })

  run vacantCutBecomesJamTest = assert(all {
    checkedRow(4, 4, 18626220, 1) == List(18626220, 1, 15826840, hit, 8, 1),
    List(0, 1, 2, 14, 10, 11, 8, 4).indices().forall(i =>
      Kernel::decode(4, 4, 18626220)[List(0, 1, 2, 14, 10, 11, 8, 4)[i]] == Kernel::empty),
  })
}
