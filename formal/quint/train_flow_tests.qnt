// Fixed finite witnesses for the full-cycle diagonal clock and TRAIN flow.
// Exhaustive low-population square graphs are checked by train_flow_check.py.
module train_flow_tests {
  import Train.* from "./Train"

  pure def diagonal(n: int, i: int): int = (i % n + i / n) % n
  // One clock tick is a COMPLETE east-then-north cycle.
  pure def corrected(n: int, i: int, time: int): int =
    (diagonal(n, i) + n - time % n) % n
  pure def correctedSupport(n: int, b: Board, time: int): Set[int] =
    b.indices().filter(i => b[i] != empty).map(i => corrected(n, i, time))
  pure def colorSupport(n: int, b: Board, phase: int, time: int): Set[int] =
    b.indices().filter(i => b[i] == phase).map(i => corrected(n, i, time))
  pure def emptyPairs(n: int, b: Board, time: int): Set[int] = {
    val support = correctedSupport(n, b, time)
    0.to(n - 1).filter(i => not(support.contains(i)) and not(support.contains((i+1) % n)))
  }
  pure def population(b: Board): int = count(b, east) + count(b, north)
  pure def allMove(w: int, h: int, b: Board): bool =
    moves(w, h, b, east) == count(b, east)
      and moves(w, h, half(w, h, b, east), north) == count(b, north)
  pure def orbit(w: int, h: int, b: Board, steps: int): List[Board] =
    range(0, steps).foldl(List(b), (out, _time) =>
      out.append(full(w, h, out[out.length() - 1])))

  run completeCycleClockTest = {
    val b = decode(3, 3, 1)
    assert(correctedSupport(3, full(3, 3, b), 1) == correctedSupport(3, b, 0)
      and correctedSupport(3, b, 0) == Set(0))
  }
  run wrongHalfStepClockRejectedTest = {
    val b = decode(3, 3, 1)
    assert(correctedSupport(3, full(3, 3, b), 2) == Set(2)
      and correctedSupport(3, full(3, 3, b), 2) != correctedSupport(3, b, 0))
  }
  run wholeTrainQueueClockTest = {
    val b = decode(5, 5, 4)
    assert(moves(5, 5, b, east) == 2 and allMove(5, 5, b)
      and colorSupport(5, full(5, 5, b), east, 1) == Set(0, 1))
  }
  // E(0,0) enters (1,0), blocking N(1,4) in the resulting board.
  // The standalone north phase is unblocked, so it is the wrong cycle count.
  run northReadsEastResultTest = {
    val b = decode(5, 5, 1 + 2*(3^21))
    assert(moves(5, 5, b, north) == 1
      and moves(5, 5, half(5, 5, b, east), north) == 0
      and not(allMove(5, 5, b)))
  }
  run blockedNorthDiagonalFallsTest = {
    val b = decode(5, 5, 1 + 2*(3^21))
    assert(colorSupport(5, b, north, 0) == Set(0)
      and colorSupport(5, full(5, 5, b), east, 1) == Set(0)
      and colorSupport(5, full(5, 5, b), north, 1) == Set(4))
  }
  // At the equality boundary 2m=N, an individual empty pair may disappear.
  // This is not a forward-invariant-pair assertion.
  run emptyGapPairCanDisappearTest = {
    val b = decode(4, 4, 3^12 + 2*(3^13))
    assert(2*population(b) == 4 and emptyPairs(4, b, 0) == Set(1)
      and emptyPairs(4, full(4, 4, b), 1) == Set())
  }
  run fixedOccupancyIsNotFullMovementTest = {
    val b = List(1, 2, 2, 1)
    assert(full(2, 2, b) == b and population(b) == 4 and not(allMove(2, 2, b)))
  }
  run rotatingRingIsFullMovementTest = {
    val b = List(1)
    assert(full(1, 1, b) == b and moves(1, 1, b, east) == 1 and allMove(1, 1, b))
  }
  run emptyOrbitIsVacuouslyFullMovementTest =
    assert(allMove(1, 1, List(0)) and stuck(1, 1, List(0)))
  run rectangularLowDensityCounterexampleTest = {
    val first = full(5, 7, decode(5, 7, 7))
    val cycle = orbit(5, 7, first, 15)
    assert(2*population(first) < 5 and encode(first) == 1459
      and cycle[15] == first and 0.to(14).exists(t => not(allMove(5, 7, cycle[t]))))
  }
}
