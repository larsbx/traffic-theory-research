module train_tests {
  import Train.* from "./Train"

  run emptyStuckTest = assert(stuck(2, 2, List(0, 0, 0, 0)))
  run eastQueueMovesTogetherTest = assert(all {
    half(3, 1, List(1, 1, 0), east) == List(0, 1, 1),
    moves(3, 1, List(1, 1, 0), east) == 2,
  })
  run northQueueMovesTogetherTest = assert(all {
    half(1, 3, List(2, 2, 0), north) == List(0, 2, 2),
    moves(1, 3, List(2, 2, 0), north) == 2,
  })
  run eastOppositeBlockerTest = assert(all {
    half(4, 1, List(1, 1, 2, 0), east) == List(1, 1, 2, 0),
    moves(4, 1, List(1, 1, 2, 0), east) == 0,
  })
  run northOppositeBlockerTest = assert(all {
    half(1, 4, List(2, 2, 1, 0), north) == List(2, 2, 1, 0),
    moves(1, 4, List(2, 2, 1, 0), north) == 0,
  })
  run eastWrapQueueTest = assert(all {
    half(4, 1, List(1, 0, 1, 1), east) == List(1, 1, 0, 1),
    moves(4, 1, List(1, 0, 1, 1), east) == 3,
  })
  run northWrapQueueTest = assert(all {
    half(1, 4, List(2, 0, 2, 2), north) == List(2, 2, 0, 2),
    moves(1, 4, List(2, 0, 2, 2), north) == 3,
  })
  run eastFullRingMovesTest = assert(all {
    half(4, 1, List(1, 1, 1, 1), east) == List(1, 1, 1, 1),
    moves(4, 1, List(1, 1, 1, 1), east) == 4,
    not(stuck(4, 1, List(1, 1, 1, 1))),
  })
  run northFullRingMovesTest = assert(all {
    half(1, 4, List(2, 2, 2, 2), north) == List(2, 2, 2, 2),
    moves(1, 4, List(2, 2, 2, 2), north) == 4,
    not(stuck(1, 4, List(2, 2, 2, 2))),
  })
  run oneCellEastRotatesTest = assert(row(1, 1, 1) == List(1, 1, 1, 1, 1, 1, 1, 0, 0, 0))
  run oneCellNorthRotatesTest = assert(row(1, 1, 2) == List(1, 1, 2, 2, 2, 2, 0, 1, 1, 0))
  run thinTorusOwnDirectionRingsTest = assert(all {
    moves(1, 4, List(1, 0, 1, 1), east) == 3,
    moves(4, 1, List(2, 0, 2, 2), north) == 3,
  })
  run quietPhaseIsNotStuckTest = assert(all {
    moves(2, 2, List(2, 0, 0, 0), east) == 0,
    moves(2, 2, List(2, 0, 0, 0), north) == 1,
    not(stuck(2, 2, List(2, 0, 0, 0))),
  })
  run fixedOccupancyIsNotStuckTest = assert(all {
    full(2, 2, List(1, 1, 1, 1)) == List(1, 1, 1, 1),
    moves(2, 2, List(1, 1, 1, 1), east) == 4,
    not(stuck(2, 2, List(1, 1, 1, 1))),
  })
  run phaseOrderMattersTest = assert(all {
    encode(full(2, 2, decode(2, 2, 5))) == 21,
    encode(half(2, 2, half(2, 2, decode(2, 2, 5), north), east)) == 19,
  })
  run mixedStuckBoardTest = assert(all {
    stuck(2, 2, List(1, 2, 2, 1)),
    full(2, 2, List(1, 2, 2, 1)) == List(1, 2, 2, 1),
  })
  run longQueuePropagationTest = assert(all {
    half(7, 1, List(1, 1, 1, 1, 1, 1, 0), east) == List(0, 1, 1, 1, 1, 1, 1),
    moves(7, 1, List(1, 1, 1, 1, 1, 1, 0), east) == 6,
    half(1, 7, List(2, 2, 2, 2, 2, 2, 0), north) == List(0, 2, 2, 2, 2, 2, 2),
  })
  run separatePhaseMovementCountsTest = assert(
    row(2, 2, 7) == List(2, 2, 7, 7, 55, 55, 0, 1, 1, 0))
  // All 3,720 boards over the 14 positive rectangles with area <= 6.
  run allRectanglesThroughSixCellsTest = assert(
    1.to(6).forall(w => 1.to(6 / w).forall(h =>
      0.to(3^(w*h) - 1).forall(code => invariant(w, h, code)))))
}
