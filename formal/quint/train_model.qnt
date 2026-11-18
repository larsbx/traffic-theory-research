// Concrete TRAIN phase machine: every 3x2 board and either initial phase.
module train_model {
  import Train.* from "./Train"
  pure val WIDTH = 3
  pure val HEIGHT = 2
  var board: Board
  var phase: int
  var tick: int
  var previousBoard: Board
  var previousPhase: int
  var moved: int
  var initialEast: int
  var initialNorth: int
  var initiallyStuck: bool

  action initialize(b: Board, p: int): bool = all {
    legal(WIDTH, HEIGHT, b), species.contains(p),
    board' = b, phase' = p, tick' = 0,
    previousBoard' = b, previousPhase' = opposite(p), moved' = 0,
    initialEast' = count(b, east), initialNorth' = count(b, north),
    initiallyStuck' = stuck(WIDTH, HEIGHT, b),
  }
  action init = {
    nondet code = 0.to(3^(WIDTH*HEIGHT) - 1).oneOf()
    nondet p = species.oneOf()
    initialize(decode(WIDTH, HEIGHT, code), p)
  }
  action step = all {
    board' = half(WIDTH, HEIGHT, board, phase),
    phase' = opposite(phase), tick' = tick + 1,
    previousBoard' = board, previousPhase' = phase,
    moved' = moves(WIDTH, HEIGHT, board, phase),
    initialEast' = initialEast, initialNorth' = initialNorth,
    initiallyStuck' = initiallyStuck,
  }
  val safety = all {
    legal(WIDTH, HEIGHT, board), species.contains(phase), tick >= 0,
    phase == opposite(previousPhase),
    count(board, east) == initialEast, count(board, north) == initialNorth,
    moved >= 0,
    tick > 0 implies moved <= count(previousBoard, previousPhase),
    tick > 0 and stuck(WIDTH, HEIGHT, previousBoard) implies board == previousBoard and moved == 0,
    initiallyStuck implies stuck(WIDTH, HEIGHT, board),
  }

  run ringMovementAdvancesClockTest =
    initialize(List(1, 1, 1, 1, 1, 1), east).then(step)
      .expect(safety and board == List(1, 1, 1, 1, 1, 1) and moved == 6
        and phase == north and tick == 1 and not(stuck(WIDTH, HEIGHT, board)))
  run emptyStepTogglesPhaseTest =
    initialize(List(0, 0, 0, 0, 0, 0), north).then(step)
      .expect(safety and moved == 0 and phase == east and tick == 1)
  run stuckStepTogglesPhaseTest =
    initialize(List(1, 2, 1, 2, 1, 2), east).then(step).then(step)
      .expect(safety and board == List(1, 2, 1, 2, 1, 2) and moved == 0
        and phase == east and tick == 2)
  run bothPhasesConserveSpeciesTest =
    initialize(List(1, 1, 0, 2, 0, 0), east).then(step)
      .expect(safety and board == List(0, 1, 1, 2, 0, 0) and moved == 2 and phase == north)
      .then(step)
      .expect(safety and board == List(2, 1, 1, 0, 0, 0) and moved == 1 and phase == east)
  run quietActivePhaseTogglesTest =
    initialize(List(2, 0, 0, 0, 0, 0), east).then(step)
      .expect(safety and moved == 0 and phase == north and not(stuck(WIDTH, HEIGHT, board)))
      .then(step)
      .expect(safety and moved == 1 and board == List(0, 0, 0, 2, 0, 0) and phase == east)
}
