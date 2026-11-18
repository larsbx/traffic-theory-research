// Nondeterministic initial board; the subsequent BML update is deterministic.
// This concrete module uses a 3x2 torus. The pure module supports other sizes.
module bml_model {
  import bml.* from "./bml"

  pure val WIDTH = 3
  pure val HEIGHT = 2
  var board: Board
  var phase: int
  var previousBoard: Board
  var previousPhase: int
  var initialEast: int
  var initialNorth: int
  var initialVacant: int
  var initiallyFrozen: bool
  var tick: int

  action initialize(b: Board, p: int): bool =
    all {
      validBoard(b, WIDTH, HEIGHT),
      PHASES.contains(p),
      board' = b,
      phase' = p,
      previousBoard' = b,
      previousPhase' = opposite(p),
      initialEast' = count(b, 1),
      initialNorth' = count(b, 2),
      initialVacant' = count(b, 0),
      initiallyFrozen' = frozen(b, WIDTH, HEIGHT),
      tick' = 0,
    }

  action init = {
    nondet b = allBoards(WIDTH, HEIGHT).oneOf()
    nondet p = PHASES.oneOf()
    initialize(b, p)
  }

  action step = all {
    board' = halfStep(board, WIDTH, HEIGHT, phase),
    phase' = opposite(phase),
    previousBoard' = board,
    previousPhase' = phase,
    initialEast' = initialEast,
    initialNorth' = initialNorth,
    initialVacant' = initialVacant,
    initiallyFrozen' = initiallyFrozen,
    tick' = tick + 1,
  }

  val typeInvariant = validBoard(board, WIDTH, HEIGHT) and PHASES.contains(phase)
  val speciesConserved = count(board, 1) == initialEast
    and count(board, 2) == initialNorth and count(board, 0) == initialVacant
  val phaseAlternates = phase == opposite(previousPhase)
  val initiallyFrozenStaysFrozen = initiallyFrozen implies frozen(board, WIDTH, HEIGHT)
  val frozenIsAbsorbing = tick > 0 and frozen(previousBoard, WIDTH, HEIGHT)
    implies board == previousBoard
  val wangEquivalent = validMatching(encodeTiles(board, WIDTH, HEIGHT), WIDTH, HEIGHT)
    == frozen(board, WIDTH, HEIGHT)
  val safety = typeInvariant and speciesConserved and phaseAlternates
    and initiallyFrozenStaysFrozen and frozenIsAbsorbing and wangEquivalent

  run frozenPhaseToggleTest =
    initialize([1, 2, 1, 2, 1, 2], 1)
      .then(step)
      .expect(safety and phase == 2 and board == [1, 2, 1, 2, 1, 2] and tick == 1)
  run emptyPhaseToggleTest =
    initialize([0, 0, 0, 0, 0, 0], 2)
      .then(step)
      .expect(safety and phase == 1 and board == [0, 0, 0, 0, 0, 0] and tick == 1)
  run bothPhasesUpdateTest =
    initialize([1, 0, 0, 2, 0, 0], 1)
      .then(step)
      .expect(safety and phase == 2 and board == [0, 1, 0, 2, 0, 0])
      .then(step)
      .expect(safety and phase == 1 and board == [2, 1, 0, 0, 0, 0] and tick == 2)
  run frozenPersistsAcrossCycleTest =
    initialize([1, 2, 1, 2, 1, 2], 2)
      .then(step).then(step)
      .expect(safety and phase == 2 and board == [1, 2, 1, 2, 1, 2] and tick == 2)
}
