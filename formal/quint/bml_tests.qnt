module bml_tests {
  import traffic.* from "./traffic"

  run emptyFrozenTest = assert(frozen([0, 0, 0, 0], 2, 2))
  run allOccupiedFrozenTest =
    assert(allBoards(2, 2).filter(b => count(b, 0) == 0).forall(b =>
      frozen(b, 2, 2) and cycle(b, 2, 2, 1) == b))
  run eastWrapTest = assert(halfStep([0, 0, 1, 0, 0, 0], 3, 2, 1) == [1, 0, 0, 0, 0, 0])
  run northWrapTest = assert(halfStep([0, 0, 2, 0], 2, 2, 2) == [2, 0, 0, 0])
  run inactiveSpeciesTest = assert(halfStep([2, 0, 0, 0], 2, 2, 1) == [2, 0, 0, 0])
  run blockedQueueSnapshotTest =
    assert(halfStep([1, 1, 0, 0, 0, 0], 3, 2, 1) == [1, 0, 1, 0, 0, 0])
  run noSequentialCascadeTest =
    assert(halfStep([1, 1, 0, 0, 0, 0], 3, 2, 1) != [0, 1, 1, 0, 0, 0])
  run vacantTargetRequirementTest =
    assert(halfStep([1, 2, 0, 0], 2, 2, 1) == [1, 2, 0, 0])
  run truncatedPathIsNotFrozenTest =
    assert(not(frozen([1, 2, 0, 0, 0, 0], 3, 2)))
  run truncatedPathEndpointMovesTest =
    assert(halfStep([1, 2, 0, 0, 0, 0], 3, 2, 2) == [1, 0, 0, 0, 2, 0])
  run quietPhaseDoesNotMeanFrozenTest =
    assert(halfStep([2, 0, 0, 0], 2, 2, 1) == [2, 0, 0, 0]
      and not(frozen([2, 0, 0, 0], 2, 2)))
  run phaseOrderMattersTest =
    assert(cycle([1, 0, 0, 2], 2, 2, 1) != cycle([1, 0, 0, 2], 2, 2, 2))

  run wangHas21TypesTest = assert(allowedTiles.size() == 21)
  run eastVacancyTileRejectedTest = assert(not(allowedTile({here: 1, east: 0, north: 1})))
  run northVacancyTileRejectedTest = assert(not(allowedTile({here: 2, east: 1, north: 0})))
  run eastNonemptyTileAcceptedTest = assert(allowedTile({here: 1, east: 2, north: 0}))
  run mismatchedWangEdgeRejectedTest = {
    val ts = encodeTiles([1, 2, 1, 2], 2, 2)
    assert(not(validMatching(ts.replaceAt(0, {here: 1, east: 1, north: 1}), 2, 2)))
  }
  run wangDecodeEncodeFrozenTest =
    assert(allBoards(3, 2).filter(b => frozen(b, 3, 2)).forall(b => {
      val ts = encodeTiles(b, 3, 2)
      validMatching(ts, 3, 2) and encodeTiles(decodeTiles(ts), 3, 2) == ts
    }))

  // These are universal finite enumerations, not randomized simulation samples.
  run exhaustive2x2Test = assert(exhaustiveLaws(2, 2))
  run exhaustive3x2Test = assert(exhaustiveLaws(3, 2))
  run exhaustive2x3Test = assert(exhaustiveLaws(2, 3))
  run exhaustive1x1Test = assert(exhaustiveLaws(1, 1))
  run exhaustive1x2Test = assert(exhaustiveLaws(1, 2))
  run exhaustive2x1Test = assert(exhaustiveLaws(2, 1))
  run transitionTableCoverageTest =
    assert(transitionRows(2, 2).length() == 162 and transitionRows(3, 2).length() == 1458)
}
