// Exact finite BML dynamics: east first, then north; both phases synchronous.
// Cell i = y * width + x, state index = sum(cell[i] * 3^i).
// Precondition for all transitions: width,height >= 1, legal state of that size.
// Pure definitions are executable specifications. The finite tests below do not
// establish an unbounded theorem or a probabilistic critical density.
module BML {
  type State = List[int]
  type Transition = { east: State, next: State, eastMoves: int, northMoves: int }

  pure val empty = 0
  pure val east = 1
  pure val north = 2

  pure def cells(w: int, h: int): List[int] = range(0, w * h)
  pure def decode(w: int, h: int, index: int): State =
    cells(w, h).foldl(List(), (s, i) => s.append((index / (3^i)) % 3))
  pure def encode(s: State): int =
    range(0, s.length()).foldl(0, (n, i) => n + s[i] * (3^i))

  pure def front(w: int, h: int, species: int, i: int): int =
    if (species == east) (i / w) * w + (i % w + 1) % w
    else ((i / w + 1) % h) * w + i % w
  pure def behind(w: int, h: int, species: int, i: int): int =
    if (species == east) (i / w) * w + (i % w + w - 1) % w
    else ((i / w + h - 1) % h) * w + i % w

  pure def canMove(w: int, h: int, s: State, species: int, i: int): bool =
    s[i] == species and s[front(w, h, species, i)] == empty

  // Every output reads the same phase input s. Reading a partially updated
  // state here would change the model to asynchronous traffic.
  pure def half(w: int, h: int, s: State, species: int): State =
    cells(w, h).foldl(List(), (out, i) => out.append(
      if (canMove(w, h, s, species, i)) empty
      else if (canMove(w, h, s, species, behind(w, h, species, i))) species
      else s[i]))
  pure def moves(w: int, h: int, s: State, species: int): int =
    s.indices().filter(i => canMove(w, h, s, species, i)).size()
  pure def count(s: State, species: int): int =
    s.indices().filter(i => s[i] == species).size()

  pure def transition(w: int, h: int, s: State): Transition = {
    val a = half(w, h, s, east)
    { east: a, next: half(w, h, a, north),
      eastMoves: moves(w, h, s, east), northMoves: moves(w, h, a, north) }
  }
  pure def step(w: int, h: int, s: State): State = transition(w, h, s).next
  pure def blocked(w: int, h: int, s: State): bool =
    s.indices().forall(i => s[i] == empty or s[front(w, h, s[i], i)] != empty)
  pure def legal(w: int, h: int, s: State): bool =
    w >= 1 and h >= 1 and s.length() == w * h and
    s.indices().forall(i => s[i] >= empty and s[i] <= north)

  // A nonempty occupied core whose cars all point to another core site.
  // This is CLASSIC snapshot-vacancy blocking, not TRAIN movement.
  pure def closedCore(w: int, h: int, s: State, core: Set[int]): bool =
    if (not(legal(w, h, s)) or core.size() == 0 or
        not(core.forall(i => s.indices().contains(i)))) false
    else core.forall(i => s[i] != empty and
      core.contains(front(w, h, s[i], i)))

  pure def coversRowsAndColumns(w: int, h: int, core: Set[int]): bool =
    0.to(h - 1).forall(y => core.exists(i => i / w == y)) and
    0.to(w - 1).forall(x => core.exists(i => i % w == x))

  pure def captureBound(w: int, h: int, s: State): int =
    count(s, east) * (w - 1) + count(s, north) * (h - 1)

  // Bounded executable check, not a universal proof: replay the actual
  // transition, preserve the core at both phases, and count every car move.
  pure def captureCheck(w: int, h: int, s: State, core: Set[int]): bool =
    if (not(closedCore(w, h, s, core)) or
        not(coversRowsAndColumns(w, h, core))) false
    else {
      val bound = captureBound(w, h, s)
      val result = range(0, bound).foldl(
        { state: s, total: 0, held: true }, (acc, unused) => {
          val t = transition(w, h, acc.state)
          { state: t.next, total: acc.total + t.eastMoves + t.northMoves,
            held: acc.held and core.forall(i =>
              t.east[i] == s[i] and t.next[i] == s[i]) }
        })
      result.held and result.total <= bound and blocked(w, h, result.state)
    }

  pure def row(w: int, h: int, index: int): List[int] = {
    val t = transition(w, h, decode(w, h, index))
    List(index, encode(t.east), encode(t.next), t.eastMoves, t.northMoves)
  }
  pure def rows(w: int, h: int, lo: int, hi: int): List[List[int]] =
    range(lo, hi).foldl(List(), (out, i) => out.append(row(w, h, i)))

  pure def invariant(w: int, h: int, index: int): bool = {
    val s = decode(w, h, index)
    val t = transition(w, h, s)
    all {
      legal(w, h, s), legal(w, h, t.east), legal(w, h, t.next),
      encode(s) == index,
      count(t.east, east) == count(s, east),
      count(t.east, north) == count(s, north),
      count(t.next, east) == count(s, east),
      count(t.next, north) == count(s, north),
      t.eastMoves >= 0, t.eastMoves <= count(s, east),
      t.northMoves >= 0, t.northMoves <= count(s, north),
      (t.next == s) == blocked(w, h, s),
      (t.eastMoves + t.northMoves == 0) == blocked(w, h, s),
      count(s, empty) > 0 or blocked(w, h, s),
    }
  }

  // Keep the five-column cross-language protocol while also checking the
  // actual internal states. Base-three encoding alone cannot certify legality:
  // for example List(1, 1) and the illegal List(4, 0) both encode as 4.
  // The adapter requires this extra flag to be 1 and strips it before CSV output.
  pure def checkedRow(w: int, h: int, index: int): List[int] =
    row(w, h, index).append(if (invariant(w, h, index)) 1 else 0)
  pure def checkedRows(w: int, h: int, lo: int, hi: int): List[List[int]] =
    range(lo, hi).foldl(List(), (out, i) => out.append(checkedRow(w, h, i)))

  var active: bool
  action init = active' = true

  // All states in these tests are quantified explicitly, not randomly sampled.
  run exhaustiveOneCellTest = init.expect(0.to(2).forall(i => invariant(1, 1, i)))
  run exhaustiveThinToriTest = init.expect(1.to(4).forall(k =>
    0.to(3^k - 1).forall(i => invariant(1, k, i) and invariant(k, 1, i))))
  run exhaustiveTwoByTwoTest = init.expect(0.to(80).forall(i => invariant(2, 2, i)))

  run phaseOrderTest = init.expect(all {
    row(2, 2, 5) == List(5, 5, 21, 0, 1),
    // North-first has successor 19; this control detects a phase reversal.
    encode(half(2, 2, half(2, 2, decode(2, 2, 5), north), east)) == 19,
  })
  run synchronousPhaseTest = init.expect(all {
    // E E . on a ring moves only its second car. Sequentially rescanning a
    // changed state would allow an extra move or move one car twice.
    row(3, 1, 4) == List(4, 10, 10, 1, 0),
    row(1, 3, 8) == List(8, 8, 20, 0, 1),
  })
  run emptyAndFullTest = init.expect(all {
    row(2, 3, 0) == List(0, 0, 0, 0, 0),
    row(2, 3, 728) == List(728, 728, 728, 0, 0),
    row(1, 1, 1) == List(1, 1, 1, 0, 0),
    row(1, 1, 2) == List(2, 2, 2, 0, 0),
  })
  // This model has species, not individual car identities. The labeled-car
  // assertion is established separately by the Lean/Python witness work.
  run nonmonotonicOccupancyWitnessTest = init.expect(all {
    row(4, 2, 3858) == List(3858, 3832, 4312, 1, 1),
    row(4, 2, 3860) == List(3860, 3860, 4340, 0, 1),
    row(4, 2, 4340) == List(4340, 4340, 3860, 0, 1),
    blocked(4, 2, step(4, 2, step(4, 2, step(4, 2, decode(4, 2, 3858))))),
  })

  // The core winds once in each direction, while the two non-core cars
  // still move during capture. Row-major cycle: 0,3,6,7,1,2.
  pure val captureCore3 = Set(0, 3, 6, 7, 1, 2)
  run closedCorePersistenceTest = init.expect(all {
    closedCore(3, 3, decode(3, 3, 5738), captureCore3),
    closedCore(3, 3, transition(3, 3, decode(3, 3, 5738)).east, captureCore3),
    closedCore(3, 3, step(3, 3, decode(3, 3, 5738)), captureCore3),
    not(closedCore(3, 3, decode(3, 3, 5738), Set())),
    not(closedCore(3, 3, decode(3, 3, 5738), Set(-1))),
    not(closedCore(3, 3, decode(3, 3, 5738), Set(9))),
    not(closedCore(3, 3, decode(3, 3, 5738), Set(0, 3, 6, 7, 1, 8))),
  })
  run mixedCoreCaptureTest = init.expect(all {
    coversRowsAndColumns(3, 3, captureCore3),
    captureBound(3, 3, decode(3, 3, 5738)) == 16,
    not(blocked(3, 3, decode(3, 3, 5738))),
    not(blocked(3, 3, step(3, 3, decode(3, 3, 5738)))),
    blocked(3, 3, step(3, 3, step(3, 3, decode(3, 3, 5738)))),
    captureCheck(3, 3, decode(3, 3, 5738), captureCore3),
  })
  run monochromaticCoreControlTest = init.expect({
    val s = List(east, east, east, east, empty, empty)
    all {
      closedCore(3, 2, s, Set(0, 1, 2)),
      not(coversRowsAndColumns(3, 2, Set(0, 1, 2))),
      not(captureCheck(3, 2, s, Set(0, 1, 2))),
      step(3, 2, step(3, 2, step(3, 2, s))) == s,
      transition(3, 2, s).eastMoves == 1,
    }
  })
}
