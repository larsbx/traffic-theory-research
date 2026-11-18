// Cell codes: 0 vacant, 1 eastbound, 2 northbound.
// Phase codes: 1 east, 2 north. Positive width/height are required.
// Coordinates use row-major index x + width*y with y increasing northward.
module traffic {
  type Board = List[int]
  type Tile = { here: int, east: int, north: int }
  type Tiles = List[Tile]

  pure val CELLS = Set(0, 1, 2)
  pure val PHASES = Set(1, 2)

  pure def sites(w: int, h: int): Set[int] = 0.to(w*h - 1)
  pure def validBoard(b: Board, w: int, h: int): bool =
    w > 0 and h > 0 and b.length() == w*h
      and b.indices().forall(i => CELLS.contains(b.nth(i)))

  pure def eastIndex(i: int, w: int): int =
    (i / w)*w + (i + 1) % w
  pure def westIndex(i: int, w: int): int =
    (i / w)*w + (i + w - 1) % w
  pure def northIndex(i: int, w: int, h: int): int = (i + w) % (w*h)
  pure def southIndex(i: int, w: int, h: int): int = (i + w*(h - 1)) % (w*h)

  pure def nextIndex(i: int, w: int, h: int, phase: int): int =
    if (phase == 1) eastIndex(i, w) else northIndex(i, w, h)
  pure def previousIndex(i: int, w: int, h: int, phase: int): int =
    if (phase == 1) westIndex(i, w) else southIndex(i, w, h)
  pure def opposite(phase: int): int = 3 - phase

  // Eligibility is evaluated entirely against the original board.
  pure def eligible(b: Board, w: int, h: int, phase: int, i: int): bool =
    b.nth(i) == phase and b.nth(nextIndex(i, w, h, phase)) == 0
  pure def moves(b: Board, w: int, h: int, phase: int): Set[int] =
    sites(w, h).filter(i => eligible(b, w, h, phase, i))

  pure def halfStep(b: Board, w: int, h: int, phase: int): Board =
    range(0, w*h).foldl([], (out, i) => out.append(
      if (eligible(b, w, h, phase, i)) 0
      else if (b.nth(i) == 0 and b.nth(previousIndex(i, w, h, phase)) == phase) phase
      else b.nth(i)
    ))

  pure def cycle(b: Board, w: int, h: int, firstPhase: int): Board =
    halfStep(halfStep(b, w, h, firstPhase), w, h, opposite(firstPhase))

  pure def frozen(b: Board, w: int, h: int): bool =
    sites(w, h).forall(i =>
      (b.nth(i) == 1 implies b.nth(eastIndex(i, w)) != 0)
      and (b.nth(i) == 2 implies b.nth(northIndex(i, w, h)) != 0))

  pure def count(b: Board, cell: int): int =
    b.foldl(0, (n, c) => n + (if (c == cell) 1 else 0))

  // Little-endian ternary board code: cell at index i has weight 3^i.
  pure def decodeBoard(code: int, w: int, h: int): Board =
    range(0, w*h).foldl([], (out, i) => out.append((code / (3^i)) % 3))
  pure def encodeBoard(b: Board): int =
    range(0, b.length()).foldl(0, (n, i) => n + b.nth(i)*(3^i))
  pure def allBoards(w: int, h: int): Set[Board] =
    0.to(3^(w*h) - 1).map(code => decodeBoard(code, w, h))

  pure def allowedTile(t: Tile): bool =
    CELLS.contains(t.here) and CELLS.contains(t.east) and CELLS.contains(t.north)
      and (t.here == 1 implies t.east != 0)
      and (t.here == 2 implies t.north != 0)
  pure val allTiles: Set[Tile] =
    tuples(CELLS, CELLS, CELLS).map(t => { here: t._1, east: t._2, north: t._3 })
  pure val allowedTiles = allTiles.filter(t => allowedTile(t))

  pure def encodeTiles(b: Board, w: int, h: int): Tiles =
    range(0, w*h).foldl([], (out, i) => out.append({
      here: b.nth(i),
      east: b.nth(eastIndex(i, w)),
      north: b.nth(northIndex(i, w, h))
    }))
  pure def decodeTiles(ts: Tiles): Board =
    ts.foldl([], (out, t) => out.append(t.here))
  pure def validMatching(ts: Tiles, w: int, h: int): bool =
    w > 0 and h > 0 and ts.length() == w*h
      and sites(w, h).forall(i =>
        allowedTile(ts.nth(i))
        and ts.nth(i).east == ts.nth(eastIndex(i, w)).here
        and ts.nth(i).north == ts.nth(northIndex(i, w, h)).here)

  // Exhaustive finite-domain property: all boards, both phases.
  pure def boardLaws(b: Board, w: int, h: int): bool =
    validBoard(b, w, h)
    and decodeBoard(encodeBoard(b), w, h) == b
    and decodeTiles(encodeTiles(b, w, h)) == b
    and (validMatching(encodeTiles(b, w, h), w, h) == frozen(b, w, h))
    and (frozen(b, w, h) == (moves(b, w, h, 1).size() == 0 and moves(b, w, h, 2).size() == 0))
    and PHASES.forall(phase => {
      val after = halfStep(b, w, h, phase)
      validBoard(after, w, h)
      and CELLS.forall(cell => count(after, cell) == count(b, cell))
      and (after == b iff moves(b, w, h, phase).size() == 0)
      and (frozen(b, w, h) implies after == b and frozen(after, w, h))
      and (cycle(b, w, h, phase) == b iff frozen(b, w, h))
    })
  pure def exhaustiveLaws(w: int, h: int): bool =
    allBoards(w, h).forall(b => boardLaws(b, w, h))

  // Each row is [width,height,inputCode,phase,outputCode,nextPhase,
  //              frozenBit,matchingBit,decodedCode,allowedTileCount].
  // This is evaluated by Quint, not a separate JavaScript implementation.
  pure def transitionRows(w: int, h: int): List[List[int]] =
    range(0, 3^(w*h)).foldl([], (rows, code) => {
      val b = decodeBoard(code, w, h)
      range(1, 3).foldl(rows, (out, phase) => out.append([
        w, h, code, phase, encodeBoard(halfStep(b, w, h, phase)), opposite(phase),
        if (frozen(b, w, h)) 1 else 0,
        if (validMatching(encodeTiles(b, w, h), w, h)) 1 else 0,
        encodeBoard(decodeTiles(encodeTiles(b, w, h))), allowedTiles.size()
      ]))
    })
}
