// TRAIN dynamics: move a whole same-species queue when its head sees a gap;
// rotate a full same-species directional ring. All reads use the old board.
// Codes: 0 empty, 1 east, 2 north; index = x + width*y, y increases north.
// Positive dimensions, legal boards, and species 1 or 2 are preconditions.
module Train {
  type Board = List[int]

  pure val empty = 0
  pure val east = 1
  pure val north = 2
  pure val species = Set(east, north)

  pure def cells(w: int, h: int): List[int] = range(0, w*h)
  pure def sites(w: int, h: int): Set[int] = 0.to(w*h - 1)
  pure def period(w: int, h: int, phase: int): int = if (phase == east) w else h
  pure def opposite(phase: int): int = 3 - phase
  pure def forward(w: int, h: int, phase: int, i: int, distance: int): int =
    if (phase == east) (i / w)*w + (i % w + distance) % w
    else ((i / w + distance) % h)*w + i % w
  pure def front(w: int, h: int, phase: int, i: int): int =
    forward(w, h, phase, i, 1)
  pure def behind(w: int, h: int, phase: int, i: int): int =
    forward(w, h, phase, i, period(w, h, phase) - 1)

  pure def legal(w: int, h: int, b: Board): bool =
    w > 0 and h > 0 and b.length() == w*h
      and b.indices().forall(i => Set(empty, east, north).contains(b[i]))
  pure def decode(w: int, h: int, code: int): Board =
    cells(w, h).foldl(List(), (b, i) => b.append((code / (3^i)) % 3))
  pure def encode(b: Board): int =
    range(0, b.length()).foldl(0, (code, i) => code + b[i]*(3^i))
  pure def count(b: Board, cell: int): int = b.indices().filter(i => b[i] == cell).size()

  pure def initialMovers(w: int, h: int, b: Board, phase: int): Set[int] =
    sites(w, h).filter(i => b[i] == phase and b[front(w, h, phase, i)] == empty)
  pure def fullRing(w: int, h: int, b: Board, phase: int): Set[int] =
    sites(w, h).filter(i =>
      0.to(period(w, h, phase) - 1).forall(k => b[forward(w, h, phase, i, k)] == phase))

  // One pass propagates eligibility backwards by one cell. period-1 passes
  // suffice on the directional ring; the full-ring branch has no empty head.
  pure def movers(w: int, h: int, b: Board, phase: int): Set[int] = {
    val queues = range(0, period(w, h, phase) - 1).foldl(
      initialMovers(w, h, b, phase), (moving, _pass) =>
        moving.union(sites(w, h).filter(i =>
          b[i] == phase and moving.contains(front(w, h, phase, i)))))
    queues.union(fullRing(w, h, b, phase))
  }
  pure def moves(w: int, h: int, b: Board, phase: int): int = movers(w, h, b, phase).size()

  // Incoming cars take priority: a queue car may both leave its old cell and
  // receive the car behind. This also preserves occupancy while rings rotate.
  pure def half(w: int, h: int, b: Board, phase: int): Board = {
    val moving = movers(w, h, b, phase)
    cells(w, h).foldl(List(), (out, i) => out.append(
      if (moving.contains(behind(w, h, phase, i))) phase
      else if (moving.contains(i)) empty
      else b[i]))
  }
  pure def full(w: int, h: int, b: Board): Board =
    half(w, h, half(w, h, b, east), north)

  // Stuck means zero movement in BOTH independently evaluated phases.
  // An unchanged board is insufficient: full rings may have positive movement.
  pure def stuck(w: int, h: int, b: Board): bool =
    moves(w, h, b, east) == 0 and moves(w, h, b, north) == 0

  // Independent local characterization: a same-species queue ends at the other
  // species before it encounters a vacancy. A full own-species ring fails it.
  pure def queueBlocked(w: int, h: int, b: Board, phase: int, i: int): bool =
    1.to(period(w, h, phase)).exists(k =>
      b[forward(w, h, phase, i, k)] == opposite(phase)
      and 1.to(k - 1).forall(j => b[forward(w, h, phase, i, j)] == phase))
  pure def allQueuesBlocked(w: int, h: int, b: Board): bool =
    sites(w, h).forall(i => b[i] == empty or queueBlocked(w, h, b, b[i], i))

  pure def invariant(w: int, h: int, code: int): bool = {
    val b = decode(w, h, code)
    val e = half(w, h, b, east)
    val n = half(w, h, b, north)
    val f = full(w, h, b)
    val em = moves(w, h, b, east)
    val nm = moves(w, h, b, north)
    val cnm = moves(w, h, e, north)
    all {
      legal(w, h, b), legal(w, h, e), legal(w, h, n), legal(w, h, f),
      encode(b) == code,
      Set(empty, east, north).forall(c =>
        count(e, c) == count(b, c) and count(n, c) == count(b, c)
          and count(f, c) == count(b, c)),
      em >= 0, em <= count(b, east),
      nm >= 0, nm <= count(b, north),
      cnm >= 0, cnm <= count(b, north),
      species.forall(p => movers(w, h, b, p).forall(i =>
        b[i] == p and (b[front(w, h, p, i)] == empty
          or movers(w, h, b, p).contains(front(w, h, p, i))))),
      stuck(w, h, b) == allQueuesBlocked(w, h, b),
      stuck(w, h, b) == (em + cnm == 0),
      stuck(w, h, b) implies e == b and n == b and f == b and stuck(w, h, f),
      (stuck(w, h, b) and count(b, empty) < w*h) implies
        w > 1 and h > 1 and w*h - count(b, empty) >= w + h,
    }
  }

  // Shared ten-column protocol. North is an independent input half-step;
  // cycleNorthMoves is measured after the east half-step.
  pure def row(w: int, h: int, code: int): List[int] = {
    val b = decode(w, h, code)
    val e = half(w, h, b, east)
    List(w, h, code, encode(e), encode(half(w, h, b, north)),
      encode(full(w, h, b)), moves(w, h, b, east), moves(w, h, b, north),
      moves(w, h, e, north), if (stuck(w, h, b)) 1 else 0)
  }
  // This extra internal flag certifies the actual boards. Equal ternary codes
  // alone cannot exclude illegal digits such as [4,0] in place of [1,1].
  pure def checkedRow(w: int, h: int, code: int): List[int] =
    row(w, h, code).append(if (invariant(w, h, code)) 1 else 0)
  pure def checkedRows(w: int, h: int, lo: int, hi: int): List[List[int]] =
    range(lo, hi).foldl(List(), (rows, code) => rows.append(checkedRow(w, h, code)))
}
