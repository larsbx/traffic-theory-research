/* Exact jam counts for a gap of the 2×W torus: g consecutive non-plug columns between two plugs.
 *
 * A gap is two rows of g cells, x = 0 … g−1 west to east. East of x = g−1 is a plug column,
 * whose two cells are occupied forever; west of x = 0 is another plug, which emits nothing.
 * Every column holds at most one N car, otherwise it would be a plug. CLASSIC rule:
 *   E half-step: an E car at x moves to x+1 iff x+1 < g and that cell is empty;
 *   N half-step: an N car moves to the other row of its column iff that cell is empty.
 * Plugs never change and no car crosses a plug column, so on the torus every gap evolves
 * independently of the others, by exactly these rules (bml.thin, Lemma 1).
 *
 * The gap "jams" iff its orbit reaches a fixed point, found exactly by Floyd cycle detection.
 * Output: one line per car count k = 0 … 2g: jams among the gap states that contain a lone
 * column. (States without one all jam; there are C(2g, k) of them.)
 * usage: gap_jam g [lo hi]   (optional prefix-task range, to split long runs; GAP_JAM_CHECK=1
 *                             instead runs a brute-force cross-check of both deciders)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct { uint32_t e0, e1, n0, n1; } S;
static int G;
static uint32_t FULL;

static inline S step(S s) {
    uint32_t o0 = s.e0 | s.n0, o1 = s.e1 | s.n1;
    uint32_t m0 = s.e0 & ~(o0 >> 1) & (FULL >> 1);   /* east cell exists and is empty */
    uint32_t m1 = s.e1 & ~(o1 >> 1) & (FULL >> 1);
    s.e0 = (s.e0 & ~m0) | (m0 << 1);
    s.e1 = (s.e1 & ~m1) | (m1 << 1);
    o0 = s.e0 | s.n0; o1 = s.e1 | s.n1;
    uint32_t a = s.n0 & ~o1, b = s.n1 & ~o0;           /* N toggles rows */
    s.n0 = (s.n0 & ~a) | b;
    s.n1 = (s.n1 & ~b) | a;
    return s;
}
static inline int eq(S a, S b) { return a.e0 == b.e0 && a.e1 == b.e1 && a.n0 == b.n0 && a.n1 == b.n1; }

static int jams_floyd(S s) {
    S slow = step(s), fast = step(slow);
    while (!eq(slow, fast)) { slow = step(slow); fast = step(step(fast)); }
    return eq(step(slow), slow);
}

/* Exact and faster. (i) Necessary: #E ≥ distance of the westmost lone column (gap condition).
 * (ii) No lone column: jams (Lemma 4). (iii) Otherwise simulate. After two consecutive rounds
 * with no E move, no E car ever moves again: in the second round every E target is a wall, a
 * stuck E car, or an N car whose other cell holds such a car, and none of these ever moves.
 * The gap then jams iff that state is fixed. E moves are finite, so this terminates. */
static int jams(S s) {
    uint32_t lone = s.n0 | s.n1;
    if (!lone) return 1;
    int dmax = G - __builtin_ctz(lone);
    if (__builtin_popcount(s.e0) + __builtin_popcount(s.e1) < dmax) return 0;
    int quiet = 0;
    for (;;) {
        S t = step(s);
        if (t.e0 == s.e0 && t.e1 == s.e1) { if (++quiet == 2) return eq(step(t), t); }
        else quiet = 0;
        s = t;
    }
}

/* column states: (row0, row1) in {0, E, N}^2 minus (N, N) */
static const int C0[8] = {0, 1, 2, 0, 1, 2, 0, 1};
static const int C1[8] = {0, 0, 0, 1, 1, 1, 2, 2};
static const int NE[8] = {0, 1, 0, 1, 2, 1, 0, 1};       /* E cars in the column */
static const int NC[8] = {0, 1, 1, 1, 2, 2, 1, 2};       /* cars in the column */
static const int LONE[8] = {0, 0, 1, 0, 0, 1, 1, 1};

/* Depth-first over columns west to east. The first lone column met fixes d_max = G − x; a branch
 * is cut once even two E cars per remaining column cannot reach d_max (gap condition). States
 * with no lone column are not visited: they all jam (Lemma 4) and are counted in closed form. */
static void dfs(S s, int x, int e, int cars, int dmax, uint64_t *j) {
    if (dmax && e + 2 * (G - x) < dmax) return;
    if (x == G) { if (dmax && e >= dmax) j[cars] += jams(s); return; }
    for (int v = 0; v < 8; v++) {
        if (!dmax && !LONE[v] && x == G - 1) continue;          /* would end with no lone column */
        S t = s;
        uint32_t bit = 1u << x;
        if (C0[v] == 1) t.e0 |= bit; else if (C0[v] == 2) t.n0 |= bit;
        if (C1[v] == 1) t.e1 |= bit; else if (C1[v] == 2) t.n1 |= bit;
        dfs(t, x + 1, e + NE[v], cars + NC[v], dmax ? dmax : (LONE[v] ? G - x : 0), j);
    }
}

int main(int argc, char **argv) {
    G = atoi(argv[1]);
    FULL = (G == 32) ? ~0u : ((1u << G) - 1);
    if (getenv("GAP_JAM_CHECK")) {                /* brute force over all 8^G states, both deciders */
        uint64_t total = 1, J[65] = {0};
        for (int i = 0; i < G; i++) total *= 8;
        for (uint64_t code = 0; code < total; code++) {
            S s = {0, 0, 0, 0}; uint64_t c = code; int k = 0, lone = 0;
            for (int x = 0; x < G; x++, c >>= 3) {
                int v = c & 7;
                if (C0[v] == 1) s.e0 |= 1u << x; else if (C0[v] == 2) s.n0 |= 1u << x;
                if (C1[v] == 1) s.e1 |= 1u << x; else if (C1[v] == 2) s.n1 |= 1u << x;
                k += NC[v]; lone |= LONE[v];
            }
            int r = jams_floyd(s);
            if (r != jams(s)) { fprintf(stderr, "mismatch at %llu\n", (unsigned long long)code); return 1; }
            if (lone) J[k] += r;
        }
        for (int k = 0; k <= 2 * G; k++) printf("%d %llu\n", k, (unsigned long long)J[k]);
        return 0;
    }
    int depth = G < 4 ? G : 4;                    /* parallelise over the first `depth` columns */
    int tasks = 1 << (3 * depth);
    /* Row swap is a symmetry (jam status and car count are invariant). Visit a prefix only if it
     * is ≤ its row-swapped image, and count it twice if it is strictly smaller. Optional argv
     * [lo, hi) restricts the prefix range, so a long run can be split into chunks. */
    static const int SWAP[8] = {0, 3, 6, 1, 4, 7, 2, 5};
    int lo = argc > 3 ? atoi(argv[2]) : 0, hi = argc > 3 ? atoi(argv[3]) : tasks;
    static uint64_t J[65];
    #pragma omp parallel
    {
        uint64_t j[65] = {0};
        #pragma omp for schedule(dynamic, 1)
        for (int t = lo; t < hi; t++) {
            int sw = 0;
            for (int x = 0, c = t; x < depth; x++, c >>= 3) sw |= SWAP[c & 7] << (3 * x);
            if (sw < t) continue;
            uint64_t mult = sw == t ? 1 : 2;
            uint64_t jt[65] = {0};
            S s = {0, 0, 0, 0}; int e = 0, cars = 0, dmax = 0, c = t, skip = 0;
            for (int x = 0; x < depth; x++, c >>= 3) {
                int v = c & 7;
                if (C0[v] == 1) s.e0 |= 1u << x; else if (C0[v] == 2) s.n0 |= 1u << x;
                if (C1[v] == 1) s.e1 |= 1u << x; else if (C1[v] == 2) s.n1 |= 1u << x;
                e += NE[v]; cars += NC[v];
                if (!dmax && LONE[v]) dmax = G - x;
            }
            if (depth == G && !dmax) skip = 1;
            if (!skip) dfs(s, depth, e, cars, dmax, jt);
            for (int k = 0; k <= 2 * G; k++) j[k] += mult * jt[k];
        }
        #pragma omp critical
        for (int k = 0; k <= 2 * G; k++) J[k] += j[k];
    }
    /* output: k, jams among states WITH a lone column (the rest all jam: C(2G, k) states) */
    for (int k = 0; k <= 2 * G; k++) printf("%d %llu\n", k, (unsigned long long)J[k]);
    return 0;
}
