/* Exhaustive CLASSIC BML classification on a W×H torus (W·H ≤ 31), quotiented by translations.
 *
 * A state is a pair of disjoint bitmasks (E, N), with cell i = x + W*y. One round is the
 * east half-step, then the north half-step, each reading occupancy from the start of its
 * half-step (CLASSIC). Each translation orbit is enumerated once: the representative has the
 * least code (E << 32 | N) among its W·H translates. It is weighted by its orbit size
 * W·H / |stabilizer|. Its terminal cycle is found with Floyd's algorithm and then walked
 * once, so there is no time horizon and nothing is stored:
 *   JAM   = nonempty and no move on the cycle;
 *   FREE  = empty, or every car moves in every round of the cycle;
 *   MIXED = otherwise.
 * Output: one line per car count n, "n jam free mixed" (weighted counts of all states).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int W, H, C;
static uint32_t FULL, LAST_COL, FIRST_COL;
static uint32_t ROTX_LOW[32];            /* cells with x < W - dx */

static inline uint32_t rot_x(uint32_t m, int dx) {          /* translate by +dx in x */
    if (!dx) return m;
    return ((m & ROTX_LOW[dx]) << dx) | ((m & ~ROTX_LOW[dx] & FULL) >> (W - dx));
}
static inline uint32_t rot_y(uint32_t m, int dy) {          /* translate by +dy in y */
    if (!dy) return m;
    return ((m << (W * dy)) & FULL) | (m >> (W * (H - dy)));
}
static inline uint32_t east_of(uint32_t m) { return rot_x(m, 1); }          /* {p+e : p∈m} */
static inline uint32_t west_of(uint32_t m) { return rot_x(m, W - 1); }      /* {p−e : p∈m} */
static inline uint32_t north_of(uint32_t m) { return rot_y(m, 1); }
static inline uint32_t south_of(uint32_t m) { return rot_y(m, H - 1); }

typedef struct { uint32_t e, n; } S;

static inline S step(S s, int *moves) {
    uint32_t occ = s.e | s.n;
    uint32_t me = s.e & ~west_of(occ);                      /* east cell empty */
    uint32_t e2 = (s.e & ~me) | east_of(me);
    uint32_t occ2 = e2 | s.n;
    uint32_t mn = s.n & ~south_of(occ2);                    /* north cell empty */
    uint32_t n2 = (s.n & ~mn) | north_of(mn);
    *moves = __builtin_popcount(me) + __builtin_popcount(mn);
    return (S){e2, n2};
}

static inline int eq(S a, S b) { return a.e == b.e && a.n == b.n; }

/* 0 = JAM, 1 = FREE, 2 = MIXED */
static int classify(S s) {
    int n = __builtin_popcount(s.e | s.n), mv;
    if (!n) return 1;
    S slow = step(s, &mv), fast = step(step(s, &mv), &mv);
    while (!eq(slow, fast)) { slow = step(slow, &mv); fast = step(step(fast, &mv), &mv); }
    int mn = 1 << 30, mx = 0;
    S c = slow;
    do { c = step(c, &mv); if (mv < mn) mn = mv; if (mv > mx) mx = mv; } while (!eq(c, slow));
    if (mx == 0) return 0;
    return mn == n ? 1 : 2;
}

/* Returns orbit size if s is the least-code translate, else 0. */
static inline int canonical_weight(S s) {
    uint64_t code = ((uint64_t)s.e << 32) | s.n;
    int stab = 0;
    for (int dy = 0; dy < H; dy++) {
        uint32_t ey = rot_y(s.e, dy), ny = rot_y(s.n, dy);
        for (int dx = 0; dx < W; dx++) {
            uint64_t t = ((uint64_t)rot_x(ey, dx) << 32) | rot_x(ny, dx);
            if (t < code) return 0;
            if (t == code) stab++;
        }
    }
    return C / stab;
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: classify W H\n"); return 2; }
    W = atoi(argv[1]); H = atoi(argv[2]); C = W * H;
    if (W < 1 || H < 1 || C > 31) { fprintf(stderr, "need 1 <= W*H <= 31\n"); return 2; }
    FULL = (C == 32) ? 0xffffffffu : ((1u << C) - 1);
    for (int dx = 0; dx < W; dx++) {
        uint32_t m = 0;
        for (int y = 0; y < H; y++) for (int x = 0; x < W - dx; x++) m |= 1u << (x + W * y);
        ROTX_LOW[dx] = m;
    }
    (void)LAST_COL; (void)FIRST_COL;
    uint64_t total[33][3];
    memset(total, 0, sizeof total);
    uint64_t nocc = 1ull << C;
    #pragma omp parallel
    {
        uint64_t local[33][3];
        memset(local, 0, sizeof local);
        #pragma omp for schedule(dynamic, 64)
        for (uint64_t occ = 0; occ < nocc; occ++) {
            uint32_t M = (uint32_t)occ;
            int n = __builtin_popcount(M);
            uint32_t sub = M;
            for (;;) {                                       /* E ranges over submasks of M */
                S s = {sub, M ^ sub};
                int wgt = canonical_weight(s);
                if (wgt) local[n][classify(s)] += (uint64_t)wgt;
                if (!sub) break;
                sub = (sub - 1) & M;
            }
        }
        #pragma omp critical
        for (int k = 0; k <= C; k++) for (int c = 0; c < 3; c++) total[k][c] += local[k][c];
    }
    for (int k = 0; k <= C; k++)
        printf("%d %llu %llu %llu\n", k, (unsigned long long)total[k][0],
               (unsigned long long)total[k][1], (unsigned long long)total[k][2]);
    return 0;
}
