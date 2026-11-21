/* Monte Carlo of CLASSIC BML on the 2×W torus (2 rows, W ≤ 64 columns) under the iid law
 * (1 − p, p/2, p/2). Each sample is classified exactly: Floyd cycle detection, and it jams iff
 * the cycle it reaches is a nonempty fixed point. No time horizon.
 * Row r is a pair of W-bit masks; EAST moves +x along rows, NORTH swaps rows (the 2-cell axis),
 * each half-step reading occupancy from its own start (CLASSIC).
 * usage: thin_mc W p samples seed  ->  "jams samples"                                          */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef struct { uint64_t e[2], n[2]; } S;
static int W; static uint64_t FULL;
static inline uint64_t rotl1(uint64_t m){ return ((m<<1)|(m>>(W-1)))&FULL; }   /* +x */
static inline uint64_t rotr1(uint64_t m){ return ((m>>1)|(m<<(W-1)))&FULL; }   /* -x */
static inline S step(S s){
  for(int r=0;r<2;r++){ uint64_t occ=s.e[r]|s.n[r]; uint64_t me=s.e[r]&~rotr1(occ);
    s.e[r]=(s.e[r]&~me)|rotl1(me); }
  uint64_t o0=s.e[0]|s.n[0], o1=s.e[1]|s.n[1];
  uint64_t m0=s.n[0]&~o1, m1=s.n[1]&~o0;          /* N in row r moves to row 1-r */
  s.n[0]=(s.n[0]&~m0)|m1; s.n[1]=(s.n[1]&~m1)|m0; return s; }
static inline int eq(S a,S b){return a.e[0]==b.e[0]&&a.e[1]==b.e[1]&&a.n[0]==b.n[0]&&a.n[1]==b.n[1];}
static int jam(S s){ if(!(s.e[0]|s.e[1]|s.n[0]|s.n[1])) return 0;
  S a=step(s),b=step(step(s)); while(!eq(a,b)){a=step(a);b=step(step(b));}
  return eq(step(a),a); }
static uint64_t rs; static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
int main(int c,char**v){ W=atoi(v[1]); double p=atof(v[2]); long n=atol(v[3]); rs=0x9E3779B97F4A7C15ULL^atol(v[4]);
  FULL=W==64?~0ULL:((1ULL<<W)-1); uint64_t th=(uint64_t)(p*18446744073709551615.0), half=th/2; long J=0;
  for(long i=0;i<n;i++){ S s={{0,0},{0,0}};
    for(int r=0;r<2;r++) for(int x=0;x<W;x++){ uint64_t u=rnd(); if(u<half) s.e[r]|=1ULL<<x; else if(u<th) s.n[r]|=1ULL<<x; }
    J+=jam(s); }
  printf("%ld %ld\n",J,n); return 0; }
