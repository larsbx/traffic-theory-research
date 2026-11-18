// Seeded PRNG (mulberry32). A generator is a closure over a seed; `seed()` exports the
// state so callers can thread it through pure state transitions.
export const makeRng = (seed) => {
  let s = seed >>> 0;
  const float = () => {
    s = (s + 0x6d2b79f5) >>> 0;
    let t = s;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const int = (n) => Math.floor(float() * n);
  const pick = (xs) => xs[int(xs.length)];
  const weighted = (xs, ws) => {
    const total = ws.reduce((a, b) => a + b, 0);
    let r = float() * total;
    for (let i = 0; i < xs.length; i++) if ((r -= ws[i]) < 0) return xs[i];
    return xs[xs.length - 1];
  };
  return { float, int, pick, weighted, seed: () => s };
};
