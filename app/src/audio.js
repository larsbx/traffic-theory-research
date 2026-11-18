// Square-wave blips. Starts only after a user gesture (browser autoplay rules).
let ctx = null;
let muted = false;
export const setMuted = (m) => { muted = m; };
export const isMuted = () => muted;
export const unlock = () => {
  try { ctx ??= new (window.AudioContext || window.webkitAudioContext)(); ctx.resume?.(); } catch { ctx = null; }
};
const tone = (f, t0, dur, type = 'square', vol = 0.05) => {
  const o = ctx.createOscillator(), g = ctx.createGain();
  o.type = type; o.frequency.setValueAtTime(f, ctx.currentTime + t0);
  g.gain.setValueAtTime(vol, ctx.currentTime + t0);
  g.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + t0 + dur);
  o.connect(g).connect(ctx.destination);
  o.start(ctx.currentTime + t0); o.stop(ctx.currentTime + t0 + dur + 0.02);
};
const SONGS = {
  incident: [[523, 0, 0.06], [784, 0.07, 0.08]],
  captured: [[392, 0, 0.05], [523, 0.05, 0.05]],
  core: [[523, 0, 0.06], [659, 0.06, 0.06], [784, 0.12, 0.06], [1047, 0.18, 0.12]],
  hit: [[440, 0, 0.12], [330, 0.12, 0.12], [220, 0.24, 0.25]],
  breakdown: [[180, 0, 0.1, 'sawtooth', 0.03]],
  clear: [[523, 0, 0.1], [659, 0.1, 0.1], [784, 0.2, 0.1], [1047, 0.3, 0.3]],
  over: [[392, 0, 0.2], [311, 0.2, 0.2], [262, 0.4, 0.5]],
};
export const play = (name) => {
  if (muted || !ctx || !SONGS[name]) return;
  SONGS[name].forEach(([f, t, d, type, v]) => tone(f, t, d, type, v));
};
