// Figures for the paper, from data/experiments.json (no plotting dependencies): SVG small
// multiples of frozen share and flow against on-street density, per place and traffic law.
import { readFile, writeFile } from 'node:fs/promises';

const d = JSON.parse(await readFile(new URL('data/experiments.json', import.meta.url)));
const mean = (a) => a.reduce((x, y) => x + y, 0) / a.length;
const sd = (a) => Math.sqrt(mean(a.map((x) => (x - mean(a)) ** 2)));
const LAW_STYLE = {
  'CITY CODE': { color: '#1f4e9c', dash: '' },
  'FREE TURNS': { color: '#2e8b57', dash: '6 3' },
  'BLOCK THE BOX': { color: '#d07a00', dash: '2 3' },
  'BML LIGHTS': { color: '#b0172b', dash: '8 3 2 3' },
};
const NAMES = { midtown: 'Midtown, New York', eixample: 'Eixample, Barcelona', grachten: 'Grachtengordel, Amsterdam', etoile: 'Étoile, Paris', bank: 'Bank, London', shibuya: 'Shibuya, Tokyo' };
const ORDER = ['midtown', 'eixample', 'grachten', 'etoile', 'bank', 'shibuya'];
const font = 'font-family="Latin Modern Roman, CMU Serif, Times New Roman, serif"';

const panel = (place, key, yMax, yLabel, ox, oy, w, h) => {
  const [l, r, t, b] = [ox + 40, ox + w - 8, oy + 18, oy + h - 30];
  const X = (x) => l + (x / 0.5) * (r - l);
  const Y = (y) => b - (y / yMax) * (b - t);
  const out = [`<text x="${(l + r) / 2}" y="${oy + 12}" text-anchor="middle" font-size="11" ${font} font-style="italic">${NAMES[place.id]}</text>`,
    `<rect x="${l}" y="${t}" width="${r - l}" height="${b - t}" fill="none" stroke="#000" stroke-width="0.6"/>`];
  for (const xv of [0, 0.1, 0.2, 0.3, 0.4, 0.5])
    out.push(`<line x1="${X(xv)}" y1="${b}" x2="${X(xv)}" y2="${b + 3}" stroke="#000" stroke-width="0.6"/><text x="${X(xv)}" y="${b + 13}" text-anchor="middle" font-size="9" ${font}>${xv}</text>`);
  const ticks = yMax <= 1 ? [0, 0.25, 0.5, 0.75, 1].filter((v) => v <= yMax) : [0, yMax / 2, yMax];
  for (const yv of ticks)
    out.push(`<line x1="${l - 3}" y1="${Y(yv)}" x2="${l}" y2="${Y(yv)}" stroke="#000" stroke-width="0.6"/><text x="${l - 5}" y="${Y(yv) + 3}" text-anchor="end" font-size="9" ${font}>${+yv.toFixed(2)}</text>`);
  out.push(`<text x="${(l + r) / 2}" y="${b + 25}" text-anchor="middle" font-size="10" ${font} font-style="italic">ρ</text>`);
  out.push(`<text transform="translate(${ox + 10} ${(t + b) / 2}) rotate(-90)" text-anchor="middle" font-size="10" ${font}>${yLabel}</text>`);
  for (const law of place.laws) {
    const { color, dash } = LAW_STYLE[law.law];
    const pts = law.runs.map((r) => [mean(r.seeds.map((s) => s.rho)), mean(r.seeds.map((s) => s[key])), sd(r.seeds.map((s) => s[key]))]);
    out.push(`<polyline fill="none" stroke="${color}" stroke-width="1.3" stroke-dasharray="${dash}" points="${pts.map(([x, y]) => `${X(x).toFixed(1)},${Y(y).toFixed(1)}`).join(' ')}"/>`);
    for (const [x, y, e] of pts) {
      out.push(`<line x1="${X(x)}" y1="${Y(Math.min(yMax, y + e))}" x2="${X(x)}" y2="${Y(Math.max(0, y - e))}" stroke="${color}" stroke-width="0.8"/>`);
      out.push(`<circle cx="${X(x)}" cy="${Y(y)}" r="2" fill="${color}"/>`);
    }
  }
  return out.join('');
};

const grid = (key, yMax, yLabel) => {
  const [w, h, cols] = [230, 170, 3];
  const places = ORDER.map((id) => d.places.find((p) => p.id === id));
  const legend = Object.entries(LAW_STYLE).map(([name, { color, dash }], i) =>
    `<g transform="translate(${40 + i * 170} ${2 * h + 14})"><line x1="0" y1="0" x2="26" y2="0" stroke="${color}" stroke-width="1.5" stroke-dasharray="${dash}"/><text x="32" y="3.5" font-size="10" ${font}>${name.toLowerCase().replace(/(^|\s)\S/g, (c) => c.toUpperCase()).replace('Bml', 'BML')}</text></g>`).join('');
  const body = places.map((p, i) => panel(p, key, yMax, yLabel, (i % cols) * w, Math.floor(i / cols) * h, w, h)).join('');
  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${cols * w} ${2 * h + 28}" width="${cols * w}" height="${2 * h + 28}">${body}${legend}</svg>`;
};

const jMax = Math.ceil(Math.max(...d.places.flatMap((p) => p.laws.flatMap((l) => l.runs.flatMap((r) => r.seeds.map((s) => s.j))))) * 20) / 20;
await writeFile(new URL('figures/frozen.svg', import.meta.url), grid('frozen', 1, 'frozen share'));
await writeFile(new URL('figures/flow.svg', import.meta.url), grid('j', jMax, 'flow J'));
console.log('figures/frozen.svg, figures/flow.svg; J max', jMax);
