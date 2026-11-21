// OpenStreetMap-backed simulation API. Transport-free: `handle(method, url)` → { status, body },
// so server.mjs, tests and any other host can mount it. OSM etiquette is built in: one
// identifying User-Agent, Nominatim limited to one request per second, results cached.
//
//   GET /api/health
//   GET /api/geocode?q=Copenhagen                     → { lat, lon, name, drive }
//   GET /api/roads?lat=&lon=  (or q=)                 → OSM centre-lines in local metres
//   GET /api/network?lat=&lon= (or q=)[&edges=1]      → lane-graph summary (girth, junctions, …)
//   GET /api/simulate?lat=&lon= (or q=)&rho=&law=&rule=&slow=&steps=&seed=&samples=
//                                                     → time series + final jam certificate
import { fetchRoads, locate, driveSide } from './fetch.js';
import { rasterize, girth } from './raster.js';
import { init, halfStep, LAWS, CLASSIC, TRAIN, DEFAULTS } from './sim.js';
import { snapshot } from './analysis.js';
import { WINDOW } from './presets.js';

export const LIMITS = Object.freeze({ steps: 6000, samples: 500, cache: 64, nominatimMs: 1000 });

class HttpError extends Error {
  constructor(status, message) { super(message); this.status = status; }
}

/** Serialise calls with at least `interval` ms between starts. */
const throttle = (interval, now, sleep) => {
  let tail = Promise.resolve();
  let next = 0;
  return (fn) => {
    const run = tail.then(async () => {
      const wait = next - now();
      if (wait > 0) await sleep(wait);
      next = now() + interval;
      return fn();
    });
    tail = run.catch(() => {});
    return run;
  };
};

/** Bounded least-recently-used memo of promises; failures are evicted. */
const memo = (size) => {
  const m = new Map();
  return (key, make) => {
    if (m.has(key)) { const v = m.get(key); m.delete(key); m.set(key, v); return v; }
    const v = make();
    m.set(key, v);
    if (m.size > size) m.delete(m.keys().next().value);
    Promise.resolve(v).catch(() => m.delete(key));
    return v;
  };
};

const num = (params, name, { min, max, def, int = false }) => {
  const raw = params.get(name);
  if (raw === null || raw === '') {
    if (def === undefined) throw new HttpError(400, `Missing parameter ${name}.`);
    return def;
  }
  const v = Number(raw);
  if (!Number.isFinite(v) || v < min || v > max || (int && !Number.isInteger(v)))
    throw new HttpError(400, `${name} must be ${int ? 'an integer' : 'a number'} in [${min}, ${max}].`);
  return v;
};

const oneOf = (params, name, options, def) => {
  const v = params.get(name) ?? def;
  if (!options.includes(v)) throw new HttpError(400, `${name} must be one of: ${options.join(', ')}.`);
  return v;
};

export const makeApi = ({ fetch, userAgent, now = Date.now, sleep = (ms) => new Promise((r) => setTimeout(r, ms)) }) => {
  if (!userAgent) throw new Error('OpenStreetMap services require an identifying User-Agent.');
  const io = { fetch, headers: { 'User-Agent': userAgent } };
  const nominatim = throttle(LIMITS.nominatimMs, now, sleep);
  const [places, roadsMemo, netsMemo] = [memo(LIMITS.cache), memo(LIMITS.cache), memo(LIMITS.cache)];
  const key = ({ lat, lon }) => `${lat.toFixed(5)},${lon.toFixed(5)}`;

  const geocode = (q) => places(q.trim().toLowerCase(), async () => {
    const coords = /^\s*-?\d/.test(q) && q.includes(',');
    const hit = await (coords ? locate(q, io) : nominatim(() => locate(q, io)))
      .catch((e) => { throw new HttpError(/No place/.test(e.message) ? 404 : 502, e.message); });
    return { ...hit, drive: driveSide(hit) };
  });

  /** The centre from lat/lon, or by geocoding q. */
  const centreOf = async (params) => {
    if (params.has('q')) return geocode(params.get('q'));
    const c = { lat: num(params, 'lat', { min: -85, max: 85 }), lon: num(params, 'lon', { min: -180, max: 180 }) };
    return { ...c, name: `${c.lat.toFixed(4)}, ${c.lon.toFixed(4)}`, drive: driveSide(c) };
  };

  const roadsAt = (c) => roadsMemo(key(c), () => fetchRoads(c, io).catch((e) => { throw new HttpError(502, e.message); }));

  const networkAt = (c, drive) => netsMemo(`${key(c)}:${drive}`, async () => {
    const { roads, source } = await roadsAt(c);
    if (roads.length < 2) throw new HttpError(404, 'No drivable streets in this window.');
    const net = rasterize(roads, { ...WINDOW, drive });
    return { net, girth: girth(net), source, roads: roads.length };
  });

  const summary = ({ net, girth: g, source, roads }, centre, drive) => ({
    centre, drive, source, window: WINDOW, roads,
    cells: net.roadCells,
    edges: net.outList.length,
    junctions: net.junction.reduce((a, b) => a + b, 0),
    entries: net.entries.length,
    exits: net.exit.reduce((a, b) => a + b, 0),
    girth: Number.isFinite(g) ? g : null,
  });

  const xy = (net, c) => ({ x: c % net.W, y: Math.floor(c / net.W) });

  const routes = {
    '/api/health': async () => ({ ok: true, window: WINDOW, laws: LAWS.map((l) => l.name), limits: LIMITS }),

    '/api/geocode': async (p) => {
      if (!p.get('q')?.trim()) throw new HttpError(400, 'Missing parameter q.');
      return geocode(p.get('q'));
    },

    '/api/roads': async (p) => {
      const centre = await centreOf(p);
      const { roads, source } = await roadsAt(centre);
      return { centre, drive: centre.drive, source, window: WINDOW, license: 'ODbL 1.0 — © OpenStreetMap contributors', roads };
    },

    '/api/network': async (p) => {
      const centre = await centreOf(p);
      const drive = oneOf(p, 'drive', ['R', 'L'], centre.drive);
      const built = await networkAt(centre, drive);
      const body = summary(built, centre, drive);
      if (p.get('edges') !== '1') return body;
      const { net } = built;
      const edges = [];
      for (let a = 0; a < net.W * net.H; a++)
        for (let i = net.outStart[a]; i < net.outStart[a + 1]; i++) edges.push([a, net.outList[i]]);
      return { ...body, W: net.W, H: net.H, edgeList: edges, junctionCells: [...net.junction.keys()].filter((c) => net.junction[c]) };
    },

    '/api/simulate': async (p) => {
      const centre = await centreOf(p);
      const drive = oneOf(p, 'drive', ['R', 'L'], centre.drive);
      const law = LAWS.find((l) => l.name === oneOf(p, 'law', LAWS.map((l) => l.name), LAWS[0].name));
      const opts = {
        ...DEFAULTS, green: law.green, box: law.box, crossTurns: law.crossTurns,
        rule: oneOf(p, 'rule', [CLASSIC, TRAIN], CLASSIC),
        slow: num(p, 'slow', { min: 0, max: 0.9, def: 0.1 }),
      };
      const rho = num(p, 'rho', { min: 0.01, max: 0.9, def: 0.3 });
      const steps = num(p, 'steps', { min: 2, max: LIMITS.steps, def: 1200, int: true });
      const samples = num(p, 'samples', { min: 1, max: LIMITS.samples, def: 60, int: true });
      const seed = num(p, 'seed', { min: 0, max: 2 ** 32 - 1, def: 1, int: true });
      const built = await networkAt(centre, drive);
      const { net } = built;
      const every = Math.max(1, Math.floor(steps / samples));
      const strip = ({ cert, ...rest }) => rest;
      let s = init(net, Math.round(net.roadCells * rho), seed, opts);
      let [prev, last] = [0, 0];
      const series = [];
      for (let t = 1; t <= steps; t++) {
        s = halfStep(net, s, opts);
        [prev, last] = [last, s.moved];
        if (t % every === 0 || t === steps) series.push(strip(snapshot(net, s, opts, prev + last)));
      }
      const fin = snapshot(net, s, opts, prev + last);
      return {
        network: summary(built, centre, drive),
        params: { law: law.name, ...opts, rho, steps, seed, cars: s.pos.length },
        series,
        final: { ...strip(fin), exited: s.exited, cores: fin.cert.cores.map((core) => core.map((k) => xy(net, s.pos[k]))) },
      };
    },
  };

  const handle = async (method, url) => {
    const u = new URL(url, 'http://local');
    const route = routes[u.pathname.replace(/\/$/, '')];
    if (!route) return { status: 404, body: { error: `No route ${u.pathname}.` } };
    if (method !== 'GET') return { status: 405, body: { error: 'Only GET is supported.' } };
    try {
      return { status: 200, body: await route(u.searchParams) };
    } catch (e) {
      return { status: e.status ?? 500, body: { error: e.message } };
    }
  };
  return { handle };
};
