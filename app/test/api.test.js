import { test } from 'node:test';
import assert from 'node:assert/strict';
import { makeApi, LIMITS } from '../src/api.js';
import { serve } from '../server.mjs';
import { OVERPASS, OSM_API, NOMINATIM } from '../src/fetch.js';

// A fake OpenStreetMap: a 6 × 4 grid of two-way residential streets, 90 m apart, round (0, 0).
const M = 1 / 111195; // degrees per metre at the equator (both axes at lat 0)
const ways = [
  ...[-225, -135, -45, 45, 135, 225].map((x) => [[-500 * M, x * M], [500 * M, x * M]]),
  ...[-135, -45, 45, 135].map((y) => [[y * M, -500 * M], [y * M, 500 * M]]),
];
const overpassJson = { elements: ways.map((g, i) => ({ type: 'way', id: i, tags: { highway: 'residential' }, geometry: g.map(([lat, lon]) => ({ lat, lon })) })) };
const osmXml = `<osm>${ways.flatMap((g, i) => g.map(([lat, lon], j) => `<node id="${i * 10 + j}" lat="${lat}" lon="${lon}"/>`)).join('')}${
  ways.map((g, i) => `<way id="${i}">${g.map((_, j) => `<nd ref="${i * 10 + j}"/>`).join('')}<tag k="highway" v="residential"/></way>`).join('')}</osm>`;

const fakeOsm = ({ overpassDown = false } = {}) => {
  const calls = [];
  const fetch = async (url, init = {}) => {
    calls.push({ url, agent: init.headers?.['User-Agent'] });
    const reply = (status, body) => ({ ok: status === 200, status, json: async () => body, text: async () => body });
    if (url === OVERPASS) return overpassDown ? reply(504, '') : reply(200, overpassJson);
    if (url.startsWith(OSM_API)) return reply(200, osmXml);
    if (url.startsWith(NOMINATIM)) return url.includes('nowhere') ? reply(200, []) : reply(200, [{ lat: '0', lon: '0', display_name: 'Null Island, Atlantic' }]);
    return reply(404, '');
  };
  return { fetch, calls };
};

const clock = () => {
  let t = 0;
  return { now: () => t, sleep: async (ms) => { t += ms; } };
};

const get = (api, path) => api.handle('GET', path);

test('the API refuses to run without an identifying User-Agent', () => {
  assert.throws(() => makeApi({ fetch: fakeOsm().fetch }), /User-Agent/);
});

test('geocode: Nominatim with User-Agent, one request per second, cached; coordinates need no lookup', async () => {
  const osm = fakeOsm(); const c = clock();
  const api = makeApi({ fetch: osm.fetch, userAgent: 'test/1.0', ...c });
  const [a, b] = await Promise.all([get(api, '/api/geocode?q=Null%20Island'), get(api, '/api/geocode?q=Atlantis')]);
  assert.equal(a.status, 200);
  assert.deepEqual(a.body, { lat: 0, lon: 0, name: 'NULL ISLAND', drive: 'R' });
  assert.equal(b.status, 200);
  assert.ok(c.now() >= LIMITS.nominatimMs, 'second lookup waited for the rate limit');
  await get(api, '/api/geocode?q=null%20island');
  assert.equal(osm.calls.length, 2, 'repeat lookup served from cache');
  assert.ok(osm.calls.every((x) => x.agent === 'test/1.0'));
  const coords = await get(api, '/api/geocode?q=51.5,-0.1');
  assert.deepEqual([coords.body.lat, coords.body.drive, osm.calls.length], [51.5, 'L', 2]);
  assert.equal((await get(api, '/api/geocode?q=nowhere')).status, 404);
});

test('roads: Overpass, cached per centre, with the OSM API as fallback', async () => {
  const osm = fakeOsm();
  const api = makeApi({ fetch: osm.fetch, userAgent: 't', ...clock() });
  const r = await get(api, '/api/roads?lat=0&lon=0');
  assert.equal(r.status, 200);
  assert.equal(r.body.source, 'overpass');
  assert.equal(r.body.roads.length, ways.length);
  await get(api, '/api/roads?lat=0.000001&lon=0');
  assert.equal(osm.calls.length, 1, 'same 5-decimal centre is cached');
  const down = makeApi({ fetch: fakeOsm({ overpassDown: true }).fetch, userAgent: 't', ...clock() });
  const f = await get(down, '/api/roads?lat=0&lon=0');
  assert.deepEqual([f.status, f.body.source, f.body.roads.length], [200, 'osm-api', ways.length]);
});

test('network: a grid of two-way streets has two-lane crossings (girth 4, the 2×2 box)', async () => {
  const api = makeApi({ fetch: fakeOsm().fetch, userAgent: 't', ...clock() });
  const { status, body } = await get(api, '/api/network?q=Null%20Island&edges=1');
  assert.equal(status, 200);
  assert.equal(body.girth, 4);
  assert.ok(body.junctions >= 4 * 24, `${body.junctions} junction cells`);
  assert.ok(body.entries > 0 && body.cells > 0);
  assert.equal(body.edgeList.length, body.edges);
  assert.ok(body.edgeList.every(([a, b]) => Math.abs((a % body.W) - (b % body.W)) + Math.abs(Math.floor(a / body.W) - Math.floor(b / body.W)) === 1));
});

test('simulate: bounded, deterministic per seed, and a repealed law can jam where the city code flows', async () => {
  const api = makeApi({ fetch: fakeOsm().fetch, userAgent: 't', ...clock() });
  const q = '/api/simulate?lat=0&lon=0&rho=0.35&steps=600&samples=30';
  const [a, b] = [await get(api, `${q}&seed=3`), await get(api, `${q}&seed=3`)];
  assert.equal(a.status, 200);
  assert.deepEqual(a.body, b.body);
  assert.equal(a.body.series.length, 30);
  for (const p of a.body.series) {
    for (const k of ['rho', 'j']) assert.ok(p[k] >= 0 && p[k] <= 1, `${k}=${p[k]}`);
    assert.ok(p.v >= 0 && p.v <= 2, `v=${p.v}`); // hops per car per full step: ≤ 2 (one per half-step)
  }
  assert.equal(a.body.params.law, 'CITY CODE');
  const bml = await get(api, `/api/simulate?lat=0&lon=0&rho=0.5&steps=1200&law=BML%20LIGHTS&slow=0`);
  for (const core of bml.body.final.cores) assert.ok(core.length >= 4, 'every jam core has ≥ girth cars');
  assert.ok(bml.body.final.loops > 0, 'bare BML lights lock the two-lane boxes');
});

test('validation and errors are JSON with the right status', async () => {
  const api = makeApi({ fetch: fakeOsm().fetch, userAgent: 't', ...clock() });
  const cases = [
    ['/api/simulate?lat=0&lon=0&steps=999999', 400], ['/api/simulate?lat=0&lon=0&law=ANARCHY', 400],
    ['/api/roads?lat=95&lon=0', 400], ['/api/roads', 400], ['/api/geocode', 400], ['/api/nope', 404],
  ];
  for (const [path, status] of cases) {
    const r = await get(api, path);
    assert.equal(r.status, status, path);
    assert.equal(typeof r.body.error, 'string');
  }
  assert.equal((await api.handle('POST', '/api/health')).status, 405);
  const broken = makeApi({ fetch: async () => { throw new TypeError('network down'); }, userAgent: 't', ...clock() });
  assert.equal((await get(broken, '/api/roads?lat=0&lon=0')).status, 502);
});

test('server: JSON under /api with CORS, the page at /', async () => {
  const api = makeApi({ fetch: fakeOsm().fetch, userAgent: 't', ...clock() });
  const server = serve({ api, page: new URL('../template.html', import.meta.url) }).listen(0);
  await new Promise((r) => server.once('listening', r));
  const base = `http://127.0.0.1:${server.address().port}`;
  try {
    const h = await fetch(`${base}/api/health`);
    assert.equal(h.headers.get('access-control-allow-origin'), '*');
    assert.equal((await h.json()).ok, true);
    assert.match(await (await fetch(`${base}/`)).text(), /<title>Gridlock City<\/title>/);
    assert.equal((await fetch(`${base}/elsewhere`)).status, 404);
  } finally { server.close(); }
});

test('analyze: dynamics-free structure of the fake grid (2×2 boxes give jam girth 4 without the box-safe law)', async () => {
  const api = makeApi({ fetch: fakeOsm().fetch, userAgent: 't', ...clock() });
  const bml = await get(api, '/api/analyze?lat=0&lon=0&law=BML%20LIGHTS&rho=0.3');
  assert.equal(bml.status, 200);
  assert.equal(bml.body.girth.cells, 4);
  assert.equal(bml.body.girth.jam, 4);
  assert.ok(bml.body.cycles.count > 0 && bml.body.cycles.hotspots[0].length === 4);
  assert.ok(bml.body.risk.index > 0 && bml.body.risk.lambda > 0 && bml.body.risk.lambda <= 1);
  assert.ok(bml.body.throughput.classic > 0 && bml.body.throughput.train >= bml.body.throughput.classic);
  assert.ok(Math.abs(bml.body.streets.meanFreeSpeedCells - 1) < 1e-9, 'an axis-aligned grid has free speed 1');
  const code = await get(api, '/api/analyze?lat=0&lon=0&law=CITY%20CODE');
  assert.ok(code.body.girth.jam === null || code.body.girth.jam >= 4);
});
