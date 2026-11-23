// OpenStreetMap client: Nominatim geocoding, roads from Overpass with the OSM API v0.6 as
// fallback. `io = { fetch, headers }` is injectable so the browser, the bake script, the API
// server and the tests share one code path (servers must send an identifying User-Agent).
import { bboxAround, projector } from './geo.js';
import { parseOsmXml, parseOverpassJson, roadsFrom } from './osm.js';
import { WINDOW, MARGIN } from './presets.js';

const window_ = () => [WINDOW.cols * WINDOW.cell * MARGIN, WINDOW.rows * WINDOW.cell * MARGIN];

export const OVERPASS = 'https://overpass-api.de/api/interpreter';
export const OSM_API = 'https://api.openstreetmap.org/api/0.6/map';
export const NOMINATIM = 'https://nominatim.openstreetmap.org/search';

const browser = () => ({ fetch: (...a) => globalThis.fetch(...a), headers: {} });

/** Drivable roads around `centre` as { roads, source }, in the app's local metres. */
export const fetchRoads = async (centre, io = browser()) => {
  const [s, w, n, e] = bboxAround(centre, ...window_());
  const project = projector(centre);
  try {
    const q = `[out:json][timeout:25];way["highway"](${s},${w},${n},${e});out geom;`;
    const res = await io.fetch(OVERPASS, { method: 'POST', body: `data=${encodeURIComponent(q)}`, headers: { ...io.headers, 'Content-Type': 'application/x-www-form-urlencoded' } });
    if (!res.ok) throw new Error(`Overpass ${res.status}`);
    return { roads: roadsFrom(parseOverpassJson(await res.json()), project), source: 'overpass' };
  } catch {
    const res = await io.fetch(`${OSM_API}?bbox=${w},${s},${e},${n}`, { headers: io.headers });
    if (!res.ok) throw new Error(`OpenStreetMap ${res.status}`);
    return { roads: roadsFrom(parseOsmXml(await res.text()), project), source: 'osm-api' };
  }
};

/** "40.75, -73.98" → centre; anything else is looked up with Nominatim. */
export const locate = async (text, io = browser()) => {
  const m = text.match(/^\s*(-?\d+(?:\.\d+)?)\s*[,\s]\s*(-?\d+(?:\.\d+)?)\s*$/);
  if (m) return { lat: +m[1], lon: +m[2], name: `${(+m[1]).toFixed(4)}, ${(+m[2]).toFixed(4)}` };
  const res = await io.fetch(`${NOMINATIM}?format=json&limit=1&q=${encodeURIComponent(text)}`, { headers: io.headers });
  if (!res.ok) throw new Error(`Nominatim ${res.status}`);
  const [hit] = await res.json();
  if (!hit) throw new Error(`No place called “${text}”`);
  return { lat: +hit.lat, lon: +hit.lon, name: hit.display_name.split(',')[0].toUpperCase() };
};

/** Drive side from longitude/latitude: a coarse list of left-hand-traffic regions. */
export const driveSide = ({ lat, lon }) => {
  const boxes = [ // [south, west, north, east]
    [49.8, -8.7, 61, 1.8], [51.4, -10.6, 55.4, -5.4], // GB, IE
    [24, 122, 46, 146], [-47.5, 112, -10, 179], [5, 68, 36, 97.5], [-35, 10, -15, 41], // JP, AU/NZ, IN, southern Africa
    [-11, 95, 7, 141], [0.8, 99, 7.5, 119.5], [21.5, 113.8, 22.6, 114.5], // ID, MY/SG, HK
  ];
  return boxes.some(([s, w, n, e]) => lat >= s && lat <= n && lon >= w && lon <= e) ? 'L' : 'R';
};
