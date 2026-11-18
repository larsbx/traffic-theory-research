// Live street data for any place: Overpass first, then the OSM API. Browser-only (fetch).
import { bboxAround, projector } from './geo.js';
import { parseOsmXml, parseOverpassJson, roadsFrom } from './osm.js';
import { WINDOW, MARGIN } from './presets.js';

const window_ = () => [WINDOW.cols * WINDOW.cell * MARGIN, WINDOW.rows * WINDOW.cell * MARGIN];

export const fetchRoads = async (centre) => {
  const [s, w, n, e] = bboxAround(centre, ...window_());
  const project = projector(centre);
  try {
    const q = `[out:json][timeout:25];way["highway"](${s},${w},${n},${e});out geom;`;
    const res = await fetch('https://overpass-api.de/api/interpreter', { method: 'POST', body: `data=${encodeURIComponent(q)}`, headers: { 'Content-Type': 'application/x-www-form-urlencoded' } });
    if (!res.ok) throw new Error(`Overpass ${res.status}`);
    return roadsFrom(parseOverpassJson(await res.json()), project);
  } catch {
    const res = await fetch(`https://api.openstreetmap.org/api/0.6/map?bbox=${w},${s},${e},${n}`);
    if (!res.ok) throw new Error(`OpenStreetMap ${res.status}`);
    return roadsFrom(parseOsmXml(await res.text()), project);
  }
};

/** "40.75, -73.98" → centre; anything else is looked up with Nominatim. */
export const locate = async (text) => {
  const m = text.match(/^\s*(-?\d+(?:\.\d+)?)\s*[,\s]\s*(-?\d+(?:\.\d+)?)\s*$/);
  if (m) return { lat: +m[1], lon: +m[2], name: `${(+m[1]).toFixed(4)}, ${(+m[2]).toFixed(4)}` };
  const res = await fetch(`https://nominatim.openstreetmap.org/search?format=json&limit=1&q=${encodeURIComponent(text)}`);
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
