// Bake real street geometry for the preset places from the OpenStreetMap API.
// Data © OpenStreetMap contributors, ODbL 1.0 — attribution is shown in the app.
import { writeFile } from 'node:fs/promises';
import { bboxAround, projector } from '../src/geo.js';
import { parseOsmXml, roadsFrom } from '../src/osm.js';
import { PLACES, WINDOW, MARGIN } from '../src/presets.js';

const [w, h] = [WINDOW.cols * WINDOW.cell * MARGIN, WINDOW.rows * WINDOW.cell * MARGIN];

const fetchPlace = async (place) => {
  const [s, wst, n, e] = bboxAround(place, w, h);
  const url = `https://api.openstreetmap.org/api/0.6/map?bbox=${wst},${s},${e},${n}`;
  const res = await fetch(url, { headers: { 'User-Agent': 'gridlock-city-bake/1.0' } });
  if (!res.ok) throw new Error(`${place.id}: HTTP ${res.status}`);
  const roads = roadsFrom(parseOsmXml(await res.text()), projector(place));
  console.log(`${place.id}: ${roads.length} roads`);
  return { ...place, roads };
};

const places = [];
for (const p of PLACES) places.push(await fetchPlace(p)); // sequential: be polite to the API
await writeFile(new URL('../data/presets.json', import.meta.url), JSON.stringify({
  source: 'OpenStreetMap API v0.6',
  license: 'ODbL 1.0 — © OpenStreetMap contributors',
  fetched: new Date().toISOString().slice(0, 10),
  places,
}));
