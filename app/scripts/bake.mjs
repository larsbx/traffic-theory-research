// Bake real street geometry for the preset places from the OpenStreetMap API.
// Data © OpenStreetMap contributors, ODbL 1.0 — attribution is shown in the app.
import { writeFile } from 'node:fs/promises';
import { fetchRoads } from '../src/fetch.js';
import { PLACES } from '../src/presets.js';

const io = { fetch, headers: { 'User-Agent': 'gridlock-city-bake/1.0 (traffic-theory-research)' } };

const fetchPlace = async (place) => {
  const { roads, source } = await fetchRoads(place, io);
  console.log(`${place.id}: ${roads.length} roads (${source})`);
  return { ...place, roads };
};

const places = [];
for (const p of PLACES) places.push(await fetchPlace(p)); // sequential: be polite to the API
await writeFile(new URL('../data/presets.json', import.meta.url), JSON.stringify({
  source: 'OpenStreetMap (Overpass, else API v0.6)',
  license: 'ODbL 1.0 — © OpenStreetMap contributors',
  fetched: new Date().toISOString().slice(0, 10),
  places,
}));
