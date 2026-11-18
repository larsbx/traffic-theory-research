// OpenStreetMap → drivable centre-lines in local metres.
// Accepts both OSM API v0.6 XML and Overpass `out geom` JSON, normalised to
// ways = [{ tags, geom: [[lat, lon], …] }].

const CLASS = {
  motorway: 0, trunk: 0, primary: 1, secondary: 2, tertiary: 3,
  unclassified: 4, residential: 4, living_street: 4,
};

const entity = (s) =>
  s.replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&lt;/g, '<')
    .replace(/&gt;/g, '>').replace(/&amp;/g, '&');

const attrs = (tag) =>
  Object.fromEntries([...tag.matchAll(/(\w+)="([^"]*)"/g)].map(([, k, v]) => [k, entity(v)]));

export const parseOsmXml = (xml) => {
  const nodes = new Map(
    [...xml.matchAll(/<node\b[^>]*>/g)].map(([t]) => {
      const a = attrs(t);
      return [a.id, [+a.lat, +a.lon]];
    }),
  );
  return [...xml.matchAll(/<way\b[^>]*>([\s\S]*?)<\/way>/g)].map(([, body]) => ({
    tags: Object.fromEntries([...body.matchAll(/<tag\b[^>]*>/g)].map(([t]) => {
      const a = attrs(t);
      return [a.k, a.v];
    })),
    geom: [...body.matchAll(/<nd\b[^>]*ref="(\d+)"/g)].map(([, r]) => nodes.get(r)).filter(Boolean),
  }));
};

export const parseOverpassJson = (json) =>
  json.elements
    .filter((e) => e.type === 'way' && e.geometry)
    .map((e) => ({ tags: e.tags ?? {}, geom: e.geometry.map((g) => [g.lat, g.lon]) }));

export const roadClass = (tags) => CLASS[(tags.highway ?? '').replace(/_link$/, '')];

/** +1 along the way, −1 against it, 0 both directions. */
export const oneway = (tags) => {
  const o = tags.oneway;
  if (o === '-1' || o === 'reverse') return -1;
  if (o === 'yes' || o === 'true' || o === '1') return 1;
  if (o === 'no' || o === 'false' || o === '0') return 0;
  return tags.junction === 'roundabout' || tags.junction === 'circular' || tags.highway === 'motorway' ? 1 : 0;
};

const drivable = ({ tags, geom }) =>
  roadClass(tags) !== undefined && geom.length >= 2 && tags.area !== 'yes' &&
  tags.access !== 'no' && tags.motor_vehicle !== 'no' && tags.motorcar !== 'no' &&
  !(tags.tunnel && tags.tunnel !== 'no') && !(tags.layer && +tags.layer < 0);

/** Roads as { o: oneway, c: class, pts: [x0, y0, x1, y1, …] } in whole decimetres. */
export const roadsFrom = (ways, project) =>
  ways.filter(drivable).map(({ tags, geom }) => ({
    o: oneway(tags),
    c: roadClass(tags),
    pts: geom.flatMap((g) => project(g).map((v) => Math.round(v * 10))),
  }));
