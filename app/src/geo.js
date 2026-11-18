// Local equirectangular projection: metres east (x) and north (y) of a centre.
// Error is O((Δφ)²) — sub-centimetre over the ~1 km windows used here.
const R = 6371008.8;
const RAD = Math.PI / 180;

export const projector = ({ lat, lon }) => {
  const k = Math.cos(lat * RAD);
  return ([la, lo]) => [(lo - lon) * RAD * R * k, (la - lat) * RAD * R];
};

/** Lat/lon box [south, west, north, east] containing a w×h metre window around the centre. */
export const bboxAround = ({ lat, lon }, w, h) => {
  const dLat = h / 2 / (R * RAD);
  const dLon = w / 2 / (R * RAD * Math.cos(lat * RAD));
  return [lat - dLat, lon - dLon, lat + dLat, lon + dLon];
};
