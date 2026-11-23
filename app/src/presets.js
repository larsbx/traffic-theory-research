// Map windows: centre and display name. Geometry is baked into data/presets.json
// by scripts/bake.mjs (OpenStreetMap, ODbL); the live loader uses the same window.
export const WINDOW = { cell: 7.5, cols: 96, rows: 64 }; // metres per cell, grid size
export const MARGIN = 1.25; // fetch slightly beyond the window so edge roads exit cleanly

export const PLACES = [
  { id: 'midtown', name: 'MIDTOWN MANHATTAN', lat: 40.7536, lon: -73.9832, drive: 'R' },
  { id: 'eixample', name: 'EIXAMPLE BARCELONA', lat: 41.3917, lon: 2.1649, drive: 'R' },
  { id: 'etoile', name: 'ETOILE PARIS', lat: 48.8738, lon: 2.2950, drive: 'R' },
  { id: 'bank', name: 'BANK LONDON', lat: 51.5133, lon: -0.0890, drive: 'L' },
  { id: 'grachten', name: 'GRACHTEN AMSTERDAM', lat: 52.3700, lon: 4.8890, drive: 'R' },
  { id: 'shibuya', name: 'SHIBUYA TOKYO', lat: 35.6598, lon: 139.7006, drive: 'L' },
];
