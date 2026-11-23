# Gridlock City

A retro pixel-art traffic simulator that runs this repository's BML dynamics on real street
maps. Streets come from OpenStreetMap and render as a low-resolution arcade maze laid on a
ground plane in perspective. Cars are lit 3D shapes (a body and a cabin, headlight forward). You
can tilt, turn, zoom and pan the view. Cars the engine has **proved** can never move again turn blue, and the
jam-loop cores that hold them flash.

```sh
cd app
npm ci
npm test          # rasterizer, engine, certificates, Python equivalence
npm run build     # → dist/index.html (open it in a browser) and dist/artifact.html
npm start         # serve the page + the OpenStreetMap API on http://localhost:8787 (PORT, OSM_USER_AGENT)
npm run bake      # refresh data/presets.json from the OpenStreetMap API
PYTHONPATH=. python app/scripts/bml_fixture.py   # (from the repo root) regenerate the Python orbits
```

Modes:
- **City:** six real places, or any place you type (through the OSM API below). Exposes the named
  traffic laws, the update rule, signal green time, density, dawdling and breakdowns, plus a
  measured fundamental diagram J(ρ).
- **BML lab:** the plain torus, with live readouts of the theorems in
  [`docs/theorems.md`](../docs/theorems.md).

## Perspective view

`src/camera.js` is a pinhole camera over the ground plane z = 0, with pitch and yaw and no
roll. Without roll every screen row meets the ground at a single depth. So each row of ground
pixels is an affine image of a world segment, as in SNES Mode 7 but at any tilt and heading.
`render.drawGround` fills the low-res target (480 × 320) row by row from the maze texture,
with distance fog and a dusk sky, and recomputes only when the camera moves. Zoom 1 frames the
whole map: the camera distance is bisected until all four corners sit on the screen margin.
Cars are drawn far to near; each is two boxes with back faces culled and side faces lit.
`test/camera.test.js` checks that unproject inverts project, the row-affinity, the framing and
the zoom.

## OpenStreetMap API

`npm start` runs `server.mjs`. It serves the simulator at `/` and a JSON API at `/api/*`
(`src/api.js`, transport-free and tested against a fake OSM). When the page is served this
way, its LOAD box goes through the API, so any place works.

| endpoint | parameters | returns |
|---|---|---|
| `GET /api/health` | | window size, law names, limits |
| `GET /api/geocode` | `q` (a name, or `lat,lon`) | `{lat, lon, name, drive}`; drive side `R`/`L` |
| `GET /api/roads` | `lat`,`lon` or `q` | OSM drivable centre-lines in local metres, plus `source` (`overpass` / `osm-api`) |
| `GET /api/network` | `lat`,`lon` or `q`; `drive`; `edges=1` | lane graph: cells, edges, junctions, entries, exits, **girth**; with `edges=1`, the edge list |
| `GET /api/analyze` | `lat`,`lon` or `q`; `law`; `rho` (0.3); `maxLen` (girth + 8) | **no simulation**: cell and jam-graph girth, short-cycle census with hotspot cells, risk index R(ρ), spectral radius, throughput bounds (CLASSIC / TRAIN), Sturmian free speeds of the streets ([note](../docs/research/2026-11-23-dynamics-free-map-mathematics.md)) |
| `GET /api/simulate` | `lat`,`lon` or `q`; `rho` (0.3), `law` (`CITY CODE`…`BML LIGHTS`), `rule` (`classic`/`train`), `slow` (0.1), `steps` ≤ 6000 (1200), `samples` ≤ 500 (60), `seed` (1) | a time series of ρ, v̄, J, queue, frozen and jam loops; the final certificate with each core's cells |

```sh
curl 'localhost:8787/api/simulate?q=Nyhavn%20Copenhagen&law=BML%20LIGHTS&rho=0.4&steps=1200'
```

OSM etiquette is built in. Requests carry an identifying `User-Agent` (set `OSM_USER_AGENT`
to your own contact). Nominatim gets at most one request per second. Places, roads and lane
graphs are cached (LRU, 64 entries). Results are deterministic per seed. Errors are JSON:
400 for a bad parameter, 404 for an unknown place or route, 502 for an OSM failure.

## The model

| piece | definition | module |
|---|---|---|
| lanes | OSM centre-lines → local metres → 7.5 m cells (one car length). Two lanes per two-way street on the drive side, offset by (s/2)(\|cos θ\|+\|sin θ\|) so diagonal staircases stay disjoint. Lanes are 4-connected Amanatides–Woo traversals, and each edge carries its street's true heading. Head-on 2-cycles and loops ≤ 12 cells through a non-junction cell are rasterising artefacts and are removed by provenance. | `raster.js` |
| update | half-steps alternate phase 0 (horizontal hops) and phase 1 (vertical hops): BML 1992 Model I. **CLASSIC** moves a car into a cell only if it was empty before the half-step. **TRAIN** lets queues move together and closed same-phase loops rotate (Austin–Benjamini). Merges go to the longest-waiting car. | `sim.js` |
| signals | a junction (a cell entered along both axes) admits only the axis with green(t) = ⌊t/G⌋ mod 2. With **G = 1** the signal equals the phase and never binds. | `sim.js` |
| box rule | a car outside a junction commits to its whole path through the box and enters only if every cell up to the first cell beyond it is empty. | `sim.js` |
| routing | turns ≤ 120°, no two-hop reversal over 150°, optional ban on turns across oncoming traffic, straight bias 4:1, Nagel–Schreckenberg dawdle p. A car re-plans only after it moves. | `sim.js` |
| boundary | cars leaving the window re-enter at a free entry: a closed population with an entry queue. | `sim.js` |

**Reduction to BML (tested).** On `torus(W, H)` with fixed species E/N, `halfStep ∘ halfStep`
equals `bml.model.step` cell for cell and in move count. This is checked on 80 Python orbits
(`test/fixtures/bml-python.json`), 10 torus shapes including 1×4 and 3×1, 4 densities, and
both rules.

## Jam certificates

Define β(k) as the car that keeps k from moving. That is the occupant of k's committed next
cell. Under the box rule, when k waits to enter a junction, it is the first occupant along k's
committed path through the box.

**Proposition (frozen cars).** Fix intents as the engine does: a car re-plans only after
moving. Let C be a β-cycle. Under CLASSIC, no car of C moves again. Under TRAIN, the same holds
unless C consists of direct edges on one axis. Every car whose β-path reaches such a C is
frozen too. Signals, dawdling and breakdowns only remove moves, so they preserve this.

*Proof sketch.* Suppose some car of C moves first, at time t. Under CLASSIC it needs its
target (or box path) empty before the half-step, but its blocker has not moved yet.
Contradiction. Under TRAIN a car whose blocker is direct moves only together with that
blocker, in the same phase. So all of C would move at t, on one axis, with direct edges. Then
proceed by induction along β-paths into C. ∎

This is the map form of Lemma G0. A direct β-cycle is a directed cycle of the lane graph on
distinct cars, so a jam core has **≥ girth** cars. That is G1's min(W, H) in city form: the
torus girth is min(W, H), which is tested. `test/sim.test.js` checks the proposition
empirically: no certified car ever moves again, across six maps × both rules × box rule ×
signals, with dawdling and breakdowns.

## What the simulator shows (headless runs during development; the City mode reproduces them)

- Pure BML on real maps locks in seconds. Its every-tick phase flip fills each crossing's 2×2
  box from both axes. Signals plus the box rule plus a ban on cross-traffic turns keep all six
  presets free-flowing up to ρ ≈ 0.3, and five of them up to ρ ≈ 0.45. Shibuya locks there.
- Grids are robust. Midtown (girth 58) and Eixample (girth 52) did not jam in any law tested,
  even with breakdowns: a core needs a block-sized loop of committed cars. Irregular centres
  (Étoile, Bank, Shibuya) jam once the laws are repealed.
- Following [freezing and capture](../docs/research/2026-11-18-freezing-gridlock-nucleation.md),
  forming a core is separate from capturing traffic, and in a closed city one core is
  absorbing: FROZEN keeps climbing after the first JAM LOOP appears.
- Flow saturates at high ρ because entries limit the inflow: the open-boundary (TASEP)
  phenomenon. The simulator reports on-street density and the entry queue separately for that
  reason.

## Scope

These are derivations and executable checks. The proposition above has a proof sketch and
property tests, not a Lean proof. The lane rasterization is a modelling choice. Real-map
behaviour is empirical and depends on routing assumptions. Nothing here claims a jamming
threshold.

Map data © OpenStreetMap contributors, ODbL 1.0.
