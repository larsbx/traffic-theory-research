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

## Re-routing and the real-traffic theorems

`opts.reroute` lets a blocked driver switch to any free legal option from its current lane,
dropping the commitment assumption, as human drivers do. `src/realflow.js` computes the greatest
**trap**, the cars that can never move whatever their drivers choose, and the **safe cells**,
where no trapped car can sit. If every cell is safe and there is no box rule, permanent gridlock is
impossible. It also provides the closed-form bounds of the
[real-traffic note](../docs/research/2026-11-24-real-traffic-theorems.md). `scripts/reroute.mjs`
reruns its 360-run experiment.

## BML, extension, bridge

The **BML lab** runs BML itself: the torus, two species, the theorems of
[`docs/theorems.md`](../docs/theorems.md). **City** mode runs an *extension* of BML to lane
graphs (signals, box rule, routing, merges), which reduces to BML only on the torus. Results
proved for the extension are in the [research note](../docs/research/2026-11-23-dynamics-free-map-mathematics.md).
The street geometry is real, but traffic in City mode is a model: uncalibrated, with random
routing and no observed data. Statements about the six cities describe the model on their
geometry, not real traffic there. See the [paper](../docs/paper/paper.pdf), §2.

## Perspective view

`src/camera.js` is a pinhole camera over the ground plane z = 0, with pitch and yaw and no
roll. Without roll every screen row meets the ground at a single depth. So each row of ground
pixels is an affine image of a world segment, as in SNES Mode 7 but at any tilt and heading.
`render.drawGround` fills the low-res target (480 × 320) row by row from the maze texture,
with distance fog and a dusk sky, and recomputes only when the camera moves. Zoom 1 frames the
whole map: the camera distance is bisected until all four corners sit on the screen margin.
Streets are drawn straight. The rasterizer keeps each lane's true polyline, and the texture
strokes those as corridors. Each cell has a display point, the projection of its centre onto
its lane. Cars sit at that point, face along the street's true heading, and are sized to the
gap between consecutive cells. The dynamics stay on the grid; only the drawing is geometric.
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
| `GET /api/analyze` | `lat`,`lon` or `q`; `law`; `rho` (0.3); `maxLen` (girth + 8, at most 512) | **no simulation**: cell and jam-graph girth, short-cycle census with hotspot cells, risk index R(ρ), spectral radius, throughput bounds (CLASSIC / TRAIN), Sturmian free speeds of the streets ([note](../docs/research/2026-11-23-dynamics-free-map-mathematics.md)) |
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
| box rule | entering from outside a junction requires pre-step vacancy of every cell in the recorded box tail. The planner records at most `AHEAD` tail entries. | `sim.js` |
| routing | turns ≤ 120°, no two-hop reversal over 150°, optional ban on turns across oncoming traffic, straight bias 4:1, Nagel–Schreckenberg dawdle p. A car re-plans only after it moves. | `sim.js` |
| boundary | cars leaving the window re-enter at a free entry: a closed population with an entry queue. | `sim.js` |

**Reduction to BML (tested).** On `torus(W, H)` with fixed species E/N, `halfStep ∘ halfStep`
equals `bml.model.step` cell for cell and in move count. This is checked on 80 Python orbits
(`test/fixtures/bml-python.json`), 10 torus shapes including 1×4 and 3×1, 4 densities, and
both rules.

## Jam certificates

Define β(k) as the occupant of k's committed next cell. If that cell is empty and k is
subject to the box-entry gate, β(k) is the first occupant in the recorded `ahead` tail,
when there is one. The gate applies when k is outside the junction and its next cell is
inside. The check uses the pre-step occupancy in CLASSIC and TRAIN.

**Proposition (frozen cars).** Fix intents as the engine does: a car re-plans only after
moving. Let C be a β-cycle. Under CLASSIC, no car of C moves again. Under TRAIN, the same holds
unless C consists of direct edges on one axis. Every car whose β-path reaches a frozen cycle
is frozen too. A direct same-axis cycle may rotate when every member can move together.
Signals, dawdling and breakdowns can prevent rotation. The certificate applies while the
update rule and box-entry gate stay fixed and cars remain in place until they move.

*Proof sketch.* Suppose some car of C moves first, at time t. Under CLASSIC it needs its
target (or box path) empty before the half-step, but its blocker has not moved yet.
Contradiction. Under TRAIN a car whose blocker is direct moves only together with that
blocker, in the same phase. So all of C would move at t, on one axis, with direct edges. Then
proceed by induction along β-paths into C. ∎ See [the Lean P1 endpoints](../formal/lean/README.md#lane-graph-deadlock-p1).

This is the map form of Lemma G0. A direct β-cycle is a directed cycle of the lane graph on
distinct cars, so a direct jam core has **≥ girth** cars. That is G1's min(W, H) in city form: the
torus girth is min(W, H), which is tested. `test/sim.test.js` checks the proposition
empirically: no certified car ever moves again, across six maps × both rules × box rule ×
signals, with dawdling and breakdowns. [The P1 controls](test/p1.test.js) cover direct-priority
selection, indirect pre-step blocking, capture, and same-axis and mixed-axis cycles.

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
- Mean speed counts hops per car per full step. It is at most 1 on axis-aligned lanes but
  reaches 1 + min(\|tan θ\|, \|cot θ\|) on a diagonal street, so it is not capped.
- Flow saturates at high ρ because entries limit the inflow: the open-boundary (TASEP)
  phenomenon. The simulator reports on-street density and the entry queue separately for that
  reason.

## Scope

These are derivations and executable checks. The proposition above has a proof sketch and
property tests, not a Lean proof. The lane rasterization is a modelling choice. Real-map
behaviour is empirical and depends on routing assumptions. Nothing here claims a jamming
threshold.

Map data © OpenStreetMap contributors, ODbL 1.0.
