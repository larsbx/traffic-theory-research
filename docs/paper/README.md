# Gridlock on Real Street Networks (paper)

[`paper.pdf`](paper.pdf). Blocking certificates, girth bounds and throughput limits for
two-phase exclusion dynamics on OpenStreetMap lane graphs, with experiments on six city centres.

| file | role |
|---|---|
| `paper.src.html` | source: HTML with TeX math (`$…$`, `$$…$$`) |
| `build.mjs` | KaTeX pre-renders the math; Chromium (Playwright) prints `paper.pdf` |
| `data/experiments.json` | 600 seeded runs + structure of each lane graph, from `app/scripts/experiments.mjs` |
| `figures.mjs` | `figures/frozen.svg`, `figures/flow.svg` from the data (no plotting dependencies) |
| `figures/*.png` | simulator renderings (Midtown, Étoile, Bank) |

```sh
cd docs/paper && npm ci
npx playwright install chromium   # the browser that prints the PDF (skip if already provisioned)
npm run experiments   # ~1 min, deterministic
npm run figures
npm run build         # paper.html (local preview) and paper.pdf
```

It is typeset from HTML because no TeX engine is available in the build environment. The
mathematics uses KaTeX's Computer Modern fonts.
