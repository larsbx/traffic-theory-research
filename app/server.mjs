// Gridlock City server: the simulator page at /, the OpenStreetMap API at /api/*.
//   npm run build && npm start        (PORT, OSM_USER_AGENT override the defaults)
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { makeApi } from './src/api.js';

export const DEFAULT_AGENT = 'gridlock-city/1.0 (+https://github.com/larsbx/traffic-theory-research)';

export const serve = ({ api, page = new URL('./dist/index.html', import.meta.url) }) =>
  createServer(async (req, res) => {
    const send = (status, type, body) => {
      res.writeHead(status, { 'Content-Type': type, 'Access-Control-Allow-Origin': '*', 'Cache-Control': 'no-store' });
      res.end(body);
    };
    if (req.url.startsWith('/api/')) {
      const { status, body } = await api.handle(req.method, req.url);
      return send(status, 'application/json; charset=utf-8', JSON.stringify(body));
    }
    if (req.url === '/' || req.url === '/index.html') {
      try { return send(200, 'text/html; charset=utf-8', await readFile(page)); } catch { return send(503, 'text/plain', 'Run `npm run build` first.'); }
    }
    send(404, 'text/plain', 'Not found');
  });

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const port = Number(process.env.PORT ?? 8787);
  const api = makeApi({ fetch, userAgent: process.env.OSM_USER_AGENT ?? DEFAULT_AGENT });
  serve({ api }).listen(port, () => console.log(`Gridlock City on http://localhost:${port}`));
}
