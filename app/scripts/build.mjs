// Bundle src/ into one self-contained page: dist/index.html (standalone) and dist/artifact.html
// (body fragment for hosts that supply the document skeleton).
import { build } from 'esbuild';
import { mkdir, readFile, writeFile } from 'node:fs/promises';

const root = new URL('..', import.meta.url);
const { outputFiles: [js] } = await build({
  entryPoints: [new URL('src/main.js', root).pathname], bundle: true, minify: true, format: 'iife',
  target: 'es2022', write: false, loader: { '.json': 'json' },
});
const code = js.text.replace(/<\/script/gi, '<\\/script');
const body = (await readFile(new URL('template.html', root), 'utf8')).replace('<!-- APP -->', () => `<script>${code}</script>`);
await mkdir(new URL('dist/', root), { recursive: true });
await writeFile(new URL('dist/artifact.html', root), body);
await writeFile(new URL('dist/index.html', root),
  `<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n</head>\n<body>\n${body}\n</body>\n</html>\n`);
console.log(`dist/index.html — ${(body.length / 1024).toFixed(0)} KB`);
