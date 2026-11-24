// paper.src.html → paper.html (math pre-rendered by KaTeX) → paper.pdf (Chromium print).
// Math: $…$ inline, $$…$$ display. Needs Playwright's Chromium (`npx playwright install chromium`).
import { readFile, writeFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import katex from 'katex';

const here = new URL('./', import.meta.url);
const src = await readFile(new URL('paper.src.html', here), 'utf8');
const render = (tex, displayMode) => katex.renderToString(tex.trim(), { displayMode, throwOnError: true, strict: 'ignore', output: 'html' });
const body = src
  .replace(/\$\$([\s\S]+?)\$\$/g, (_, t) => render(t, true))
  .replace(/\$([^$\n]+?)\$/g, (_, t) => render(t, false));
const css = (await readFile(new URL('node_modules/katex/dist/katex.min.css', here), 'utf8'))
  .replace(/url\(fonts\//g, `url(${new URL('node_modules/katex/dist/fonts/', here).href}`);
const html = `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Gridlock on Real Street Networks</title><style>${css}</style></head><body>${body}</body></html>`;
await writeFile(new URL('paper.html', here), html);

const require = createRequire(import.meta.url);
const { chromium } = require('playwright');
const browser = await chromium.launch();
const page = await browser.newPage();
await page.goto(new URL('paper.html', here).href, { waitUntil: 'load' });
await page.evaluate(() => document.fonts.ready);
await page.pdf({
  path: new URL('paper.pdf', here).pathname, format: 'A4', printBackground: true,
  margin: { top: '22mm', bottom: '22mm', left: '24mm', right: '24mm' },
  displayHeaderFooter: true, headerTemplate: '<span></span>',
  footerTemplate: '<div style="width:100%;text-align:center;font-size:8pt;font-family:serif"><span class="pageNumber"></span></div>',
});
await browser.close();
console.log('paper.html, paper.pdf');
