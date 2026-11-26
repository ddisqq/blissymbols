/*
 * Renders each poem token's 3D model (poem/3d/*.glb) to a PNG (poem/3d/*.png).
 *   node tools/render_poem_3d.js [poem-folder]   (default: poem/; e.g. poem/crossing-the-river)
 * Needs Playwright with Chromium. Set THREE_LOCAL=/path/to/node_modules/three (the package folder)
 * to serve three.js from disk instead of unpkg (useful offline).
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const { chromium } = require('playwright');

const REPO = path.resolve(__dirname, '..');
const TYPES = { '.html': 'text/html', '.js': 'application/javascript', '.glb': 'model/gltf-binary', '.json': 'application/json' };

function serve() {
  return new Promise((resolve) => {
    const srv = http.createServer((req, res) => {
      const p = path.join(REPO, decodeURIComponent(req.url.split('?')[0]));
      fs.readFile(p, (err, data) => {
        if (err) { res.writeHead(404); return res.end(); }
        res.writeHead(200, { 'Content-Type': TYPES[path.extname(p)] || 'application/octet-stream' });
        res.end(data);
      });
    }).listen(0, '127.0.0.1', () => resolve(srv));
  });
}

(async () => {
  const srv = await serve();
  const base = `http://127.0.0.1:${srv.address().port}`;
  const browser = await chromium.launch({ args: ['--use-gl=swiftshader', '--enable-webgl', '--ignore-gpu-blocklist'] });
  const page = await browser.newPage({ viewport: { width: 480, height: 360 }, deviceScaleFactor: 1 });
  page.on('pageerror', (e) => console.error('page error:', e.message));
  if (process.env.THREE_LOCAL) {
    await page.route('https://unpkg.com/three@0.160.0/**', (route) => {
      const rel = new URL(route.request().url()).pathname.replace('/three@0.160.0/', '');
      route.fulfill({ path: path.join(process.env.THREE_LOCAL, rel), contentType: 'application/javascript' });
    });
  }
  await page.goto(`${base}/tools/render3d.html`);
  await page.waitForFunction('window.ready === true', null, { timeout: 60000 });

  const folder = process.argv[2] || 'poem';
  const poem = JSON.parse(fs.readFileSync(path.join(REPO, folder, 'poem.json'), 'utf8'));
  let n = 0;
  for (const rec of Object.values(poem.tokens)) {
    await page.evaluate((u) => window.renderModel(u), `${base}/${folder}/${rec.glb}`);
    await page.locator('canvas').screenshot({ path: path.join(REPO, folder, rec.png) });
    n++;
  }
  console.log(`rendered ${n} 3D pictures`);
  await browser.close();
  srv.close();
})().catch((e) => { console.error(e); process.exit(1); });
