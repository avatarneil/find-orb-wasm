// SPDX-License-Identifier: GPL-2.0-or-later
import {test, expect} from '@playwright/test';
import {createServer} from 'node:http';
import {readFile} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {loadCases} from '../../benchmark/cases.mjs';
import {validate} from '../../benchmark/accuracy.mjs';

const root = resolve('.'), dist = resolve(process.env.FIND_ORB_BROWSER_DIST || 'dist-compact');
const manifest = JSON.parse(await readFile(join(dist, 'manifest.json'), 'utf8'));
const command = (await loadCases()).find(item => item.id === 'ceres-30d');
let app, cdn, appURL, dataURL;
const listen = server => new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const close = server => new Promise(resolve => server.close(resolve));

test.beforeAll(async () => {
  cdn = createServer(async (request, response) => {
    if (request.url !== '/find-orb.data.gz') {response.writeHead(404).end(); return;}
    try {
      response.setHeader('Access-Control-Allow-Origin', '*');
      // This header is intentionally NOT in Access-Control-Expose-Headers.
      // Browser fetch still decodes the body but hides the header from JS.
      response.setHeader('Content-Encoding', 'gzip');
      response.setHeader('Content-Type', 'application/octet-stream');
      response.end(await readFile(join(dist, 'find-orb.data.gz')));
    } catch {response.writeHead(500).end();}
  });
  app = createServer(async (request, response) => {
    try {
      if (request.url === '/') {
        response.setHeader('Content-Type', 'text/html');
        response.end('<!doctype html><title>Cross-origin Find_Orb data test</title>');
        return;
      }
      let file;
      if (/^\/src\/[a-z.-]+\.js$/.test(request.url)) file = join(root, request.url);
      else if (request.url === '/find-orb-worker.js') file = join(dist, 'find-orb-worker.js');
      else {response.writeHead(404).end(); return;}
      response.setHeader('Content-Type', 'text/javascript');
      response.end(await readFile(file));
    } catch {response.writeHead(500).end();}
  });
  await listen(app); await listen(cdn);
  appURL = 'http://127.0.0.1:' + app.address().port;
  dataURL = 'http://127.0.0.1:' + cdn.address().port + '/find-orb.data.gz';
});

test.afterAll(async () => {await close(app); await close(cdn);});

test('CDN gzip with a CORS-hidden Content-Encoding header loads without double decoding', async ({page}) => {
  await page.goto(appURL);
  const result = await page.evaluate(async ({manifest, command, dataURL}) => {
    const probe = await fetch(dataURL);
    const visibleEncoding = probe.headers.get('content-encoding');
    await probe.body.cancel();
    const {createSessionFromUrls} = await import('/src/index.js');
    const session = await createSessionFromUrls({
      workerURL: '/find-orb-worker.js', dataURL, manifest, compression: 'gzip',
    });
    try {
      return {visibleEncoding, calculation: await session.execute(command.args, command.files, command.outputs)};
    } finally {session.close();}
  }, {manifest, command, dataURL});
  expect(result.visibleEncoding).toBeNull();
  validate(command, result.calculation);
});
