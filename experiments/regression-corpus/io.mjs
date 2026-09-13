// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdir, readFile, writeFile} from 'node:fs/promises';
import {gzipSync, gunzipSync} from 'node:zlib';
import {setTimeout as delay} from 'node:timers/promises';
import {fileURLToPath} from 'node:url';
import {resolve} from 'node:path';

export const root = fileURLToPath(new URL('./', import.meta.url));
export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
export const json = value => JSON.stringify(value, null, 2) + '\n';
export async function existing(path) {
  try { return await readFile(path, 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return null; throw error; }
}
export async function immutableJson(name, value) {
  const path = resolve(root, name), text = json(value), previous = await existing(path);
  if (previous === null) await writeFile(path, text, {flag: 'wx'});
  else assert.equal(previous, text, `${name} changed; preserve this corpus and create a new version`);
  return sha256(text);
}
export async function request(key, endpoint, query, {offline = false, horizons = false} = {}) {
  assert(/^[a-z0-9_-]+$/.test(key));
  assert(['https://ssd-api.jpl.nasa.gov/sbdb_query.api', 'https://ssd.jpl.nasa.gov/api/horizons.api'].includes(endpoint));
  const params = horizons ? Object.fromEntries(Object.entries(query).map(([k, v]) =>
    [k, k === 'format' || k === 'TLIST' ? v : `'${v}'`])) : query;
  const url = endpoint + '?' + new URLSearchParams(params);
  assert(url.length < 7800, 'Query is too long; split its predeclared time list');
  const path = `raw/${key}.json.gz`, absolute = resolve(root, path);
  await mkdir(resolve(root, 'raw'), {recursive: true});
  let bytes;
  try { bytes = await readFile(absolute); }
  catch (error) { if (error.code !== 'ENOENT') throw error; }
  if (!bytes) {
    assert(!offline, `Offline response missing: ${path}`);
    let response, lastError;
    for (let attempt = 0; attempt < 3; attempt++) {
      try {
        response = await fetch(url, {signal: AbortSignal.timeout(45000)});
        if (response.ok || ![429, 500, 502, 503, 504].includes(response.status)) break;
        await response.arrayBuffer();
      } catch (error) { lastError = error; }
      if (attempt < 2) await delay(1000 * (attempt + 1));
    }
    assert(response, `${key}: request failed after three attempts: ${lastError}`);
    assert(response.ok, `${key}: HTTP ${response.status}`);
    const responseText = await response.text();
    JSON.parse(responseText); // Invalid transport bodies are not cached.
    const text = json({schemaVersion: 1, query, url, retrievedAt: new Date().toISOString(),
      responseSha256: sha256(responseText), responseText});
    bytes = gzipSync(text, {level: 9});
    await writeFile(absolute, bytes, {flag: 'wx'});
    await delay(350); // Strictly sequential, bounded requests; no fan-out.
  }
  const text = gunzipSync(bytes), saved = JSON.parse(text);
  assert.equal(saved.schemaVersion, 1);
  assert.deepEqual(saved.query, query, `${key}: cache query mismatch`);
  assert.equal(saved.url, url, `${key}: cache URL mismatch`);
  assert.equal(sha256(saved.responseText), saved.responseSha256, `${key}: response checksum mismatch`);
  return {document: JSON.parse(saved.responseText), ref: {path, sha256: sha256(bytes), bytes: bytes.length,
    uncompressedSha256: sha256(text), responseSha256: saved.responseSha256, retrievedAt: saved.retrievedAt}};
}
