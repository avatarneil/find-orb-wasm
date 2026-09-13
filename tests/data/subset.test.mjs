// SPDX-License-Identifier: GPL-2.0-or-later
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {gunzipSync, brotliDecompressSync} from 'node:zlib';
import {subsetEphemeris, inspectEphemeris, sha256, DEFAULT_WINDOW} from '../../data/compact.mjs';
import {EPHEMERIS} from '../../build/pins.mjs';
// Missing build/data prerequisites fail visibly; no silent skips.
const full = await readFile(new URL('../../.cache/' + EPHEMERIS.filename, import.meta.url));
const subset = subsetEphemeris(full);
test('crop preserves every selected coefficient and all constants bytes', () => {
  const m = subset.metadata, r = m.recordBytes;
  assert.deepEqual(subset.bytes.subarray(r, r * 2), full.subarray(r, r * 2));
  assert.deepEqual(subset.bytes.subarray(r * 2), full.subarray((m.firstRecord + 2) * r, (m.firstRecord + m.records + 2) * r));
  assert.equal(sha256(full), EPHEMERIS.sha256);
  assert.ok(m.supportedStartExclusiveJD < DEFAULT_WINDOW.startJD);
  assert.ok(m.supportedEndInclusiveJD > DEFAULT_WINDOW.endJD);
  assert.equal(inspectEphemeris(subset.bytes).records, m.records);
});
test('crop headers report the actual supported interval', () => {
  const m = subset.metadata;
  assert.equal(subset.bytes.readDoubleLE(2652), m.supportedStartExclusiveJD);
  assert.equal(subset.bytes.readDoubleLE(2660), m.supportedEndInclusiveJD);
  assert.match(subset.bytes.toString('ascii', 84, 168), /1999-NOV-22/);
  assert.match(subset.bytes.toString('ascii', 168, 252), /2040-FEB-08/);
});
test('untrusted and malformed sources fail before extraction', () => {
  const damaged = Buffer.from(full); damaged[20000] ^= 1;
  assert.throws(() => subsetEphemeris(damaged), /checksum/);
  const truncated = subset.bytes.subarray(0, subset.bytes.length - 1);
  assert.throws(() => inspectEphemeris(truncated), /record length/);
  const misdated = Buffer.from(subset.bytes); misdated.writeDoubleLE(1, 2 * subset.metadata.recordBytes);
  assert.throws(() => inspectEphemeris(misdated), /record dates/);
});
test('invalid date windows and missing boundary margins fail', () => {
  for (const options of [{startJD: NaN}, {endJD: Infinity}, {startJD: 1}, {startJD: 2467000}, {marginRecords: 0}, {marginRecords: 1.5}])
    assert.throws(() => subsetEphemeris(full, options), /in-range JD window/);
});
test('published compact gzip and Brotli reconstruct the verified pack exactly', async () => {
  const location = new URL('../../dist-compact/', import.meta.url);
  const manifest = JSON.parse(await readFile(new URL('manifest.json', location), 'utf8'));
  const bytes = await readFile(new URL(manifest.pack.filename, location));
  assert.equal(sha256(bytes), manifest.pack.sha256);
  for (const [name, decompress] of [['gzip', gunzipSync], ['brotli', brotliDecompressSync]]) {
    const encoding = manifest.pack.encodings[name], encoded = await readFile(new URL(encoding.filename, location));
    assert.equal(encoded.length, encoding.size); assert.equal(sha256(encoded), encoding.sha256);
    assert.deepEqual(decompress(encoded), bytes);
  }
  const worker = await readFile(new URL('find-orb-worker.js', location));
  assert.equal(sha256(worker), manifest.workerSHA256);
});
