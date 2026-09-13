// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {after, before, test} from 'node:test';
import {cp, mkdtemp, readFile, rm, unlink, writeFile} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {resolve} from 'node:path';
import {spawnSync} from 'node:child_process';
import {gzipSync, gunzipSync} from 'node:zlib';
import {root, sha256} from './io.mjs';

let temporary, corpus, originalCorpus;
before(async () => {
  temporary = await mkdtemp(resolve(tmpdir(), 'find-orb-corpus-integrity-'));
  await cp(root, temporary, {recursive: true});
  originalCorpus = await readFile(resolve(temporary, 'corpus.json'));
  corpus = JSON.parse(originalCorpus);
});
after(async () => { if (temporary) await rm(temporary, {recursive: true, force: true}); });

function run(script, args = []) {
  return spawnSync(process.execPath, [resolve(temporary, script), ...args],
    {cwd: temporary, encoding: 'utf8', timeout: 30000, maxBuffer: 8 * 1024 * 1024});
}
async function mutated(path, change, check) {
  const absolute = resolve(temporary, path), original = await readFile(absolute);
  try {
    const changed = await change(original);
    if (changed === null) await unlink(absolute); else await writeFile(absolute, changed);
    await check();
    assert.deepEqual(await readFile(resolve(temporary, 'corpus.json')), originalCorpus,
      'Failed validation must leave the published corpus untouched');
  } finally { await writeFile(absolute, original); }
}
function reject(script, args, pattern) {
  const result = run(script, args);
  assert.equal(result.error, undefined, 'Verifier completed normally');
  assert.notEqual(result.status, 0, 'Invalid evidence must fail');
  assert.match(result.stderr, pattern);
}
function editResult(bytes, change) {
  const envelope = JSON.parse(gunzipSync(bytes)), document = JSON.parse(envelope.responseText);
  document.result = change(document.result);
  envelope.responseText = JSON.stringify(document);
  envelope.responseSha256 = sha256(envelope.responseText);
  return gzipSync(JSON.stringify(envelope));
}
const firstObserver = () => corpus.cases[0].model.exactHeaders.observer.rawPath;

test('complete frozen corpus verifies and replays byte-identically offline', () => {
  const result = run('verify.mjs');
  assert.equal(result.status, 0, result.stderr);
  const report = JSON.parse(result.stdout);
  assert.equal(report.offlineReplayByteIdentical, true);
  assert.equal(report.usableObjects, 96);
  assert.equal(report.coreCases, 192);
});

test('missing raw source fails closed without overwriting corpus', async () => {
  await mutated(firstObserver(), () => null, () => {
    reject('verify.mjs', [], /missing or unindexed raw files/i);
    reject('fetch.mjs', ['--offline'], /Offline response missing/);
  });
});

test('corrupt compressed source fails closed', async () => {
  await mutated(firstObserver(), bytes => Buffer.from('corrupt gzip'), () => {
    reject('verify.mjs', [], /header|gzip|data/i);
    reject('fetch.mjs', ['--offline'], /header|gzip|data/i);
  });
});

test('self-consistent cache URL tampering is rejected', async () => {
  await mutated(firstObserver(), bytes => {
    const envelope = JSON.parse(gunzipSync(bytes));
    envelope.url += '&unrequested=true'; return gzipSync(JSON.stringify(envelope));
  }, () => reject('fetch.mjs', ['--offline'], /cache URL mismatch/));
});

test('equivalent response recompression still violates pinned source identity', async () => {
  await mutated(firstObserver(), bytes => gzipSync(gunzipSync(bytes), {level: 1}), () => {
    reject('verify.mjs', [], /byte size|compressed checksum/);
    reject('fetch.mjs', ['--offline'], /Offline replay differs/);
  });
});

test('nondecimal RA cannot be silently coerced into a valid number', async () => {
  await mutated(firstObserver(), bytes => editResult(bytes, text => {
    const [header, rest] = text.split('$$SOE'), lines = rest.split('\n');
    const firstRow = lines.findIndex(line => line.includes(',')), values = lines[firstRow].split(',');
    values[3] = '0x10'; lines[firstRow] = values.join(','); return header + '$$SOE' + lines.join('\n');
  }), () => reject('fetch.mjs', ['--offline'], /invalid decimal\/scientific number/));
});

test('mixed Horizons orbit solution IDs cannot pass orbital invariant checks alone', async () => {
  const path = corpus.cases[0].model.exactHeaders.state.rawPath;
  await mutated(path, bytes => editResult(bytes, text => text.replace(/(Target body name:.*\{source: )[^}]+/, '$1JPL#999999999')),
    () => reject('fetch.mjs', ['--offline'], /Target orbit solution changed/));
});

test('malformed API signature cannot be classified as scientific unavailability', async () => {
  await mutated(firstObserver(), bytes => {
    const envelope = JSON.parse(gunzipSync(bytes));
    envelope.responseText = JSON.stringify({signature: {source: 'unknown', version: '1.2'}, error: 'not available'});
    envelope.responseSha256 = sha256(envelope.responseText); return gzipSync(JSON.stringify(envelope));
  }, () => reject('fetch.mjs', ['--offline'], /Unknown Horizons response source/));
});

test('partial publication is rejected before any offline reconstruction', async () => {
  const path = resolve(temporary, 'corpus.json');
  const incomplete = Buffer.from(JSON.stringify({...corpus, complete: false}));
  try {
    await writeFile(path, incomplete);
    reject('verify.mjs', [], /Incomplete corpus/);
    reject('fetch.mjs', ['--offline'], /previously completed corpus/);
    assert.deepEqual(await readFile(path), incomplete);
  } finally { await writeFile(path, originalCorpus); }
});

test('falsified coverage counts cannot mark a completed corpus accepted', async () => {
  const path = resolve(temporary, 'corpus.json');
  const changed = Buffer.from(JSON.stringify({...corpus, counts: {...corpus.counts, coreCases: 160}}));
  try {
    await writeFile(path, changed);
    reject('verify.mjs', [], /Published counts match actual coverage/);
    assert.deepEqual(await readFile(path), changed);
  } finally { await writeFile(path, originalCorpus); }
});
