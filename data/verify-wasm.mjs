#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {readFile, writeFile, mkdir} from 'node:fs/promises';
import {resolve, dirname} from 'node:path';
import {loadWasm} from '../benchmark/engines.mjs';
import {loadCases, stateCommand} from '../benchmark/cases.mjs';
import {validate} from '../benchmark/accuracy.mjs';
import {EPHEMERIS} from '../build/pins.mjs';
const options = {full: resolve('dist'), compact: resolve('dist-compact'), out: resolve('results/local/dataset-wasm.json')};
for (let i = 2; i < process.argv.length; i += 2) {
  const key = process.argv[i].slice(2);
  if (!Object.hasOwn(options, key) || !process.argv[i + 1]) throw new Error('Options: --full DIST --compact DIST_COMPACT --out REPORT_JSON');
  options[key] = resolve(process.argv[i + 1]);
}
const full = await loadWasm(options.full), compact = await loadWasm(options.compact);
assert.equal(full.manifest.binarySHA256, compact.manifest.binarySHA256, 'same compiled engine');
const subset = compact.manifest.ephemeris.subset;
assert.ok(subset, 'compact manifest has an explicit supported interval');
const report = {schema: 1, engineSHA256: full.manifest.binarySHA256, fullPackSHA256: full.manifest.pack.sha256,
  compactPackSHA256: compact.manifest.pack.sha256, ignoredMetadata: ['elements.txt: # Elements written wall-clock line', 'elements.json: created and created iso wall-clock fields'], cases: [], guards: []};
function normalize(name, text) {
  if (name.endsWith('elements.txt')) return text.replace(/^# Elements written:.*\r?\n/gm, '');
  if (name.endsWith('.json')) {
    const parsed = JSON.parse(text);
    for (const object of Object.values(parsed.objects || {})) {delete object.created; delete object['created iso'];}
    return parsed;
  }
  return text;
}
for (const command of await loadCases()) {
  console.log('Data equivalence: ' + command.id);
  const a = await full.execute(command), b = await compact.execute(command);
  const accuracy = validate(command, b);
  assert.deepEqual(Object.keys(a.files), Object.keys(b.files));
  for (const name of Object.keys(a.files)) assert.deepEqual(normalize(name, a.files[name]), normalize(name, b.files[name]), 'exact output parity: ' + command.id + ' ' + name);
  report.cases.push({id: command.id, exactScientificOutputs: true, files: Object.keys(a.files), accuracy});
}
const state = [1.842066453749, 2.100073008903, -.272870386667, -.007964937613003, .006136285229858, .001661644856635];
const originalExitCode = process.exitCode;
for (const [label, epoch] of [['before-start', subset.supportedStartExclusiveJD - 1], ['after-end', subset.supportedEndInclusiveJD + 1], ['excluded-lower-endpoint', subset.supportedStartExclusiveJD]]) {
  const command = stateCommand(state, {epoch, count: 1});
  let message;
  await assert.rejects(async () => {try {await compact.execute(command);} catch (error) {message = error.message; throw error;}}, /JPL ephemeris unavailable.*outside supported/s);
  report.guards.push({id: label, rejected: true, epoch, message});
}
// Exercise the actual reader error branch after valid header initialization.
// Deliberately corrupt only an in-memory verified-test copy after verification;
// this simulates an I/O truncation without publishing a corrupted distribution.
const damaged = await loadWasm(options.compact);
const damagedEntry = damaged.manifest.entries[EPHEMERIS.filename];
const oldSize = damagedEntry.size;
damagedEntry.size = subset.recordBytes * 2;
try {
  await assert.rejects(() => damaged.execute(stateCommand(state, {count: 1})), /JPL ephemeris evaluation failed.*analytic fallback is disabled/s);
  report.guards.push({id: 'reader-truncated-after-header', rejected: true});
} finally {damagedEntry.size = oldSize;}
const missing = await loadWasm(options.compact);
const saved = missing.manifest.entries[EPHEMERIS.filename];
delete missing.manifest.entries[EPHEMERIS.filename];
await assert.rejects(() => missing.execute(stateCommand(state, {count: 1})), /JPL ephemeris (unavailable|could not be loaded)/s);
missing.manifest.entries[EPHEMERIS.filename] = saved;
report.guards.push({id: 'missing-ephemeris', rejected: true});
// Emscripten's Node quit shim records the intentional native failure status.
// These assertions caught those expected failures, so restore the test status.
process.exitCode = originalExitCode;
await mkdir(dirname(options.out), {recursive: true});
await writeFile(options.out, JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report, null, 2));
