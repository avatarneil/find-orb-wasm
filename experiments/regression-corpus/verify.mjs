// SPDX-License-Identifier: GPL-2.0-or-later
// Offline integrity authority: hashes, coverage, frozen choices and exact replay.
import assert from 'node:assert/strict';
import {readFile, readdir, lstat} from 'node:fs/promises';
import {resolve} from 'node:path';
import {spawnSync} from 'node:child_process';
import {gunzipSync} from 'node:zlib';
import {root, sha256} from './io.mjs';

assert.equal(process.argv.length, 2, 'verify.mjs takes no arguments and never downloads data');
const read = async name => JSON.parse(await readFile(resolve(root, name), 'utf8'));
const corpusBytes = await readFile(resolve(root, 'corpus.json'));
const corpus = JSON.parse(corpusBytes);
assert.equal(corpus.schemaVersion, 1);
assert.equal(corpus.complete, true, 'Incomplete corpus cannot pass verification');
const protocol = await read('protocol.json'), selection = await read('selection.json');
const generation = await read('generation-protocol.json');
const cometSelection = await read('comet-record-selection.json');
const history = await read('acquisition-history.json');

for (const stem of ['protocol', 'selection', 'generationProtocol', 'cometRecordSelection', 'acquisitionHistory']) {
  const name = corpus.provenance[stem + 'File'];
  assert.match(name, /^[a-z-]+\.json$/, 'Safe provenance path');
  assert.equal(sha256(await readFile(resolve(root, name))), corpus.provenance[stem + 'Sha256'], name + ' checksum');
}
assert.equal(selection.protocolSha256, corpus.provenance.protocolSha256);
assert.equal(cometSelection.selectionSha256, corpus.provenance.selectionSha256);
assert.equal(selection.frozenAt, corpus.provenance.selectionFrozenAt);
assert.deepEqual(corpus.objects, selection.objects, 'Every frozen catalog identity is retained');
const expectedSources = ['catalog.mjs', 'fetch.mjs', 'io.mjs', 'resolve-comets.mjs'];
assert.deepEqual(Object.keys(corpus.provenance.generatorSources).sort(), expectedSources);
for (const [name, hash] of Object.entries(corpus.provenance.generatorSources)) {
  assert.equal(sha256(await readFile(resolve(root, name))), hash, name + ' source checksum');
}

const objects = new Map(selection.objects.map(body => [body.spkid, body]));
assert.equal(objects.size, 96, 'All 96 distinct frozen objects');
assert.equal(selection.objects.length, objects.size);
const casesByObject = new Map(), unavailableIds = new Set();
const ids = new Set();
for (const c of corpus.cases) {
  assert.ok(!ids.has(c.id), 'Unique case ID'); ids.add(c.id);
  const body = objects.get(c.objectId);
  assert.ok(body, 'Case belongs to a frozen object');
  assert.equal(c.split, body.split, 'Object-level split');
  assert.equal(c.knownRegression, body.knownRegression);
  assert.equal(c.object.designation, body.pdes);
  assert.equal(c.observer, protocol.observer);
  assert.equal(c.astrometry.length, 37, 'Complete predeclared astrometry bank');
  assert.equal(c.truthEpochs.length, 6, 'Initial state plus all five arc endpoints');
  assert.deepEqual(c.arcs.map(arc => arc.id), protocol.arcs.map(arc => arc.id));
  for (let i = 0; i < c.arcs.length; i++) {
    const arc = c.arcs[i], spec = protocol.arcs[i];
    const observations = spec.trackletDays.flatMap(day => protocol.exposureMinutes.map(minute => c.anchorJdUtc + day + minute / 1440));
    assert.equal(arc.observationIndices.length, observations.length);
    arc.observationIndices.forEach((index, j) => {
      assert.ok(Math.abs(c.astrometry[index].requestedJdUtc - observations[j]) < 1e-9, 'Declared observation schedule');
    });
    assert.equal(arc.predictionIndices.length, 3);
    arc.predictionIndices.forEach((index, j) => {
      assert.ok(Math.abs(c.astrometry[index].requestedJdUtc - observations.at(-1) - protocol.forecastDaysAfterEachArc[j]) < 1e-9,
        'Forecasts follow this arc endpoint by +1/+3/+7 days');
    });
    assert.ok(Math.abs(c.truthEpochs[arc.truthEpochIndex].jdUtc - observations.at(-1)) < 1e-9, 'Matched requested state epoch');
  }
  for (const point of c.astrometry) {
    assert.ok(Math.abs(point.jdUtc - point.requestedJdUtc) <= 0.001 / 86400, 'Documented observer epoch precision');
    assert.ok(Number.isFinite(point.RA) && point.RA >= 0 && point.RA < 360);
    assert.ok(Number.isFinite(point.Dec) && Math.abs(point.Dec) <= 90);
  }
  for (const truth of c.truthEpochs) {
    assert.equal(truth.state.horizonsJdTdb, truth.elements.horizonsJdTdb, 'State and elements returned at same epoch');
    assert.ok(Math.abs(truth.state.horizonsJdTdb - truth.jdTdb) <= 2e-9, 'Geometric output epoch precision');
  }
  assert.equal(c.applicability.fit, true);
  assert.ok(['strict', 'model-limited'].includes(c.applicability.forwardTruth));
  assert.equal(c.applicability.toleranceArcsec, c.applicability.forwardTruth === 'strict' ? 0.1 : null);
  assert.ok(c.model.reasonCodes.length === 0 ? c.applicability.forwardTruth === 'strict' : c.applicability.forwardTruth === 'model-limited');
  if (body.kind.startsWith('c')) assert.equal(c.applicability.forwardTruth, 'model-limited', 'Comet physical model remains limited');
  if (!casesByObject.has(c.objectId)) casesByObject.set(c.objectId, []);
  casesByObject.get(c.objectId).push(c);
}
for (const item of corpus.unavailable) {
  assert.ok(objects.has(item.objectId) && !casesByObject.has(item.objectId) && !unavailableIds.has(item.objectId));
  assert.ok(item.rawFiles.length > 0 && item.reason.length > 0, 'Unavailable references retain explicit raw evidence');
  unavailableIds.add(item.objectId);
}
for (const body of selection.objects) {
  if (unavailableIds.has(body.spkid)) continue;
  const cases = casesByObject.get(body.spkid);
  assert.ok(cases, 'Every frozen object is usable or explicitly unavailable');
  const core = cases.filter(c => c.role === 'core');
  assert.deepEqual(core.map(c => c.anchorUtc), protocol.anchorsUtc, 'Both independent anchors per usable object');
  const extras = protocol.supplements.filter(item => item.pdes === body.pdes);
  assert.equal(cases.length, core.length + extras.length, 'All declared temporal supplements');
}
const counts = {plannedObjects: objects.size, completedObjects: casesByObject.size + unavailableIds.size,
  usableObjects: casesByObject.size, usableCases: corpus.cases.length,
  coreCases: corpus.cases.filter(c => c.role === 'core').length,
  temporalSupplementCases: corpus.cases.filter(c => c.role === 'temporal-supplement').length,
  unavailableObjects: unavailableIds.size};
assert.deepEqual(corpus.counts, counts, 'Published counts match actual coverage');
assert.equal(counts.completedObjects, 96);
assert.ok(counts.usableObjects >= 80 && counts.coreCases >= 160, 'Substantial usable dataset acceptance guard');
const expectedSentinels = protocol.catalog.strata.flatMap(stratum => {
  const body = selection.objects.find(value => value.stratum === stratum.id);
  const first = corpus.cases.find(c => c.objectId === body.spkid && c.role === 'core');
  return first ? [first.id] : [];
});
assert.deepEqual(corpus.suite.sentinelIds, expectedSentinels, 'Frozen sentinel selection');
assert.deepEqual(corpus.suite.defaultArcs, protocol.arcs.map(arc => arc.id));
assert.equal(generation.observerBatchEpochs, 40);

const references = new Map();
const addRef = ref => {
  assert.match(ref.path, /^raw\/[a-z0-9_-]+\.json\.gz$/, 'Safe raw path');
  if (references.has(ref.path)) assert.deepEqual(references.get(ref.path), ref, 'Consistent duplicate raw reference');
  else references.set(ref.path, ref);
};
for (const ref of [...selection.rawFiles, ...cometSelection.records.map(record => record.lookup),
  ...history.records.map(record => record.rawFile), ...corpus.cases.flatMap(c => c.rawFiles),
  ...corpus.unavailable.flatMap(item => item.rawFiles)]) addRef(ref);
assert.deepEqual(corpus.provenance.rawFiles, [...references.values()].sort((a, b) => a.path.localeCompare(b.path)), 'Every raw response is indexed exactly once');
assert.deepEqual((await readdir(resolve(root, 'raw'))).sort(), [...references.keys()].map(path => path.slice(4)).sort(),
  'No missing or unindexed raw files, including failed preflight history');
const documents = new Map();
let rawBytes = 0, decodedBytes = 0;
for (const ref of references.values()) {
  const path = resolve(root, ref.path), stat = await lstat(path);
  assert.ok(stat.isFile() && !stat.isSymbolicLink(), 'Raw reference must be a regular file');
  const compressed = await readFile(path), decoded = gunzipSync(compressed);
  assert.equal(compressed.length, ref.bytes, ref.path + ' byte size');
  assert.equal(sha256(compressed), ref.sha256, ref.path + ' compressed checksum');
  assert.equal(sha256(decoded), ref.uncompressedSha256, ref.path + ' envelope checksum');
  const envelope = JSON.parse(decoded), document = JSON.parse(envelope.responseText);
  assert.equal(envelope.schemaVersion, 1);
  assert.equal(sha256(envelope.responseText), envelope.responseSha256, ref.path + ' response checksum');
  assert.equal(envelope.responseSha256, ref.responseSha256);
  assert.equal(envelope.retrievedAt, ref.retrievedAt);
  assert.ok(Number.isFinite(Date.parse(envelope.retrievedAt)), 'Retrieval timestamp');
  const endpoint = ref.path.startsWith('raw/catalog-') ? protocol.catalog.endpoint : 'https://ssd.jpl.nasa.gov/api/horizons.api';
  const horizons = endpoint.includes('horizons');
  const params = horizons ? Object.fromEntries(Object.entries(envelope.query).map(([key, value]) =>
    [key, key === 'format' || key === 'TLIST' ? value : `'${value}'`])) : envelope.query;
  assert.equal(envelope.url, endpoint + '?' + new URLSearchParams(params), ref.path + ' exact query URL');
  assert.equal(document.signature?.source, horizons ? 'NASA/JPL Horizons API' : 'NASA/JPL SBDB (Small-Body DataBase) Query API');
  assert.ok((horizons ? ['1.2', '1.3'] : ['1.0']).includes(document.signature.version), 'Pinned API version');
  documents.set(ref.path, document); rawBytes += compressed.length; decodedBytes += decoded.length;
}
for (const c of corpus.cases) for (const header of Object.values(c.model.exactHeaders)) {
  assert.equal(header.responseResultPrefixBefore, '$$SOE');
  const prefix = documents.get(header.rawPath)?.result?.split('$$SOE')[0];
  assert.equal(typeof prefix, 'string', 'Referenced exact header exists');
  assert.equal(sha256(prefix), header.sha256, 'Exact physical model header checksum');
  assert.equal(Buffer.byteLength(prefix), header.bytes);
}

// Reconstruct both catalog choice and every parsed value from pinned responses.
// Offline fetch rejects any difference and never writes the completed corpus.
for (const script of ['catalog.mjs', 'resolve-comets.mjs', 'fetch.mjs']) {
  const args = [resolve(root, script), ...(script === 'resolve-comets.mjs' ? [] : ['--offline'])];
  const result = spawnSync(process.execPath, args, {cwd: root, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024});
  assert.equal(result.status, 0, script + ' offline replay failed:\n' + result.stderr + '\n' + result.stdout);
}
assert.equal(sha256(await readFile(resolve(root, 'corpus.json'))), sha256(corpusBytes), 'Verification did not alter corpus bytes');
process.stdout.write(JSON.stringify({verified: true, corpusSha256: sha256(corpusBytes), ...counts,
  sentinelCases: expectedSentinels.length, arcProblems: corpus.cases.length * protocol.arcs.length,
  astrometryPositions: corpus.cases.reduce((n, c) => n + c.astrometry.length, 0),
  matchedStateElementPairs: corpus.cases.reduce((n, c) => n + c.truthEpochs.length, 0),
  rawFiles: references.size, rawCompressedBytes: rawBytes, rawDecodedBytes: decodedBytes,
  splitObjects: Object.fromEntries(['development', 'regression-holdout'].map(split => [split, selection.objects.filter(body => body.split === split).length])),
  applicabilityCases: Object.fromEntries(['strict', 'model-limited'].map(value => [value, corpus.cases.filter(c => c.applicability.forwardTruth === value).length])),
  offlineReplayByteIdentical: true}, null, 2) + '\n');
