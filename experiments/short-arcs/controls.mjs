#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
// Independent-state propagation and development-only native/WASM parity.
import assert from 'node:assert/strict';
import {readFile, writeFile, mkdir} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {gzipSync} from 'node:zlib';
import os from 'node:os';
import {loadNative, loadWasm} from '../../benchmark/engines.mjs';
import {stateCommand} from '../../benchmark/cases.mjs';
import {skyRows} from '../../benchmark/accuracy.mjs';
import {fitCommand, separationArcsec, sha} from './methods.mjs';
import {evaluate, candidateRows, offsetEnsemble} from './run.mjs';
import {selectPredictive, familyRows} from './predictive.mjs';
import {patches} from './patches.mjs';

const root = fileURLToPath(new URL('../../', import.meta.url));
const numericFields = (value, prefix = '', output = {}) => {
  for (const [key, child] of Object.entries(value)) {
    const path = prefix ? prefix + '.' + key : key;
    if (typeof child === 'number') output[path] = child;
    else if (child && typeof child === 'object') numericFields(child, path, output);
  }
  return output;
};
function numericalComparison(a, b) {
  const left = numericFields(a), right = numericFields(b);
  const keys = [...new Set([...Object.keys(left), ...Object.keys(right)])].sort();
  const differences = {}, missing = [];
  for (const key of keys) {
    if (!Number.isFinite(left[key]) || !Number.isFinite(right[key])) missing.push(key);
    else differences[key] = Math.abs(left[key] - right[key]);
  }
  return {differences, missing, maxAbsoluteDifference: Math.max(0, ...Object.values(differences))};
}
function compareSky(a, b) {
  assert.equal(a.length, b.length, 'matched ephemeris length');
  const errors = a.map((point, i) => {
    assert.ok(Math.abs(point.JD - b[i].JD) < 1e-7, 'matched UTC prediction epochs');
    return separationArcsec(point, b[i]);
  });
  const fields = {};
  for (let i = 0; i < a.length; i++) {
    const comparison = numericalComparison(a[i], b[i]);
    for (const [key, value] of Object.entries(comparison.differences)) fields[key] = Math.max(fields[key] || 0, value);
  }
  return {maxSeparationArcsec: Math.max(...errors), separationArcsecByEpoch: errors,
    maxAbsoluteDifferenceByNumericField: fields, exactJSONEquality: JSON.stringify(a) === JSON.stringify(b)};
}
function compareCandidates(a, b) {
  const rowsA = candidateRows(a.files['/job/candidates.csv'] || '');
  const rowsB = candidateRows(b.files['/job/candidates.csv'] || '');
  const indicesIdentical = JSON.stringify(rowsA.map(row => row.source_index)) === JSON.stringify(rowsB.map(row => row.source_index));
  const acceptedA = rowsA.filter(row => row.heuristic_score < .7), acceptedB = rowsB.filter(row => row.heuristic_score < .7);
  const maxima = Array(6).fill(0);
  let weightedRmsDifference = 0, heuristicScoreDifference = 0;
  if (indicesIdentical) for (let i = 0; i < rowsA.length; i++) {
    for (let j = 0; j < 6; j++) maxima[j] = Math.max(maxima[j], Math.abs(rowsA[i].state[j] - rowsB[i].state[j]));
    weightedRmsDifference = Math.max(weightedRmsDifference, Math.abs(rowsA[i].weighted_rms - rowsB[i].weighted_rms));
    heuristicScoreDifference = Math.max(heuristicScoreDifference, Math.abs(rowsA[i].heuristic_score - rowsB[i].heuristic_score));
  }
  const familyA = a.files['/job/family.csv']?.trim() ? familyRows(a.files['/job/family.csv']) : [];
  const familyB = b.files['/job/family.csv']?.trim() ? familyRows(b.files['/job/family.csv']) : [];
  return {generatedCounts: [rowsA.length, rowsB.length], acceptedCounts: [acceptedA.length, acceptedB.length],
    orderedFamilyCounts: [familyA.length, familyB.length], successfulSourceIndicesIdentical: indicesIdentical,
    acceptedSourceIndicesIdentical: JSON.stringify(acceptedA.map(row => row.source_index)) === JSON.stringify(acceptedB.map(row => row.source_index)),
    maxStateDifferenceByComponent: indicesIdentical ? maxima : null, maxWeightedRmsDifference: indicesIdentical ? weightedRmsDifference : null,
    maxHeuristicScoreDifference: indicesIdentical ? heuristicScoreDifference : null,
    exactCandidateCSVEquality: a.files['/job/candidates.csv'] === b.files['/job/candidates.csv'],
    exactFamilyCSVEquality: a.files['/job/family.csv'] === b.files['/job/family.csv'],
    exactBatchCSVEquality: a.files['/job/batches.csv'] === b.files['/job/batches.csv']};
}
function fitComparison(a, b, {requireExact = false, instrumented = false} = {}) {
  if (a.error || b.error || !a.summary?.valid || !b.summary?.valid)
    return {passed: false, reason: 'One or both fit/control executions failed.', leftError: a.error || null, rightError: b.error || null};
  const leftRaw = a.predictionRaw || a.result, rightRaw = b.predictionRaw || b.result;
  const elements = numericalComparison(a.summary.elements, b.summary.elements);
  const sky = compareSky(skyRows(leftRaw), skyRows(rightRaw));
  const observationsMatch = a.summary.observations.count === b.summary.observations.count && a.summary.observations.used === b.summary.observations.used;
  const framesMatch = ['central body', 'frame'].every(key => a.summary.elements[key] === b.summary.elements[key]);
  const exactElements = JSON.stringify(a.summary.elements) === JSON.stringify(b.summary.elements);
  const scienceWithinTolerance = elements.missing.length === 0 && elements.maxAbsoluteDifference <= 1e-6 && sky.maxSeparationArcsec <= .001 && observationsMatch && framesMatch;
  const exports = instrumented ? compareCandidates(a.result, b.result) : null;
  const search = instrumented ? {left: a.summary.search, right: b.summary.search,
    attemptedTotalsMatch: a.summary.search?.attemptedTotal === b.summary.search?.attemptedTotal,
    batchJSONIdentical: JSON.stringify(a.summary.search) === JSON.stringify(b.summary.search)} : null;
  const exportCountsMatch = !instrumented || (exports.successfulSourceIndicesIdentical && exports.acceptedSourceIndicesIdentical &&
    exports.orderedFamilyCounts[0] === exports.orderedFamilyCounts[1] && search.attemptedTotalsMatch);
  return {passed: scienceWithinTolerance && exportCountsMatch && (!requireExact || (exactElements && sky.exactJSONEquality)),
    scienceWithinTolerance, requestedExact: requireExact, exactElementsJSONEquality: exactElements, observationsMatch, framesMatch,
    elementToleranceAbsolute: 1e-6, skyToleranceArcsec: .001, elements, sky, exports, search,
    predictiveIndices: [a.summary.predictive?.index ?? null, b.summary.predictive?.index ?? null]};
}

export async function runControls({output = 'results/local/short-arcs/controls-v2', corpus = 'experiments/short-arcs/fixtures/observable-corpus.json'} = {}) {
  const directory = resolve(root, output), corpusPath = resolve(root, corpus), corpusBytes = await readFile(corpusPath);
  const fixtures = JSON.parse(corpusBytes), development = fixtures.cases.filter(c => c.split === 'development');
  assert.ok(development.length > 0 && fixtures.cases.length > development.length, 'explicit object split');
  // Exclusive creation keeps evidence immutable, including interrupted runs.
  await mkdir(directory, {recursive: true});
  const manifestPath = join(directory, 'manifest.json');
  const manifest = {schemaVersion: 1, startedAt: new Date().toISOString(), corpus, corpusSHA256: sha(corpusBytes),
    scope: 'Truth-state propagation for every observable fixture; orbital fits only for development objects. No held-out fitted outcome is loaded.',
    initialStateEpochConvention: 'Horizons states at epochJdTdb are supplied at epochJdTt, labeling the same physical instant using the fixture UTC/TDB/TT conversions; velocities retain Horizons au/TDB-day units.',
    limitations: ['Horizons and Find_Orb forces, solar GM, frame realization and Earth orientation can differ.',
      'Reference-trajectory propagation is a numerical control, not proof that a short-arc inverse problem is identifiable.',
      'Fit tolerances compare printed elements in their native units and all sampled sky directions; they are empirical parity thresholds, not formal error bounds.',
      'Concurrent research/build activity means recorded timings must not be interpreted as isolated performance measurements.'],
    engines: {}, sourceSHA256: {}, host: {platform: os.platform(), arch: os.arch(), node: process.version, cpu: os.cpus()[0]?.model}};
  for (const name of ['controls.mjs', 'methods.mjs', 'run.mjs', 'predictive.mjs', 'patches.mjs'])
    manifest.sourceSHA256[name] = sha(await readFile(new URL('./' + name, import.meta.url)));
  await writeFile(manifestPath, JSON.stringify(manifest, null, 2) + '\n', {flag: 'wx'});
  const engines = {
    nativeBaseline: await loadNative(join(root, '.native-engine')),
    wasmBaseline: await loadWasm(join(root, 'dist-compact')),
    nativeExperiment: await loadNative(join(root, '.native-engine-short-arcs')),
    wasmExperiment: await loadWasm(join(root, 'dist-short-arcs')),
  };
  for (const [name, engine] of Object.entries(engines)) {
    manifest.engines[name] = {directory: engine.root, binary: engine.binary || 'fo.wasm', manifest: engine.manifest};
    if (name.endsWith('Experiment')) {
      const evidence = JSON.parse(await readFile(join(engine.root, 'short-arc-experiment.json')));
      assert.equal(evidence.patchesSHA256, sha(JSON.stringify(patches)), 'current instrumented binary patches');
      manifest.engines[name].experiment = evidence;
    }
  }
  await writeFile(manifestPath, JSON.stringify(manifest, null, 2) + '\n');
  const records = [], comparisons = [], cache = new Map();
  const save = async (id, value) => {
    const bytes = Buffer.from(JSON.stringify(value)), name = id + '.json.gz';
    await writeFile(join(directory, name), gzipSync(bytes, {level: 9}), {flag: 'wx'});
    return {file: name, uncompressedSHA256: sha(bytes), compressedSHA256: sha(await readFile(join(directory, name)))};
  };
  const summarize = async () => {
    const result = {schemaVersion: 1, updatedAt: new Date().toISOString(), records, comparisons,
      executedRecords: records.length, executionFailures: records.filter(r => r.error).length,
      comparisonsPassed: comparisons.filter(c => c.passed).length, comparisonsFailed: comparisons.filter(c => !c.passed).length};
    await writeFile(join(directory, 'summary.json'), JSON.stringify(result, null, 2) + '\n');
    return result;
  };
  const fit = async (c, engineName, selection, budget) => {
    assert.equal(c.split, 'development', 'never fit a held-out object in controls');
    const id = [c.id, engineName, selection, budget].join('_');
    if (cache.has(id)) return cache.get(id);
    const experimental = engineName.endsWith('Experiment'), engine = engines[engineName];
    let command, result, summary, predictionRaw = null, predictionCommand = null, error = null;
    try {
      command = fitCommand(c, {selection, budget, scenario: 'gaussian', replicate: 0, arc: 'one-hour', experimental});
      result = await engine.execute(command);
      summary = evaluate(c, command, result);
      if (selection === 'predictive1d') ({summary, predictionRaw, predictionCommand} = await selectPredictive(c, command, result, summary, engine, {offsetEnsemble, candidateRows}));
    } catch (failure) {error = String(failure.stack || failure);}
    const value = {id, caseId: c.id, engine: engineName, selection, budget, scenario: 'gaussian', replicate: 0,
      command: command || null, result: result || null, summary: summary || null, predictionCommand, predictionRaw, error};
    const raw = await save(id, value);
    records.push({id, kind: 'development-fit', caseId: c.id, engine: engineName, selection, budget,
      valid: Boolean(summary?.valid) && !error, used: summary?.observations?.used, search: summary?.search, predictive: summary?.predictive,
      error, raw});
    cache.set(id, value); await summarize();
    console.log(JSON.stringify({control: 'fit', id, valid: summary?.valid && !error, error: error?.split('\n')[0]}));
    return value;
  };

  for (const c of fixtures.cases) {
    const propagated = {};
    for (const engineName of ['nativeBaseline', 'wasmBaseline']) {
      const command = stateCommand([...c.state.positionAu, ...c.state.velocityAuPerDay],
        {epoch: c.epochJdTt, start: c.epochJdUtc, count: 29, step: '6h', scale: 'UTC', sky: true});
      assert.equal(c.observer, 'F52', 'state-command observer matches corpus');
      command.args.push('-tEJD' + c.epochJdTt); command.outputs.push('/job/elements.json');
      const id = c.id + '_' + engineName + '_truth-propagation';
      let result = null, error = null, predictions = null;
      try {
        result = await engines[engineName].execute(command); assert.equal(result.exitCode, 0);
        assert.match(result.files['/job/elements.txt'], /^# Perturbers:\s+[0-9a-f]+.*JPL DE-440.*$/im);
        const force = Number.parseInt(/^# Perturbers:\s+([0-9a-f]+)/im.exec(result.files['/job/elements.txt'])[1], 16);
        assert.equal(force & 0x7fe, 0x7fe, 'all planetary perturbers');
        const sky = skyRows(result); assert.equal(sky.length, command.count);
        predictions = [c.observations.at(-1), ...c.holdout].map(truth => {
          const point = sky.find(p => Math.abs(p.JD - truth.jdUtc) < 1e-7); assert.ok(point);
          return {jdUtc: truth.jdUtc, daysAfterStateEpoch: truth.jdUtc - c.epochJdUtc,
            separationArcsec: separationArcsec(point, truth), estimate: point, truth};
        });
      } catch (failure) {error = String(failure.stack || failure);}
      const raw = await save(id, {id, caseId: c.id, engine: engineName, command, result, predictions, error});
      propagated[engineName] = {result, error};
      records.push({id, kind: 'truth-propagation', caseId: c.id, split: c.split, engine: engineName, predictions,
        maxSeparationArcsec: predictions ? Math.max(...predictions.map(p => p.separationArcsec)) : null, error, raw});
      await summarize();
      console.log(JSON.stringify({control: 'truth-propagation', id, maxArcsec: records.at(-1).maxSeparationArcsec, error: error?.split('\n')[0]}));
    }
    if (Object.values(propagated).every(p => p.result && !p.error)) {
      const sky = compareSky(skyRows(propagated.nativeBaseline.result), skyRows(propagated.wasmBaseline.result));
      comparisons.push({kind: 'truth-state-native-wasm-parity', caseId: c.id, passed: sky.maxSeparationArcsec <= .001, sky});
    } else comparisons.push({kind: 'truth-state-native-wasm-parity', caseId: c.id, passed: false, reason: 'Propagation execution failed.'});
  }
  for (const c of development) {
    const baselineNative = await fit(c, 'nativeBaseline', 'position', 100);
    const baselineWasm = await fit(c, 'wasmBaseline', 'position', 100);
    const experimentNative = await fit(c, 'nativeExperiment', 'position', 100);
    const experimentWasm = await fit(c, 'wasmExperiment', 'position', 100);
    for (const [kind, a, b, exact] of [
      ['native-default-instrumentation-parity', baselineNative, experimentNative, false],
      ['wasm-release-default-instrumentation-parity', baselineWasm, experimentWasm, true],
      ['baseline-native-wasm-parity', baselineNative, baselineWasm, false],
    ]) comparisons.push({kind, caseId: c.id, budget: 100, ...fitComparison(a, b, {requireExact: exact}),
      experimentalSingleBatch: experimentNative.summary?.search?.batches?.length === 1 && experimentNative.summary.search.attemptedTotal === 100});
    for (const budget of [100, 500]) for (const selection of ['position', 'phase6d', 'min-rms', 'predictive1d']) {
      const native = await fit(c, 'nativeExperiment', selection, budget);
      const wasm = await fit(c, 'wasmExperiment', selection, budget);
      comparisons.push({kind: 'experimental-native-wasm-parity', caseId: c.id, budget, selection,
        ...fitComparison(native, wasm, {instrumented: true})});
      await summarize();
    }
  }
  const summary = await summarize();
  manifest.completedAt = new Date().toISOString(); manifest.executedRecords = records.length;
  manifest.summarySHA256 = sha(await readFile(join(directory, 'summary.json')));
  await writeFile(manifestPath, JSON.stringify(manifest, null, 2) + '\n');
  return summary;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const options = {};
  for (let i = 2; i < process.argv.length; i += 2) {
    const key = process.argv[i]?.slice(2);
    if (!['output', 'corpus'].includes(key) || !process.argv[i + 1]) throw new Error('Usage: node experiments/short-arcs/controls.mjs [--output DIRECTORY] [--corpus FILE]');
    options[key] = process.argv[i + 1];
  }
  const summary = await runControls(options);
  console.log(JSON.stringify({executedRecords: summary.executedRecords, executionFailures: summary.executionFailures,
    comparisonsPassed: summary.comparisonsPassed, comparisonsFailed: summary.comparisonsFailed}));
}
