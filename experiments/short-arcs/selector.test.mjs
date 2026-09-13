// SPDX-License-Identifier: GPL-2.0-or-later
// node --test experiments/short-arcs/selector.test.mjs
import {test, after} from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {mkdtemp, readFile, writeFile, rm} from 'node:fs/promises';
import {join, resolve} from 'node:path';
import {tmpdir} from 'node:os';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {SOURCE_PINS} from '../../build/pins.mjs';
import {patches as releasePatches} from '../../build/patches.mjs';
import {applyShortArcPatches} from './patches.mjs';

const root = fileURLToPath(new URL('../../', import.meta.url));
const sourceRoots = process.env.FIND_ORB_SELECTOR_SOURCE
  ? [resolve(process.env.FIND_ORB_SELECTOR_SOURCE)]
  : ['.native-engine/sources/find_orb', '.wasm-engine/sources/find_orb'].map(path => join(root, path));
const compiler = process.env.CXX || 'c++';
const command = (program, args) => spawnSync(program, args, {
  encoding: 'utf8', timeout: 30000, maxBuffer: 8 * 1024 * 1024,
});
const sha256 = text => createHash('sha256').update(text).digest('hex');
let skipReason, source, sortingSource, selectedRoot, directory, binary;

const compilerVersion = command(compiler, ['--version']);
if (compilerVersion.error?.code === 'ENOENT') {
  skipReason = `C++ compiler unavailable: ${compiler}; these native selector checks require ASan and UBSan.`;
} else {
  assert.equal(compilerVersion.status, 0, compilerVersion.error?.message || compilerVersion.stderr);
  for (const path of sourceRoots) {
    const result = command('git', ['-C', path, 'show', `${SOURCE_PINS.find_orb}:orb_func.cpp`]);
    if (result.status !== 0) continue;
    const sorting = command('git', ['-C', path, 'show', `${SOURCE_PINS.find_orb}:shellsor.cpp`]);
    assert.equal(sorting.status, 0, sorting.stderr);
    source = result.stdout;
    sortingSource = sorting.stdout;
    selectedRoot = path;
    break;
  }
  if (!source) skipReason = `Pinned Find_Orb source ${SOURCE_PINS.find_orb} unavailable; build the native/WASM engine or set FIND_ORB_SELECTOR_SOURCE to its Git checkout.`;
}

function section(text, begin, end, from = 0) {
  const start = text.indexOf(begin, from);
  const finish = text.indexOf(end, start + begin.length);
  assert.ok(start >= 0 && finish > start, `Source extraction context changed: ${begin}`);
  return text.slice(start, finish);
}

function definition(text, signature) {
  const start = text.lastIndexOf(signature);
  assert.ok(start >= 0, `Missing source function: ${signature}`);
  const opening = text.indexOf('\n{', start);
  assert.ok(opening >= 0, `Missing function body: ${signature}`);
  // These explicitly named kernels contain no braces in comments or literals.
  // Checked extraction delimiters below independently bound larger sections.
  let depth = 0;
  for (let i = opening + 1; i < text.length; i++) {
    if (text[i] === '{') depth++;
    if (text[i] === '}' && --depth === 0) return text.slice(start, i + 1);
  }
  throw new Error(`Unclosed source function: ${signature}`);
}

if (!skipReason) {
  // Use the actual release transformation for the fixed-count SR branch,
  // then compile that branch natively by defining __EMSCRIPTEN__. This checks
  // loop control and export accounting; whole-WASM execution is tested by the
  // parent benchmark separately.
  let portable = source;
  for (const patch of releasePatches.filter(patch => patch.file === 'orb_func.cpp')) {
    assert.equal(portable.split(patch.from).length, 2);
    portable = portable.replace(patch.from, patch.to);
  }
  const patched = applyShortArcPatches(portable);
  const acceptanceExport = 'research_sr_select_orbit( sr_orbits, n_sr_orbits, obs, n_obs);\n         research_sr_write_family( sr_orbits, n_sr_orbits, orbit_epoch);\n         memcpy( orbit, sr_orbits, 6 * sizeof( double));';
  assert.ok(patched.includes(acceptanceExport), 'Family export must follow the accepted-family nominal swap and precede the nominal copy.');
  const functions = [
    definition(sortingSource, 'void shellsort_r( void *base, const size_t n_elements'),
    definition(source, 'double vect_diff2( const double *a, const double *b)'),
    definition(source, 'static int compare_doubles( const void *aptr, const void *bptr, void *unused_context)'),
    section(patched, 'static void research_sr_failure(', 'int get_sr_orbits('),
    definition(patched, 'static int sr_orbit_compare( const void *a, const void *b)'),
    section(patched, 'int get_sr_orbits(', 'static bool is_valid_sr_orbit('),
    section(patched, 'static void find_median_orbit(', '#define INITIAL_ORBIT_NOT_YET_FOUND'),
  ].join('\n\n');
  const scaffold = await readFile(new URL('./selector-test.cpp', import.meta.url), 'utf8');
  assert.equal(scaffold.split('// @SOURCE_FUNCTIONS@').length, 2);
  directory = await mkdtemp(join(tmpdir(), 'find-orb-selector-tests-'));
  binary = join(directory, 'selector-tests');
  const path = join(directory, 'selector-tests.cpp');
  await writeFile(path, scaffold.replace('// @SOURCE_FUNCTIONS@', functions));
  const compiled = command(compiler, [
    '-std=c++11', '-O1', '-g', '-UNDEBUG', '-D__EMSCRIPTEN__', '-fsanitize=address,undefined',
    '-fno-omit-frame-pointer', path, '-o', binary,
  ]);
  assert.equal(compiled.status, 0,
    `Selector sanitizer compilation failed (not skipped): ${compiled.error?.message || compiled.stderr}`);
  after(async () => { await rm(directory, {recursive: true, force: true}); });
}

for (const name of ['default', 'phase6d', 'degenerate', 'min-rms', 'csv-unset']) {
  test(`source-extracted selector: ${name}`, {skip: skipReason}, t => {
    if (name === 'default') t.diagnostic(JSON.stringify({
      sourceRevision: SOURCE_PINS.find_orb, sourceRoot: selectedRoot,
      sourceSHA256: sha256(source), compiler: compilerVersion.stdout.split('\n')[0],
      sanitizers: ['address', 'undefined'],
      scope: 'Actual selector/sorting/export kernels; observation evaluator stubbed.',
    }));
    const result = command(binary, [name]);
    assert.equal(result.status, 0, result.error?.message || result.stderr);
    assert.equal(result.stderr, '');
    assert.match(result.stdout, new RegExp(`PASS ${name}`));
  });
}

for (const [name, message] of [
  ['invalid', 'SR_SELECTION must be position, phase6d, or min-rms'],
  ['nonfinite', 'Nonfinite phase6d candidate state'],
  ['empty', 'Cannot select an empty candidate family'],
]) {
  test(`selector rejects ${name}`, {skip: skipReason}, () => {
    const result = command(binary, [name]);
    assert.equal(result.signal, 'SIGABRT', result.error?.message || result.stderr);
    assert.ok(result.stderr.includes(`Short-arc research error: ${message}`));
    assert.doesNotMatch(result.stderr, /runtime error:|ERROR: AddressSanitizer/);
  });
}

test('candidate CSV records states and appends batches without observation mutations', {skip: skipReason}, async () => {
  const path = join(directory, 'candidates.csv');
  const result = command(binary, ['csv', path]);
  assert.equal(result.status, 0, result.error?.message || result.stderr);
  assert.equal(result.stderr, '');
  const [header, ...rows] = (await readFile(path, 'utf8')).trim().split('\n');
  assert.deepEqual(header.split(','), [
    'source_index', 'epoch_tt_jd', 'x_au', 'y_au', 'z_au', 'vx_au_day', 'vy_au_day', 'vz_au_day',
    'heuristic_score', 'weighted_rms', 'n_residuals', 'rparam', 'vparam',
  ]);
  assert.deepEqual(rows.map(row => row.split(',').map(Number)), [7, 48].map(index =>
    [index, 2461150.5, 1, 2, 3, .004, .005, .006, .625, .125, 8, .2, -.4]));
});

test('requested candidate-output failure is explicit', {skip: skipReason}, () => {
  const result = command(binary, ['csv', join(directory, 'missing-directory', 'candidates.csv')]);
  assert.equal(result.signal, 'SIGABRT', result.error?.message || result.stderr);
  assert.match(result.stderr, /Short-arc research error: Cannot open SR_CANDIDATES_FILE/);
});

test('family CSV preserves exact order after the nominal swap without mutations', {skip: skipReason}, async () => {
  const path = join(directory, 'family.csv');
  await writeFile(path, ''); // Supported placeholder if the solver never accepts SR.
  const result = command(binary, ['family', path]);
  assert.equal(result.status, 0, result.error?.message || result.stderr);
  assert.equal(result.stderr, '');
  const selected = Number(/nominal_source_index=(\d+)/.exec(result.stdout)?.[1]);
  assert.ok(Number.isInteger(selected) && selected >= 0 && selected < 5);
  const expected = [
    [1, 4, -3, .003, -.002, .001],
    [1.1, 3.8, -2.9, .004, -.0021, .0015],
    [.9, 4.2, -3.1, .002, -.0019, .0005],
    [1.02, 3.95, -3.03, .0025, -.00205, .0009],
    [9, -7, 6, .2, .4, -.5],
  ];
  [expected[0], expected[selected]] = [expected[selected], expected[0]];
  const [header, ...rows] = (await readFile(path, 'utf8')).trim().split('\n');
  assert.equal(header, 'family_index,epoch_tt_jd,x_au,y_au,z_au,vx_au_day,vy_au_day,vz_au_day');
  assert.deepEqual(rows.map(row => row.split(',').map(Number)), expected.map((state, i) => [i, 2461150.5, ...state]));
});

test('actual fixed-count SR loop audits attempts, failures, and candidate-truncating retries', {skip: skipReason}, async () => {
  const batches = join(directory, 'batches.csv'), candidates = join(directory, 'batch-candidates.csv');
  await writeFile(batches, '');
  await writeFile(candidates, '');
  const result = command(binary, ['batches', batches, candidates]);
  assert.equal(result.status, 0, result.error?.message || result.stderr);
  assert.equal(result.stderr, '');
  const [header, ...rows] = (await readFile(batches, 'utf8')).trim().split('\n');
  assert.equal(header, 'starting_orbit,n_observations,max_orbits,attempted,successful,epoch_tt_jd');
  assert.deepEqual(rows.map(row => row.split(',').map(Number)), [
    [0, 4, 8, 8, 4, 2461150.5],
    [20, 4, 4, 4, 2, 2461150.5],
    [0, 4, 10, 10, 5, 2461150.5],
  ]);
  const candidateRows = (await readFile(candidates, 'utf8')).trim().split('\n').slice(1);
  assert.deepEqual(candidateRows.map(row => Number(row.split(',')[0])), [1, 2, 4, 7, 8]);
});

for (const [name, message] of [
  ['family-nonfinite', 'Nonfinite family state'],
  ['invalid-batch', 'Invalid SR batch diagnostics'],
]) {
  test(`new telemetry rejects ${name}`, {skip: skipReason}, () => {
    const result = command(binary, [name, join(directory, `${name}.csv`)]);
    assert.equal(result.signal, 'SIGABRT', result.error?.message || result.stderr);
    assert.ok(result.stderr.includes(`Short-arc research error: ${message}`));
  });
}

for (const [name, variable] of [['family', 'SR_FAMILY_FILE'], ['batches', 'SR_BATCHES_FILE']]) {
  test(`requested ${variable} failure is explicit`, {skip: skipReason}, () => {
    const args = [name, join(directory, 'missing-directory', `${name}.csv`)];
    if (name === 'batches') args.push(join(directory, 'error-candidates.csv'));
    const result = command(binary, args);
    assert.equal(result.signal, 'SIGABRT', result.error?.message || result.stderr);
    assert.ok(result.stderr.includes(`Short-arc research error: Cannot open ${variable}`));
  });
}
