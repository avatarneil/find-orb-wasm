#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {mkdir, readFile, writeFile} from 'node:fs/promises';
import {resolve, join, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {SOURCE_PINS, EPHEMERIS} from '../build/pins.mjs';
import {subsetEphemeris, sha256} from './compact.mjs';
const exec = promisify(execFile);
const here = dirname(fileURLToPath(import.meta.url));
const options = {source: resolve('.wasm-engine/sources/jpl_eph'), full: resolve('.cache', EPHEMERIS.filename), out: resolve('results/local/dataset-native.json')};
for (let i = 2; i < process.argv.length; i += 2) {
  const key = process.argv[i].slice(2);
  if (!['source','full','out'].includes(key) || !process.argv[i + 1]) throw new Error('Options: --source JPL_SOURCE --full DE440 --out REPORT_JSON');
  options[key] = resolve(process.argv[i + 1]);
}
const revision = (await exec('git', ['rev-parse', 'HEAD'], {cwd: options.source})).stdout.trim();
if (revision !== SOURCE_PINS.jpl_eph) throw new Error('Unpinned JPL reader source.');
const lunar = join(dirname(options.source), 'lunar');
if ((await exec('git', ['rev-parse', 'HEAD'], {cwd: lunar})).stdout.trim() !== SOURCE_PINS.lunar ||
    (await exec('git', ['show', 'HEAD:get_bin.h'], {cwd: lunar})).stdout !== await readFile(join(lunar, 'get_bin.h'), 'utf8'))
  throw new Error('Unpinned or modified lunar binary reader header.');
for (const name of ['jpleph.cpp','jpleph.h','jpl_int.h']) {
  const original = (await exec('git', ['show', 'HEAD:' + name], {cwd: options.source})).stdout;
  if (original !== await readFile(join(options.source, name), 'utf8')) throw new Error('Modified JPL reader source: ' + name);
}
const work = resolve('.cache/dataset-verification'); await mkdir(work, {recursive: true});
const full = await readFile(options.full), subset = subsetEphemeris(full);
const compact = join(work, 'compact.440'); await writeFile(compact, subset.bytes);
const binary = join(work, 'verify-jpl');
const compiler = process.env.CXX || 'clang++';
const flags = ['-std=c++17', '-O2', '-ffp-contract=off', '-I', options.source, '-I', lunar, join(here, 'verify-jpl.cpp'), join(options.source, 'jpleph.cpp'), '-o', binary];
await exec(compiler, flags, {maxBuffer: 4000000});
const report = JSON.parse((await exec(binary, [options.full, compact], {maxBuffer: 4000000})).stdout);
const compilerVersion = (await exec(compiler, ['--version'])).stdout.trim();
Object.assign(report, {source: SOURCE_PINS.jpl_eph, fullSHA256: sha256(full), compactSHA256: sha256(subset.bytes), compiler: compilerVersion, flags, subset: subset.metadata});
await mkdir(dirname(options.out), {recursive: true});
await writeFile(options.out, JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report, null, 2));
