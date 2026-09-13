#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import {readFile, writeFile, mkdir} from 'node:fs/promises';
const parse = async path => JSON.parse(await readFile(path, 'utf8'));
const sizes = await parse('dist-compact/dataset-report.json');
const native = await parse('results/local/dataset-native.json');
const wasm = await parse('results/local/dataset-wasm.json');
const report = {schema: 1, measuredOn: '2026-09-13', sizes,
  native: {...native, flags: native.flags.map(flag => flag.replace(process.cwd(), '$REPO'))}, wasm,
  transportReductionPercent: 100 * (1 - sizes.compactPack.gzip9 / sizes.fullPack.gzip9),
  commands: ['node data/compact.mjs', 'node data/verify-native.mjs', 'node data/verify-wasm.mjs', 'node --test tests/data/*.test.mjs', 'node data/report.mjs'],
  limitations: [
    'The supported interval applies to every actual JPL query, including intermediate integration and light-time epochs. Requested dates alone do not guarantee acceptance.',
    'The lower endpoint is excluded to preserve the full reader\'s record-boundary convention.',
    'Upstream state-vector commands create a 2000-01-01 dummy observation. The distribution generator requires J2000 coverage.',
    'All auxiliary files are retained, including the 6.48 MB full-resolution sky brightness map.',
    'Exact coefficient preservation and the finite native/WASM regression suite are not a formal proof of the complete orbit solver.',
    'Compressed size reduces download and initialization costs; it does not accelerate orbital integration arithmetic.',
  ],
  primarySources: {
    originalFindOrb: 'https://github.com/Bill-Gray/find_orb',
    upstreamSubset: 'https://github.com/Bill-Gray/jpl_eph/blob/a73f25e54d02b99b1c0d9a9d6c61acfbb2fa3a26/sub_eph.cpp',
    jplData: 'https://ssd.jpl.nasa.gov/planets/eph_export.html',
    jplAttribution: 'https://ssd.jpl.nasa.gov/about/',
  },
};
await mkdir('results', {recursive: true});
await writeFile('results/dataset.json', JSON.stringify(report, null, 2) + '\n');
console.log('Wrote results/dataset.json');
