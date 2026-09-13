#!/usr/bin/env node
// GPL-2.0-or-later. Lossless DE440 time-window extraction.
// Record selection follows Bill Gray's jpl_eph/sub_eph.cpp; no coefficients
// or physical constants are recomputed, quantized, or removed.
import {createHash} from 'node:crypto';
import {readFile, writeFile, mkdir, cp, rename, rm} from 'node:fs/promises';
import {resolve, join, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {gzipSync, brotliCompressSync, constants} from 'node:zlib';
import {EPHEMERIS} from '../build/pins.mjs';
const here = dirname(fileURLToPath(import.meta.url));
export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
// -o commands read upstream's 2000-01-01 dummy observation before replacing
// its epoch. Keep J2000 coverage so all supported command modes can initialize.
export const DEFAULT_WINDOW = Object.freeze({startJD: 2451544.5, endJD: 2466154.5, marginRecords: 1});

export function inspectEphemeris(bytes) {
  if (!Buffer.isBuffer(bytes) || bytes.length < 4096) throw new Error('Truncated DE440 file.');
  const startJD = bytes.readDoubleLE(2652), endJD = bytes.readDoubleLE(2660), stepDays = bytes.readDoubleLE(2668);
  const constantsCount = bytes.readUInt32LE(2676), version = bytes.readUInt32LE(2840);
  const records = (endJD - startJD) / stepDays;
  if (version !== 440 || stepDays !== 32 || constantsCount !== 645 || !Number.isSafeInteger(records) || records < 1)
    throw new Error('Only pinned little-endian DE440 layout is supported.');
  const recordBytes = bytes.length / (records + 2);
  if (!Number.isSafeInteger(recordBytes) || recordBytes !== 8144) throw new Error('DE440 record length mismatch.');
  for (let i = 0; i < records; i++) {
    const offset = (i + 2) * recordBytes;
    if (bytes.readDoubleLE(offset) !== startJD + i * stepDays || bytes.readDoubleLE(offset + 8) !== startJD + (i + 1) * stepDays)
      throw new Error('DE440 record dates are inconsistent.');
  }
  return {startJD, endJD, stepDays, constantsCount, version, records, recordBytes};
}

function replaceDate(header, offset, jd) {
  const date = new Date((jd - 2440587.5) * 86400000);
  const month = ['JAN','FEB','MAR','APR','MAY','JUN','JUL','AUG','SEP','OCT','NOV','DEC'][date.getUTCMonth()];
  const calendar = `${date.getUTCFullYear()}-${month}-${String(date.getUTCDate()).padStart(2, '0')} 00:00:00`;
  header.write(jd.toFixed(1).padStart(11) + '  ' + calendar, offset, 'ascii');
}

export function subsetEphemeris(full, options = {}) {
  if (sha256(full) !== EPHEMERIS.sha256) throw new Error('Full DE440 source checksum does not match the pinned JPL file.');
  const source = inspectEphemeris(full);
  const {startJD, endJD, marginRecords} = {...DEFAULT_WINDOW, ...options};
  if (!Number.isFinite(startJD) || !Number.isFinite(endJD) || startJD >= endJD || startJD <= source.startJD || endJD > source.endJD ||
      !Number.isSafeInteger(marginRecords) || marginRecords < 1 || marginRecords > 100)
    throw new Error('Specify an increasing in-range JD window and 1–100 margin records.');
  const firstRecord = Math.max(0, Math.floor((startJD - source.startJD) / source.stepDays) - marginRecords);
  const afterLastRecord = Math.min(source.records, Math.ceil((endJD - source.startJD) / source.stepDays) + marginRecords);
  const actualStart = source.startJD + firstRecord * source.stepDays;
  const actualEnd = source.startJD + afterLastRecord * source.stepDays;
  const header = Buffer.from(full.subarray(0, 2 * source.recordBytes));
  header.writeDoubleLE(actualStart, 2652); header.writeDoubleLE(actualEnd, 2660);
  replaceDate(header, 101, actualStart); replaceDate(header, 185, actualEnd);
  const coefficients = full.subarray((firstRecord + 2) * source.recordBytes, (afterLastRecord + 2) * source.recordBytes);
  const bytes = Buffer.concat([header, coefficients]);
  inspectEphemeris(bytes);
  return {bytes, metadata: {
    method: 'Verbatim complete DE440 coefficient records; original constants; date headers updated',
    sourceSHA256: EPHEMERIS.sha256, sourceURL: EPHEMERIS.url,
    requestedStartJD: startJD, requestedEndJD: endJD, marginRecords,
    supportedStartExclusiveJD: actualStart, supportedEndInclusiveJD: actualEnd,
    lowerEndpointReason: 'The full reader chooses the preceding record at boundaries; that record is absent at the cropped file start.',
    stepDays: source.stepDays, recordBytes: source.recordBytes, firstRecord,
    records: afterLastRecord - firstRecord,
    coefficientSHA256: sha256(coefficients), constantsSHA256: sha256(header.subarray(source.recordBytes)),
  }};
}

export function compressSizes(bytes) {
  const gzip = gzipSync(bytes, {level: 9});
  const brotli = brotliCompressSync(bytes, {params: {[constants.BROTLI_PARAM_QUALITY]: 5}});
  return {gzip, brotli, sizes: {raw: bytes.length, gzip9: gzip.length, brotli5: brotli.length}};
}

export async function compactDistribution({dist = resolve('dist'), out = resolve('dist-compact'), ...window} = {}) {
  dist = resolve(dist); out = resolve(out);
  if (dist === out || out.startsWith(dist + '/') || dist.startsWith(out + '/')) throw new Error('Input and output distributions must be separate sibling directories.');
  const manifest = JSON.parse(await readFile(join(dist, 'manifest.json'), 'utf8'));
  if (manifest.ephemerisPolicy !== 'required; actual JPL queries fail closed outside (start, end] or on evaluation error')
    throw new Error('Compact packs require an engine built with the strict JPL query guard. Rebuild the candidate first.');
  const pack = await readFile(join(dist, manifest.pack.filename));
  if (sha256(pack) !== manifest.pack.sha256 || pack.length !== manifest.pack.size) throw new Error('Input pack integrity check failed.');
  let end = 0;
  for (const [name, entry] of Object.entries(manifest.entries)) {
    if (!/^(data\/)?[A-Za-z0-9_.-]+$/.test(name) || name.includes('..') || !Number.isSafeInteger(entry.offset) || !Number.isSafeInteger(entry.size) ||
        entry.offset !== end || entry.size < 1 || entry.offset + entry.size > pack.length ||
        sha256(pack.subarray(entry.offset, entry.offset + entry.size)) !== entry.sha256) throw new Error('Invalid input pack entry.');
    end += entry.size;
  }
  if (end !== pack.length) throw new Error('Input pack has unaccounted bytes.');
  const entry = manifest.entries[EPHEMERIS.filename];
  if (!entry) throw new Error('Pinned DE440 entry is absent.');
  const subset = subsetEphemeris(pack.subarray(entry.offset, entry.offset + entry.size), window);
  if (!(subset.metadata.supportedStartExclusiveJD < 2451544.5 && subset.metadata.supportedEndInclusiveJD >= 2451545))
    throw new Error('Distribution must include J2000: upstream -o commands load a 2000-01-01 dummy observation before the requested epoch.');
  const chunks = [], entries = {}; let offset = 0;
  for (const [name, item] of Object.entries(manifest.entries)) {
    const bytes = name === EPHEMERIS.filename ? subset.bytes : pack.subarray(item.offset, item.offset + item.size);
    entries[name] = {offset, size: bytes.length, sha256: sha256(bytes)};
    offset += bytes.length; chunks.push(bytes);
  }
  const compactPack = Buffer.concat(chunks);
  const compressedFull = compressSizes(pack), compressed = compressSizes(compactPack);
  manifest.entries = entries;
  manifest.ephemeris = {...manifest.ephemeris, sha256: sha256(subset.bytes), subset: subset.metadata};
  manifest.pack = {filename: 'find-orb.data', size: compactPack.length, sha256: sha256(compactPack),
    encodings: {gzip: {filename: 'find-orb.data.gz', size: compressed.gzip.length, sha256: sha256(compressed.gzip)},
      brotli: {filename: 'find-orb.data.br', size: compressed.brotli.length, sha256: sha256(compressed.brotli)}}};
  delete manifest.workerSHA256;
  const originalWorker = await readFile(join(dist, 'find-orb-worker.js'), 'utf8');
  const sourceManifest = JSON.parse(await readFile(join(dist, 'manifest.json'), 'utf8'));
  if (sha256(originalWorker) !== sourceManifest.workerSHA256) throw new Error('Input worker integrity check failed.');
  const firstNewline = originalWorker.indexOf('\n');
  if (!originalWorker.startsWith('const FIND_ORB_MANIFEST=') || firstNewline < 0) throw new Error('Unrecognized trusted worker format.');
  const worker = 'const FIND_ORB_MANIFEST=' + JSON.stringify(manifest) + ';\n' + originalWorker.slice(firstNewline + 1);
  manifest.workerSHA256 = sha256(worker);
  const report = {schema: 1, ...subset.metadata, fullPack: compressedFull.sizes, compactPack: compressed.sizes,
    reductionPercent: 100 * (1 - compactPack.length / pack.length), unchangedEngineSHA256: manifest.binarySHA256,
    auxiliaryFiles: Object.entries(entries).filter(([name]) => name !== EPHEMERIS.filename).map(([name, item]) => ({name, bytes: item.size})).sort((a,b) => b.bytes-a.bytes),
    scope: 'All auxiliary files retained. No coefficient truncation, quantization, body removal, or analytic fallback.'};
  const stage = out + '.tmp-' + process.pid;
  await mkdir(dirname(out), {recursive: true});
  try {
    await cp(dist, stage, {recursive: true, filter: path => !['find-orb.data','find-orb.data.gz','find-orb.data.br','manifest.json','find-orb-worker.js'].includes(path.slice(dist.length + 1))});
    await writeFile(join(stage, 'find-orb.data'), compactPack);
    await writeFile(join(stage, 'find-orb.data.gz'), compressed.gzip);
    await writeFile(join(stage, 'find-orb.data.br'), compressed.brotli);
    await writeFile(join(stage, 'find-orb-worker.js'), worker);
    await writeFile(join(stage, 'manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
    await writeFile(join(stage, 'dataset-report.json'), JSON.stringify(report, null, 2) + '\n');
    // Never replace an existing distribution implicitly.
    await rename(stage, out);
  } catch (error) {await rm(stage, {recursive: true, force: true}); throw error;}
  // Explicit transport assets for applications hosting the full historical data.
  await writeFile(join(dist, 'find-orb.data.gz'), compressedFull.gzip);
  await writeFile(join(dist, 'find-orb.data.br'), compressedFull.brotli);
  return report;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const options = {};
  const names = {'--dist': 'dist', '--out': 'out', '--start-jd': 'startJD', '--end-jd': 'endJD', '--margin-records': 'marginRecords'};
  for (let i = 2; i < process.argv.length; i += 2) {
    const name = names[process.argv[i]], value = process.argv[i + 1];
    if (!name || !value) throw new Error('Options: --dist PATH --out PATH --start-jd JD --end-jd JD --margin-records N');
    options[name] = ['dist', 'out'].includes(name) ? resolve(value) : Number(value);
  }
  console.log(JSON.stringify(await compactDistribution(options), null, 2));
}
