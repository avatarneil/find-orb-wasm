// SPDX-License-Identifier: GPL-2.0-or-later
// Exploratory fixed-schedule observational intervention; no solver outputs read.
// Run: node experiments/short-arcs/fetch-followup.mjs [--offline] [--out DIR]
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdir, readFile, writeFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {setTimeout as delay} from 'node:timers/promises';

const API = 'https://ssd.jpl.nasa.gov/api/horizons.api';
const fixtureRoot = fileURLToPath(new URL('./fixtures/', import.meta.url));
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const json = value => JSON.stringify(value, null, 2) + '\n';
const quote = value => `'${value}'`;

async function existing(path) {
  try { return await readFile(path, 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return null; throw error; }
}

function checkedResponse(responseText) {
  const data = JSON.parse(responseText);
  assert(!data.error, `Horizons: ${data.error}`);
  assert.equal(data.signature?.source, 'NASA/JPL Horizons API');
  assert(['1.2', '1.3'].includes(data.signature.version), 'Review unexpected API version');
  assert.equal(typeof data.result, 'string');
  assert.equal(data.result.split('$$SOE').length, 2, 'Missing or ambiguous table');
  assert.equal(data.result.split('$$EOE').length, 2, 'Missing or ambiguous end marker');
  return data;
}

async function queryResponse(out, item, times, offline) {
  const query = {format: 'json', COMMAND: item.object.number + ';', OBJ_DATA: 'YES', MAKE_EPHEM: 'YES',
    CENTER: item.observer, EPHEM_TYPE: 'OBSERVER', TIME_TYPE: 'UT', TLIST_TYPE: 'JD',
    TLIST: times.map(jd => quote(jd.toFixed(12))).join(' '), REF_SYSTEM: 'ICRF', CSV_FORMAT: 'YES',
    TIME_DIGITS: 'FRACSEC', QUANTITIES: '1,4', ANG_FORMAT: 'DEG', EXTRA_PREC: 'YES',
    CAL_FORMAT: 'JD', APPARENT: 'AIRLESS', ELEV_CUT: '-90', SKIP_DAYLT: 'NO', SOLAR_ELONG: '0,180'};
  const encoded = Object.fromEntries(Object.entries(query).map(([key, value]) =>
    [key, key === 'format' || key === 'TLIST' ? value : quote(value)]));
  const url = API + '?' + new URLSearchParams(encoded);
  const file = `raw/followup-${item.id}.json`;
  const path = resolve(out, file);
  let source = await existing(path);
  if (source === null) {
    assert(!offline, `Offline response missing: ${file}`);
    const response = await fetch(url, {signal: AbortSignal.timeout(45000)});
    assert(response.ok, `${file}: HTTP ${response.status}`);
    const responseText = await response.text();
    checkedResponse(responseText);
    source = json({schemaVersion: 1, query, url, retrievedAt: new Date().toISOString(),
      responseSha256: sha256(responseText), responseText});
    await writeFile(path, source, {flag: 'wx'});
    await delay(200);
  }
  const saved = JSON.parse(source);
  assert.equal(saved.schemaVersion, 1);
  assert.deepEqual(saved.query, query, 'Cached query differs; use a new output directory');
  assert.equal(saved.url, url, 'URL does not match query');
  assert.equal(sha256(saved.responseText), saved.responseSha256, 'Corrupt cached response');
  return {data: checkedResponse(saved.responseText), record: {file, sha256: sha256(source),
    responseSha256: saved.responseSha256, retrievedAt: saved.retrievedAt}};
}

function numeric(value) {
  assert(value !== '' && value !== 'n.a.' && Number.isFinite(Number(value)), `Invalid value: ${value}`);
  return Number(value);
}

function positions(data, item, times) {
  const text = data.result;
  assert.match(text, new RegExp(`Target body name: ${item.object.number} ${item.object.name} `));
  assert.match(text, /Center body name: Earth \(399\)/);
  assert.match(text, /Center-site name: Pan-STARRS 2, Haleakala/);
  const [before, after] = text.split('$$SOE');
  const header = before.split('\n').filter(line => line.includes(',')).at(-1);
  assert.deepEqual(header.split(',').map(value => value.trim()).filter(Boolean),
    ['Date_________JDUT', 'R.A.___(ICRF)', 'DEC____(ICRF)', 'Azimuth_(a-app)', 'Elevation_(a-app)']);
  const rows = after.split('$$EOE')[0].trim().split('\n').map(line => line.split(',').map(value => value.trim()));
  assert.equal(rows.length, times.length);
  return rows.map((row, index) => {
    assert.equal(row.length, 8);
    const point = {jdUtc: numeric(row[0]), RA: numeric(row[3]), Dec: numeric(row[4]),
      altitudeDeg: numeric(row[6]), solarPresence: row[1], lunarPresence: row[2]};
    assert(Math.abs(point.jdUtc - times[index]) < 2e-9, 'Unexpected UTC time');
    assert(point.RA >= 0 && point.RA < 360 && Math.abs(point.Dec) <= 90 && Math.abs(point.altitudeDeg) <= 90);
    return point;
  });
}

async function main() {
  let offline = false, out = fixtureRoot;
  const args = process.argv.slice(2);
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--offline') offline = true;
    else if (args[i] === '--out' && args[i + 1]) out = resolve(args[++i]);
    else throw new Error(`Unknown or incomplete argument: ${args[i]}`);
  }
  const corpusText = await readFile(resolve(fixtureRoot, 'observable-corpus.json'), 'utf8');
  const corpus = JSON.parse(corpusText);
  assert.equal(corpus.schemaVersion, 1);
  assert.equal(corpus.cases.length, 7, 'Review protocol when observable corpus changes');
  const protocol = {schemaVersion: 1, name: 'Exploratory second- and third-night tracklet intervention, version 1',
    status: 'Declared after initial short-arc and single-follow-up experiments; this is an exploratory observational intervention, not a prospectively held-out method-selection result.',
    inputCorpus: 'observable-corpus.json', inputCorpusSha256: sha256(corpusText),
    caseIds: corpus.cases.map(item => item.id),
    splitPolicy: corpus.splitPolicy,
    scheduleReference: 'Original LAST observation epochJdUtc, in UTC',
    night2MinutesAfterLastObservation: [1440, 1460, 1480, 1500],
    night3MinutesAfterLastObservation: [2880, 2900, 2920, 2940],
    selectionPolicy: 'Fetch every fixed scheduled position. Mark each complete tracklet available only if all four exposures have apparent altitude >=20 degrees and empty solarPresence (astronomical night). Retain unavailable rows and reasons. No rescheduling and no selection by solver outputs.',
    firstNightPolicy: 'Keep original four first-night observations, noise realization, weighting and identifiers unchanged in paired experiments.',
    heldoutPolicy: 'The original +3 day and +7 day positions remain unmodified prediction targets and must not enter a fit. The +1 day target now becomes input and cannot be scored as a held-out prediction.',
  };
  await mkdir(resolve(out, 'raw'), {recursive: true});
  const protocolText = json(protocol);
  const protocolPath = resolve(out, 'followup-protocol.json');
  const previous = await existing(protocolPath);
  if (previous === null) await writeFile(protocolPath, protocolText, {flag: 'wx'});
  else assert.equal(previous, protocolText, 'Protocol changed; use a new output directory');
  const cases = [];
  for (const item of corpus.cases) {
    assert.equal(item.observer, 'F52');
    const offsets = [...protocol.night2MinutesAfterLastObservation, ...protocol.night3MinutesAfterLastObservation];
    const times = offsets.map(minutes => item.epochJdUtc + minutes / 1440);
    const {data, record} = await queryResponse(out, item, times, offline);
    const rows = positions(data, item, times);
    const night2 = rows.slice(0, 4), night3 = rows.slice(4);
    const failures = tracklet => tracklet.flatMap((point, index) => [
      ...(point.altitudeDeg < 20 ? [`Exposure ${index + 1}: altitude ${point.altitudeDeg} <20 degrees`] : []),
      ...(point.solarPresence !== '' ? [`Exposure ${index + 1}: solar-presence flag '${point.solarPresence}' is not astronomical night`] : []),
    ]);
    const night2Failures = failures(night2), night3Failures = failures(night3);
    // The overlapping +24 h position is an independent consistency check against
    // the pinned original reference; it is not a solver-dependent selection.
    const original = item.holdout.find(point => Math.abs(point.jdUtc - times[0]) < 2e-9);
    assert(original, 'Missing original +24 h target');
    const raDifference = Math.abs(((rows[0].RA - original.RA + 540) % 360) - 180);
    assert(raDifference < 1e-7 && Math.abs(rows[0].Dec - original.Dec) < 1e-7,
      'Horizons reference changed at overlapping epoch; review consistency before use');
    cases.push({id: item.id, object: item.object, split: item.split, observer: item.observer,
      epochJdUtc: item.epochJdUtc, night2, night3,
      night2Available: night2Failures.length === 0, night3Available: night3Failures.length === 0,
      unavailableReasons: {night2: night2Failures, night3: night3Failures}, rawFiles: [record]});
    process.stdout.write(`${item.id}: night 2 ${night2Failures.length ? 'unavailable' : 'available'}, night 3 ${night3Failures.length ? 'unavailable' : 'available'}\n`);
  }
  const output = {schemaVersion: 1, provenance: {
    provider: 'NASA/JPL Horizons', api: API,
    documentation: ['https://ssd-api.jpl.nasa.gov/doc/horizons.html', 'https://ssd.jpl.nasa.gov/horizons/manual.html'],
    generator: 'experiments/short-arcs/fetch-followup.mjs', generatorSha256: sha256(await readFile(fileURLToPath(import.meta.url))),
    protocolFile: 'followup-protocol.json', protocolSha256: sha256(protocolText),
    inputCorpus: protocol.inputCorpus, inputCorpusSha256: protocol.inputCorpusSha256,
    coordinates: 'Horizons quantity 1: ICRF astrometric right ascension/declination in decimal degrees with down-leg light-time only. Reception epochs are UTC (TIME_TYPE=UT in 2026), observer F52. Quantity 4 apparent altitude is used only for visibility selection.',
    noise: 'No random measurement noise; runners must record the injected noise law and seed. The original first-night realization must remain paired.',
    limitations: 'Independent numerical ephemerides are not actual observations or exact physical truth. Availability models only altitude and astronomical night, not weather, limiting magnitude, lunar background or observing resources. This exploratory arm follows earlier results; retain original object splits and describe the timing of this intervention honestly.',
    rawResponseCount: cases.length,
  }, protocol, cases};
  await writeFile(resolve(out, 'followup-tracklets.json'), json(output));
  process.stdout.write(`Wrote ${cases.length} cases to ${resolve(out, 'followup-tracklets.json')}\n`);
}

main().catch(error => { process.stderr.write(error.stack + '\n'); process.exitCode = 1; });
