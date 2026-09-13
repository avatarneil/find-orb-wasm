// SPDX-License-Identifier: GPL-2.0-or-later
// Independent numerical-reference corpus; never reads Find_Orb outputs.
// Run: node experiments/short-arcs/fetch-horizons.mjs [--observable] [--offline] [--out DIR]
// Cached responses are immutable and verified. Use a new output directory to
// obtain a newer Horizons solution, and retain the previous corpus for replay.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdir, readFile, writeFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {setTimeout as delay} from 'node:timers/promises';

const API = 'https://ssd.jpl.nasa.gov/api/horizons.api';
const MANUAL = 'https://ssd.jpl.nasa.gov/horizons/manual.html';
const API_DOC = 'https://ssd-api.jpl.nasa.gov/doc/horizons.html';
const DAY_SECONDS = 86400;
const TT_MINUS_UTC_SECONDS_2026 = 69.184; // TAI−UTC = 37 s; TT−TAI = 32.184 s.
const protocol = {
  schemaVersion: 1,
  name: 'Unconditional short-arc geometry stress corpus, version 1',
  selectionPolicy: 'Objects, dates, arc length, sampling and split are fixed before solver evaluation. No visibility or solver-success selection.',
  splitPolicy: 'Split by object: both epochs of each object remain in the same split. Tune only on development objects; inspect held-out objects after methods are frozen. Achilles is a held-out class stress case.',
  observer: 'F52',
  datesUtc: ['2026-03-01T10:00:00.000Z', '2026-09-01T10:00:00.000Z'],
  observationMinutesAfterStart: [0, 10, 20, 30, 40, 50, 60],
  fourObservationIndices: [0, 2, 4, 6],
  holdoutHoursAfterLastObservation: [6, 24, 72, 168],
  followupPolicy: 'The +6 h or +24 h holdout positions may be used as simulated follow-up input only in a separately labeled experiment; evaluate that experiment solely on subsequent unused epochs.',
  bodies: [
    {number: 1, name: 'Ceres', class: 'main-belt', split: 'development'},
    {number: 2, name: 'Pallas', class: 'main-belt', split: 'development'},
    {number: 3, name: 'Juno', class: 'main-belt', split: 'held-out'},
    {number: 4, name: 'Vesta', class: 'main-belt', split: 'held-out'},
    {number: 433, name: 'Eros', class: 'near-Earth (Amor)', split: 'development'},
    {number: 99942, name: 'Apophis', class: 'near-Earth (Aten)', split: 'development'},
    {number: 101955, name: 'Bennu', class: 'near-Earth (Apollo)', split: 'held-out'},
    {number: 588, name: 'Achilles', class: 'Jupiter Trojan', split: 'held-out'},
  ],
};
const observableProtocol = {
  ...protocol,
  name: 'Observable short-arc geometry corpus, version 1',
  selectionPolicy: 'For each predeclared body and UTC anchor, scan at 30-minute cadence for 30 days. Select the earliest three consecutive samples spanning one hour with apparent altitude at least 20 degrees and an empty Horizons solar-presence flag (astronomical night) at all three samples. If absent, scan the predetermined 90-day interval from the same anchor. Record unavailable when no qualifying hour exists. No Find_Orb output or fit quality enters selection.',
  visibility: {scanStepMinutes: 30, scanDurationsDays: [30, 90], minimumAltitudeDeg: 20,
    requiredSolarPresence: '', requiredContiguousSamples: 3,
    verification: 'After selecting a window, fetch at 10-minute cadence and require all seven observation positions to meet the same altitude/night thresholds; fail explicitly if that check disagrees with the coarse scan.'},
  followupPolicy: 'Future positions remain unfiltered numerical prediction targets. Use +6 h or +24 h as simulated follow-up input only if its own altitude/night metadata permits observation, and evaluate solely on subsequent unused epochs. No follow-up visibility enters the initial-window selection.',
};

const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const json = value => JSON.stringify(value, null, 2) + '\n';
const jdUtc = iso => Date.parse(iso) / 86400000 + 2440587.5;
const quote = value => `'${value}'`;
const tlist = times => times.map(jd => quote(jd.toFixed(12))).join(' ');

function options(argv) {
  const result = {offline: false, observable: false, out: fileURLToPath(new URL('./fixtures/', import.meta.url))};
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === '--offline') result.offline = true;
    else if (argv[i] === '--observable') result.observable = true;
    else if (argv[i] === '--out' && argv[i + 1]) result.out = resolve(argv[++i]);
    else throw new Error(`Unknown or incomplete argument: ${argv[i]}`);
  }
  return result;
}

async function existing(path) {
  try { return await readFile(path, 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return null; throw error; }
}

function checkedResponse(text, label) {
  const document = JSON.parse(text);
  assert(!document.error, `${label}: Horizons error: ${document.error}`);
  assert.equal(document.signature?.source, 'NASA/JPL Horizons API', `${label}: unexpected API source`);
  assert(['1.2', '1.3'].includes(document.signature.version), `${label}: review new API version ${document.signature.version}`);
  assert.equal(typeof document.result, 'string', `${label}: missing result`);
  assert.equal(document.result.split('$$SOE').length, 2, `${label}: missing or ambiguous ephemeris`);
  assert.equal(document.result.split('$$EOE').length, 2, `${label}: missing or ambiguous end marker`);
  return document;
}

async function response(out, id, kind, query, offline) {
  const file = `raw/${id}-${kind}.json`;
  const path = resolve(out, file);
  const encoded = Object.fromEntries(Object.entries(query).map(([key, value]) =>
    [key, key === 'format' || key === 'TLIST' ? value : quote(value)]));
  const url = API + '?' + new URLSearchParams(encoded);
  let source = await existing(path);
  if (source === null) {
    assert(!offline, `Offline response missing: ${path}`);
    let fetched;
    for (let attempt = 0; attempt < 3; attempt++) {
      fetched = await fetch(url, {signal: AbortSignal.timeout(45000)});
      if (fetched.ok || ![429, 500, 502, 503, 504].includes(fetched.status)) break;
      await fetched.arrayBuffer();
      await delay(1000 * (attempt + 1));
    }
    assert(fetched.ok, `${id}/${kind}: HTTP ${fetched.status}`);
    const responseText = await fetched.text();
    checkedResponse(responseText, `${id}/${kind}`); // Never cache a failed or ambiguous query.
    source = json({schemaVersion: 1, query, url, retrievedAt: new Date().toISOString(),
      responseSha256: hash(responseText), responseText});
    await writeFile(path, source, {flag: 'wx'});
    await delay(200); // Sequential API requests; no concurrent download fan-out.
  }
  const saved = JSON.parse(source);
  assert.equal(saved.schemaVersion, 1, `${file}: unknown raw schema`);
  assert.deepEqual(saved.query, query, `${file}: query changed; use a new output directory`);
  assert.equal(saved.url, url, `${file}: URL does not match query`);
  assert.equal(hash(saved.responseText), saved.responseSha256, `${file}: corrupt response`);
  const document = checkedResponse(saved.responseText, file);
  return {text: document.result, record: {file, sha256: hash(source), responseSha256: saved.responseSha256,
    retrievedAt: saved.retrievedAt, apiVersion: document.signature.version}};
}

function table(text, expectedHeader, expectedRows) {
  const [before, after] = text.split('$$SOE');
  const header = before.split('\n').map(line => line.trim()).filter(line => line.includes(',')).at(-1);
  assert(header, 'Missing CSV column header');
  assert.deepEqual(header.split(',').map(value => value.trim()).filter(Boolean), expectedHeader,
    'Horizons columns changed; review parser before accepting new data');
  const result = after.split('$$EOE')[0].trim().split('\n').map(line => line.split(',').map(value => value.trim()));
  assert.equal(result.length, expectedRows, 'Unexpected ephemeris row count');
  return result;
}

function number(value, label) {
  assert(value !== '' && value !== 'n.a.', `${label}: missing numeric value`);
  const parsed = Number(value);
  assert(Number.isFinite(parsed), `${label}: invalid number ${value}`);
  return parsed;
}

function close(actual, expected, tolerance, label) {
  assert(Math.abs(actual - expected) <= tolerance, `${label}: ${actual} differs from ${expected}`);
}

function observerRows(text, times) {
  assert.match(text, /Center-site name: Pan-STARRS 2, Haleakala/);
  assert.match(text, /Center body name: Earth \(399\)/);
  const parsed = table(text, ['Date_________JDUT', 'R.A.___(ICRF)', 'DEC____(ICRF)',
    'Azimuth_(a-app)', 'Elevation_(a-app)', 'APmag', 'S-brt', 'delta', 'deldot', 'S-O-T', '/r', 'TDB-UT'], times.length);
  return parsed.map((row, i) => {
    assert.equal(row.length, 15);
    const result = {jdUtc: number(row[0], 'JD UTC'), RA: number(row[3], 'RA'), Dec: number(row[4], 'Dec'),
      altitudeDeg: number(row[6], 'altitude'), apparentMagnitude: row[7] === 'n.a.' ? null : number(row[7], 'magnitude'),
      rangeAu: number(row[9], 'range'), rangeRateKmPerSecond: number(row[10], 'range rate'),
      elongationDeg: number(row[11], 'elongation'), tdbMinusUtcSeconds: number(row[13], 'TDB−UTC'),
      solarPresence: row[1], lunarPresence: row[2]};
    close(result.jdUtc, times[i], 2e-9, 'Observation time');
    assert(result.RA >= 0 && result.RA < 360 && Math.abs(result.Dec) <= 90);
    assert(result.rangeAu > 0 && Math.abs(result.altitudeDeg) <= 90);
    assert(result.elongationDeg >= 0 && result.elongationDeg <= 180);
    assert(Math.abs(result.tdbMinusUtcSeconds - TT_MINUS_UTC_SECONDS_2026) < 0.002,
      'Unexpected 2026 time conversion; review leap-second assumption');
    return result;
  });
}

async function observableWindow(out, id, body, anchor, offline, selectedProtocol) {
  const {visibility} = selectedProtocol;
  const scanFiles = [];
  for (const days of visibility.scanDurationsDays) {
    const scan = await response(out, id, `scan-${days}d`, {format: 'json', COMMAND: body.number + ';',
      OBJ_DATA: 'YES', MAKE_EPHEM: 'YES', CENTER: selectedProtocol.observer, EPHEM_TYPE: 'OBSERVER',
      TIME_TYPE: 'UT', START_TIME: 'JD' + anchor.toFixed(12), STOP_TIME: 'JD' + (anchor + days).toFixed(12),
      STEP_SIZE: visibility.scanStepMinutes + 'm', REF_SYSTEM: 'ICRF', CSV_FORMAT: 'YES', TIME_DIGITS: 'FRACSEC',
      QUANTITIES: '4', ANG_FORMAT: 'DEG', EXTRA_PREC: 'YES', CAL_FORMAT: 'JD', APPARENT: 'AIRLESS',
      ELEV_CUT: '-90', SKIP_DAYLT: 'NO', SOLAR_ELONG: '0,180'}, offline);
    scanFiles.push(scan.record);
    assert.match(scan.text, new RegExp(`Target body name: ${body.number} ${body.name} `), 'Wrong scan target');
    assert.match(scan.text, /Center-site name: Pan-STARRS 2, Haleakala/);
    const count = days * 1440 / visibility.scanStepMinutes + 1;
    const parsed = table(scan.text, ['Date_________JDUT', 'Azimuth_(a-app)', 'Elevation_(a-app)'], count);
    const rows = parsed.map((row, index) => {
      assert.equal(row.length, 6, 'Unexpected visibility scan columns');
      const jd = number(row[0], 'Scan JD UTC');
      close(jd, anchor + index * visibility.scanStepMinutes / 1440, 2e-9, 'Scan time');
      return {jdUtc: jd, solarPresence: row[1], altitudeDeg: number(row[4], 'Scan altitude')};
    });
    const eligible = row => row.altitudeDeg >= visibility.minimumAltitudeDeg && row.solarPresence === visibility.requiredSolarPresence;
    for (let index = 0; index <= rows.length - visibility.requiredContiguousSamples; index++) {
      const window = rows.slice(index, index + visibility.requiredContiguousSamples);
      if (window.every(eligible)) {
        // Use the exact declared cadence epoch, not the CSV's rounded Julian day.
        const startJdUtc = anchor + index * visibility.scanStepMinutes / 1440;
        return {startJdUtc, scanFiles, scanDurationDays: days, scanStartIndex: index,
          scanWindow: window, rule: selectedProtocol.selectionPolicy};
      }
    }
    process.stdout.write(`${id}: no qualifying one-hour window in ${days} days\n`);
  }
  return {startJdUtc: null, scanFiles, reason: 'No one-hour window satisfies the preregistered visibility rule within 90 days'};
}

function stateRows(text, epochs) {
  assert.match(text, /Center body name: Sun \(10\)/);
  assert.match(text, /Reference frame : Ecliptic of J2000\.0/);
  assert.match(text, /Output units\s+: AU-D/);
  assert.match(text, /Output type\s+: GEOMETRIC cartesian states/);
  const rows = table(text, ['JDTDB', 'Calendar Date (TDB)', 'X', 'Y', 'Z', 'VX', 'VY', 'VZ'], epochs.length);
  return rows.map((row, index) => {
    close(number(row[0], 'State JD TDB'), epochs[index], 2e-9, 'State epoch');
    return {positionAu: row.slice(2, 5).map(value => number(value, 'position')),
      velocityAuPerDay: row.slice(5, 8).map(value => number(value, 'velocity'))};
  });
}

function elementsRows(text, epochs) {
  assert.match(text, /Center body name: Sun \(10\)/);
  assert.match(text, /Reference frame : Ecliptic of J2000\.0/);
  assert.match(text, /Output units\s+: AU-D/);
  assert.match(text, /Output type\s+: GEOMETRIC osculating elements/);
  const rows = table(text, ['JDTDB', 'Calendar Date (TDB)', 'EC', 'QR', 'IN', 'OM', 'W', 'Tp', 'N', 'MA', 'TA', 'A', 'AD', 'PR'], epochs.length);
  const names = ['e', 'q', 'i', 'asc_node', 'arg_per', 'perihelionJdTdb', 'meanMotionDegPerDay', 'M', 'trueAnomalyDeg', 'a', 'aphelionAu', 'periodDays'];
  return rows.map((row, index) => {
    close(number(row[0], 'Elements JD TDB'), epochs[index], 2e-9, 'Elements epoch');
    const elements = Object.fromEntries(names.map((name, i) => [name, number(row[i + 2], name)]));
    elements.gmAu3PerDay2 = number(text.match(/Keplerian GM\s+:\s+(\S+)/)?.[1], 'Keplerian GM');
    close(elements.q, elements.a * (1 - elements.e), 1e-12, 'Perihelion consistency');
    return elements;
  });
}

// These identities catch row shifts, units/frame disagreements and time mistakes
// independently of Find_Orb. They do not establish that the JPL orbit is exact.
function validateStateAndElements(state, elements) {
  const r = Math.hypot(...state.positionAu);
  const v2 = state.velocityAuPerDay.reduce((sum, value) => sum + value * value, 0);
  const inverseA = 2 / r - v2 / elements.gmAu3PerDay2;
  close(inverseA, 1 / elements.a, 2e-12, 'State/element specific energy');
  const [x, y, z] = state.positionAu, [vx, vy, vz] = state.velocityAuPerDay;
  const h = [y * vz - z * vy, z * vx - x * vz, x * vy - y * vx];
  const hNorm = Math.hypot(...h);
  close(Math.acos(h[2] / hNorm) * 180 / Math.PI, elements.i, 1e-9, 'State/element inclination');
  close(1 - hNorm * hNorm / (elements.gmAu3PerDay2 * elements.a), elements.e * elements.e,
    2e-12, 'State/element eccentricity');
}

async function main() {
  const {out, offline, observable} = options(process.argv.slice(2));
  const selectedProtocol = observable ? observableProtocol : protocol;
  await mkdir(resolve(out, 'raw'), {recursive: true});
  // Persist the experimental split before the first query. Resumes verify it.
  const protocolFile = observable ? 'observable-protocol.json' : 'protocol.json';
  const protocolPath = resolve(out, protocolFile);
  const protocolText = json(selectedProtocol);
  const previous = await existing(protocolPath);
  if (previous === null) await writeFile(protocolPath, protocolText, {flag: 'wx'});
  else assert.equal(previous, protocolText, 'Protocol differs; generate into a new directory');

  const cases = [];
  const unavailable = [];
  for (const body of selectedProtocol.bodies) {
    for (const date of selectedProtocol.datesUtc) {
      const id = (observable ? 'observable-' : '') + body.name.toLowerCase() + '-' + date.slice(0, 10);
      const anchor = jdUtc(date);
      const selection = observable ? await observableWindow(out, id, body, anchor, offline, selectedProtocol) : null;
      if (selection && selection.startJdUtc === null) {
        unavailable.push({id, split: body.split, object: {number: body.number, name: body.name, class: body.class},
          anchorDateUtc: date, anchorJdUtc: anchor, reason: selection.reason, rawFiles: selection.scanFiles});
        continue;
      }
      const start = selection?.startJdUtc ?? anchor;
      const obsTimes = selectedProtocol.observationMinutesAfterStart.map(minutes => start + minutes / 1440);
      const lastTime = obsTimes.at(-1);
      const heldoutTimes = selectedProtocol.holdoutHoursAfterLastObservation.map(hours => lastTime + hours / 24);
      const times = [...obsTimes, ...heldoutTimes];
      const common = {format: 'json', COMMAND: body.number + ';', OBJ_DATA: 'YES', MAKE_EPHEM: 'YES',
        TLIST_TYPE: 'JD', REF_SYSTEM: 'ICRF', CSV_FORMAT: 'YES', TIME_DIGITS: 'FRACSEC'};
      const observer = await response(out, id, 'observer', {...common, CENTER: selectedProtocol.observer,
        EPHEM_TYPE: 'OBSERVER', TIME_TYPE: 'UT', TLIST: tlist(times), QUANTITIES: '1,4,9,20,23,30',
        ANG_FORMAT: 'DEG', EXTRA_PREC: 'YES', CAL_FORMAT: 'JD', APPARENT: 'AIRLESS',
        ELEV_CUT: '-90', SKIP_DAYLT: 'NO', SOLAR_ELONG: '0,180'}, offline);
      assert.match(observer.text, new RegExp(`Target body name: ${body.number} ${body.name} `), 'Wrong target');
      const allRows = observerRows(observer.text, times);
      if (observable) {
        assert(allRows.slice(0, obsTimes.length).every(row =>
          row.altitudeDeg >= selectedProtocol.visibility.minimumAltitudeDeg &&
          row.solarPresence === selectedProtocol.visibility.requiredSolarPresence),
        `${id}: ten-minute verification disagrees with coarse visibility scan`);
      }
      const epochJdUtc = lastTime;
      const epochJdTdb = epochJdUtc + allRows[obsTimes.length - 1].tdbMinusUtcSeconds / DAY_SECONDS;
      const epochJdTt = epochJdUtc + TT_MINUS_UTC_SECONDS_2026 / DAY_SECONDS;
      const startJdTdb = start + allRows[0].tdbMinusUtcSeconds / DAY_SECONDS;
      const startJdTt = start + TT_MINUS_UTC_SECONDS_2026 / DAY_SECONDS;
      const truthEpochs = [startJdTdb, epochJdTdb];
      const geometric = {...common, CENTER: '500@10', TIME_TYPE: 'TDB', TLIST: tlist(truthEpochs),
        REF_PLANE: 'ECLIPTIC', OUT_UNITS: 'AU-D'};
      const elementsResponse = await response(out, id, 'elements', {...geometric, EPHEM_TYPE: 'ELEMENTS'}, offline);
      const stateResponse = await response(out, id, 'state', {...geometric, EPHEM_TYPE: 'VECTORS',
        VEC_TABLE: '2', VEC_CORR: 'NONE'}, offline);
      for (const result of [elementsResponse, stateResponse]) {
        assert.match(result.text, new RegExp(`Target body name: ${body.number} ${body.name} `), 'Wrong geometric target');
      }
      const [initialElements, elements] = elementsRows(elementsResponse.text, truthEpochs);
      const [initialState, state] = stateRows(stateResponse.text, truthEpochs);
      validateStateAndElements(initialState, initialElements);
      validateStateAndElements(state, elements);
      cases.push({id, split: body.split, object: {number: body.number, name: body.name, class: body.class},
        ...(selection ? {anchorDateUtc: date, anchorJdUtc: anchor, visibilitySelection: {
          scanDurationDays: selection.scanDurationDays, scanStartIndex: selection.scanStartIndex,
          scanWindow: selection.scanWindow, rule: selection.rule}} : {}),
        observer: selectedProtocol.observer, startJdUtc: start, startJdTdb, startJdTt, epochJdUtc, epochJdTdb, epochJdTt,
        observations: allRows.slice(0, obsTimes.length), holdout: allRows.slice(obsTimes.length),
        initialElements, initialState, elements, state,
        truthSolution: observer.text.match(/Target body name:.*\{source: ([^}]+)\}/)?.[1] ?? null,
        observerCenterEphemeris: observer.text.match(/Center body name:.*\{source: ([^}]+)\}/)?.[1] ?? null,
        rawFiles: [...(selection?.scanFiles ?? []), observer.record, elementsResponse.record, stateResponse.record]});
      process.stdout.write(`${id}: verified ${obsTimes.length} observations, ${heldoutTimes.length} holdouts, elements and state\n`);
    }
  }
  assert.equal(new Set(cases.map(item => item.id)).size, cases.length);
  const rawRecords = [...cases, ...unavailable].flatMap(item => item.rawFiles);
  const corpus = {schemaVersion: 1, provenance: {
    provider: 'NASA/JPL Horizons', api: API, documentation: [API_DOC, MANUAL],
    generator: 'experiments/short-arcs/fetch-horizons.mjs', generatorSha256: hash(await readFile(fileURLToPath(import.meta.url))),
    protocolFile, protocolSha256: hash(protocolText),
    retrievedFrom: rawRecords.map(record => record.retrievedAt).sort()[0],
    retrievedThrough: rawRecords.map(record => record.retrievedAt).sort().at(-1),
    rawResponseCount: rawRecords.length,
    observationCoordinates: 'ICRF equatorial astrometric RA/Dec in decimal degrees; Horizons quantity 1, down-leg light-time only, topocentric F52 reception time in UTC (TIME_TYPE=UT in 2026). Apparent altitude is metadata only.',
    elementCoordinates: 'Geometric heliocentric IAU76/J2000 ecliptic elements in au/degrees and Cartesian state in au and au/day. Reference obliquity 84381.448 arcseconds. initialElements/initialState are at startJdTdb; elements/state are at epochJdTdb (last observation). UTC is converted to TDB using Horizons quantity 30.',
    timeScales: 'epochJdTdb uses tabulated TDB−UTC; epochJdTt uses TT−UTC=69.184 s for these 2026 dates. The maximum TT−TDB distinction is about 2 ms and must not be silently treated as zero in precision state tests.',
    noise: 'No random measurement noise is present in these truth fixtures. Runners must record their own angular quantization, timing quantization, injected noise law and seed.',
    limitations: [
      'Numerical reference trajectories are independently computed by Horizons, not observed astrometry or exact physical reality. JPL orbit solutions, Earth orientation and ephemerides can change; cached raw responses are the replay authority.',
      observable
        ? 'Eight selected known numbered bodies and two anchor dates do not represent the discovery population. Input arcs pass a predeclared altitude/night selection; brightness, weather, lunar interference and survey detectability are not modeled. Future numerical prediction targets may be below the horizon or in daylight and must not automatically be treated as feasible follow-up observations.'
        : 'Eight selected known numbered bodies at two fixed epochs do not represent the discovery population. Cases may be below the horizon, near the Sun, in daylight, or too faint; all are retained with visibility metadata. These are unconditional geometry stress cases, not a telescope scheduling or survey benchmark.',
      'All epochs of a held-out object belong to the same split. Repeated epochs and noise realizations are correlated and must not be counted as independent discoveries.',
      'Horizons uses its own planetary ephemeris, massive-asteroid perturbations and fitted small-body force models. Find_Orb DE440 and configured force models may differ. Bennu, and potentially other near-Earth targets, can include nongravitational parameters; any mismatch limits interpretation of precision residuals and long-term prediction.',
      'A nominal orbit does not express the full uncertainty in the JPL solution. Formal covariance, catalog systematics, observational selection and real correlated astrometric errors are not sampled by this corpus. Nominal-truth coverage is not calibrated real-world population coverage.',
      'RA/Dec coordinates have finite Horizons output precision. Retain frame, light-time and time-scale conventions when synthesizing observations; do not use apparent RA/Dec in place of astrometric coordinates.',
    ],
  }, splitPolicy: selectedProtocol.splitPolicy, protocol: selectedProtocol, cases, ...(observable ? {unavailable} : {})};
  await writeFile(resolve(out, observable ? 'observable-corpus.json' : 'corpus.json'), json(corpus));
  process.stdout.write(`Wrote ${cases.length} cases from ${rawRecords.length} verified raw responses to ${out}\n`);
}

main().catch(error => { process.stderr.write(error.stack + '\n'); process.exitCode = 1; });
