// SPDX-License-Identifier: GPL-2.0-or-later
// Fetch/replay independent regression truth after catalog.mjs freezes the IDs.
import assert from 'node:assert/strict';
import {readFile, writeFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {root, request, sha256, json, immutableJson, existing} from './io.mjs';

const API = 'https://ssd.jpl.nasa.gov/api/horizons.api';
const DAY_SECONDS = 86400, DAY_MINUTES = 1440, TT_MINUS_UTC = 69.184;
const utcJd = iso => Date.parse(iso) / 86400000 + 2440587.5;
const isoJd = jd => new Date(Math.round((jd - 2440587.5) * 86400000)).toISOString();
const tlist = times => times.map(jd => `'${jd.toFixed(12)}'`).join(' ');
const sourceMatch = (text, label) => text.match(new RegExp(label + ':.*\\{source: ([^}]+)\\}'))?.[1] ?? null;
const generationProtocol = {
  schemaVersion: 1, observerBatchEpochs: 40,
  epochPrecision: 'Horizons documents millisecond observer input precision. Round only the fractional SBDB-derived supplemental anchor to the nearest millisecond before acquisition, retaining its original nominal anchor. Preserve requested and returned epochs; observer epochs must agree within 1 ms and geometric JDTDB epochs within 2e-9 days. Matched epoch means agreement within this finite API precision, not exact real-number identity.',
  transportReason: 'A 74-epoch GET request with a URL length of 2,382 characters returned HTTP 502, while 37 epochs and 1,383 characters succeeded. Batch at 40 epochs independently of scientific outcomes.',
  observer: {CENTER: '500@399', EPHEM_TYPE: 'OBSERVER', TIME_TYPE: 'UT', REF_SYSTEM: 'ICRF', QUANTITIES: '1,20,23,30', ANG_FORMAT: 'DEG', EXTRA_PREC: 'YES', CSV_FORMAT: 'YES'},
  geometry: {CENTER: '500@10', TIME_TYPE: 'TDB', REF_SYSTEM: 'ICRF', REF_PLANE: 'ECLIPTIC', OUT_UNITS: 'AU-D', VEC_CORR: 'NONE'},
  timeConvention: 'UTC reception epochs; TDB = UTC + Horizons quantity 30 / 86400, TT = UTC + 69.184 / 86400. Require absolute(TDB − UTC − 69.184) < 0.002 seconds over these dates. TT/TDB labels refer to the same instant; velocities remain au/TDB-day.',
  gravityApplicability: 'Strict forward comparison requires a standard JPL# target, a DE440/441 Earth center and an explicit Small-body perts: Yes header, with no comet classification, no nonzero SBDB or Horizons nongravitational coefficient, no declared Horizons extra-force heading, and no catalog two-body flag. Otherwise the case is model-limited with explicit reasons; null SBDB coefficients remain unknown.',
  failures: 'Transport, parser, identity, frame, time and checksum errors fail closed. Only a cached successful HTTP Horizons response explicitly lacking an ephemeris or carrying an API error becomes an unavailable reference. These objects and raw responses remain recorded without replacement.',
};
class ReferenceUnavailable extends Error {
  constructor(message, rawFiles) { super(message); this.rawFiles = rawFiles; }
}

function numeric(value, label, nullable = false) {
  if (nullable && (value === '' || value === 'n.a.')) return null;
  const text = typeof value === 'number' ? String(value) : value;
  assert(typeof text === 'string' && /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?$/.test(text)
    && Number.isFinite(Number(text)), `${label}: invalid decimal/scientific number ${value}`);
  return Number(value);
}
function near(a, b, tolerance, label) {
  assert(Math.abs(a - b) <= tolerance, `${label}: ${a} versus ${b}`);
}
function table(document, body, expectedHeader, times, timeLabel, epochToleranceDays = 2e-9) {
  assert(!document.error, `Horizons error: ${document.error}`);
  assert.equal(document.signature?.source, 'NASA/JPL Horizons API');
  assert(['1.2', '1.3'].includes(document.signature.version), 'Review changed Horizons API version');
  const text = document.result;
  assert.equal(typeof text, 'string');
  const target = text.match(/Target body name:\s+(.+?)\s+\{source:/)?.[1];
  const designation = body.pdes.replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\s+/g, '\\s+');
  const identity = /^\d+$/.test(body.pdes) ? new RegExp('^' + designation + '(?=$|\\s|\\()')
    : new RegExp('(?:^|[\\s(/])' + designation + '(?=$|[\\s)/])');
  assert(target && identity.test(target), `Wrong or ambiguous target for ${body.pdes}: ${target}`);
  assert.equal(text.split('$$SOE').length, 2, `No unique ephemeris for ${body.pdes}`);
  assert.equal(text.split('$$EOE').length, 2);
  const [before, after] = text.split('$$SOE');
  const header = before.split('\n').filter(line => line.includes(',')).at(-1);
  assert.deepEqual(header?.split(',').map(value => value.trim()).filter(Boolean), expectedHeader,
    'Review changed Horizons CSV columns');
  const rows = after.split('$$EOE')[0].trim().split('\n').map(line => line.split(',').map(value => value.trim()));
  assert.equal(rows.length, times.length, 'Unexpected row count');
  for (let i = 0; i < rows.length; i++) near(numeric(rows[i][0], timeLabel), times[i], epochToleranceDays, timeLabel);
  return rows;
}
function observerRows(document, body, times) {
  assert.match(document.result ?? '', /Center body name: Earth \(399\)/);
  assert(/Center-site name: GEOCENTRIC/.test(document.result ?? ''), 'Expected Horizons GEOCENTRIC observer header');
  return table(document, body, ['Date_________JDUT', 'R.A.___(ICRF)', 'DEC____(ICRF)', 'delta', 'deldot', 'S-O-T', '/r', 'TDB-UT'], times, 'UTC epoch', 0.001 / DAY_SECONDS)
    .map((row, index) => {
      assert.equal(row.length, 11);
      const value = {requestedJdUtc: times[index], jdUtc: numeric(row[0], 'JD UTC'), RA: numeric(row[3], 'RA'), Dec: numeric(row[4], 'Dec'),
        rangeAu: numeric(row[5], 'range'), rangeRateKmPerSecond: numeric(row[6], 'range rate'),
        elongationDeg: numeric(row[7], 'elongation'), tdbMinusUtcSeconds: numeric(row[9], 'TDB−UTC')};
      assert(value.RA >= 0 && value.RA < 360 && Math.abs(value.Dec) <= 90 && value.rangeAu > 0);
      assert(Math.abs(value.tdbMinusUtcSeconds - TT_MINUS_UTC) < 0.002,
        'Review leap-second assumptions for requested temporal supplement');
      return value;
    });
}
function geometry(document) {
  assert.match(document.result ?? '', /Center body name: Sun \(10\)/);
  assert.match(document.result ?? '', /Reference frame : Ecliptic of J2000\.0/);
  assert.match(document.result ?? '', /Output units\s+: AU-D/);
}
function stateRows(document, body, times) {
  geometry(document);
  assert.match(document.result, /Output type\s+: GEOMETRIC cartesian states/);
  return table(document, body, ['JDTDB', 'Calendar Date (TDB)', 'X', 'Y', 'Z', 'VX', 'VY', 'VZ'], times, 'State TDB epoch')
    .map(row => ({horizonsJdTdb: numeric(row[0], 'State printed JDTDB'), positionAu: row.slice(2, 5).map(v => numeric(v, 'position')),
      velocityAuPerDay: row.slice(5, 8).map(v => numeric(v, 'velocity'))}));
}
function elementRows(document, body, times) {
  geometry(document);
  assert.match(document.result, /Output type\s+: GEOMETRIC osculating elements/);
  const gm = numeric(document.result.match(/Keplerian GM\s+:\s+(\S+)/)?.[1], 'Keplerian GM');
  return table(document, body, ['JDTDB', 'Calendar Date (TDB)', 'EC', 'QR', 'IN', 'OM', 'W', 'Tp', 'N', 'MA', 'TA', 'A', 'AD', 'PR'], times, 'Elements TDB epoch')
    .map(row => {
      const names = ['e', 'q', 'i', 'asc_node', 'arg_per', 'perihelionJdTdb', 'meanMotionDegPerDay', 'M', 'trueAnomalyDeg', 'a', 'aphelionAu', 'periodDays'];
      const values = Object.fromEntries(names.map((name, i) => [name, numeric(row[i + 2], name, i >= 10)]));
      if (values.e >= 1) { values.aphelionAu = null; values.periodDays = null; }
      else assert(values.aphelionAu !== null && values.periodDays > 0, 'Elliptic orbit requires finite aphelion and positive period');
      return {...values, horizonsJdTdb: numeric(row[0], 'Elements printed JDTDB'), gmAu3PerDay2: gm};
    });
}
function consistent(state, elements) {
  const r = Math.hypot(...state.positionAu), v2 = state.velocityAuPerDay.reduce((n, v) => n + v * v, 0);
  const [x, y, z] = state.positionAu, [vx, vy, vz] = state.velocityAuPerDay;
  const h = [y * vz - z * vy, z * vx - x * vz, x * vy - y * vx], h2 = h.reduce((n, v) => n + v * v, 0);
  const gm = elements.gmAu3PerDay2;
  near(2 / r - v2 / gm, 1 / elements.a, 2e-11, 'State/element inverse semimajor axis');
  near(h2 / (gm * (1 + elements.e)), elements.q, 1e-8, 'Stable all-conic perihelion identity');
  near(Math.acos(Math.max(-1, Math.min(1, h[2] / Math.sqrt(h2)))) * 180 / Math.PI, elements.i, 1e-7, 'Inclination identity');
  near(1 - h2 / (gm * elements.a), elements.e ** 2, 2e-10, 'State/element eccentricity identity');
}

function grid(protocol, anchorJdUtc) {
  const inputMinutes = protocol.trackletDays.flatMap(day => protocol.exposureMinutes.map(minute => day * DAY_MINUTES + minute));
  const arcs = protocol.arcs.map(arc => {
    const observationMinutes = arc.trackletDays.flatMap(day => protocol.exposureMinutes.map(minute => day * DAY_MINUTES + minute));
    const endMinute = observationMinutes.at(-1);
    return {...arc, observationMinutes, endMinute, predictionMinutes: protocol.forecastDaysAfterEachArc.map(day => endMinute + day * DAY_MINUTES)};
  });
  const minutes = [...new Set([...inputMinutes, ...arcs.flatMap(arc => arc.predictionMinutes)])].sort((a, b) => a - b);
  const truthMinutes = [0, ...arcs.map(arc => arc.endMinute)];
  return {minutes, truthMinutes, times: minutes.map(minute => anchorJdUtc + minute / DAY_MINUTES),
    arcs: arcs.map(arc => ({id: arc.id, observationIndices: arc.observationMinutes.map(minute => minutes.indexOf(minute)),
      predictionIndices: arc.predictionMinutes.map(minute => minutes.indexOf(minute)), truthEpochIndex: truthMinutes.indexOf(arc.endMinute)}))};
}

function anchors(protocol, body) {
  const values = protocol.anchorsUtc.map(date => ({anchorJdUtc: utcJd(date), date: date.slice(0, 10), role: 'core'}));
  for (const supplement of protocol.supplements.filter(item => item.pdes === body.pdes)) {
    const nominalAnchorJdUtc = supplement.anchorUtc ? utcJd(supplement.anchorUtc) : numeric(body.tp, 'Catalog perihelion') - TT_MINUS_UTC / DAY_SECONDS - 7;
    const anchorJdUtc = supplement.anchorUtc ? nominalAnchorJdUtc : utcJd(isoJd(nominalAnchorJdUtc));
    assert(anchorJdUtc > 2457754.5 && anchorJdUtc + 38 < 2466192.5, 'Temporal supplement leaves pinned leap-second/compact-ephemeris interval');
    values.push({anchorJdUtc, nominalAnchorJdUtc, anchorQuantizationSeconds: (anchorJdUtc - nominalAnchorJdUtc) * DAY_SECONDS, date: supplement.id, role: 'temporal-supplement', purpose: supplement.purpose});
  }
  return values;
}

async function fetchBody(protocol, body, offline, cometResolution) {
  const scheduled = anchors(protocol, body).map(anchor => ({...anchor, ...grid(protocol, anchor.anchorJdUtc)}));
  const allTimes = scheduled.flatMap(value => value.times).sort((a, b) => a - b);
  assert.equal(new Set(allTimes).size, allTimes.length, 'Overlapping schedules must use an explicit deduplicated mapping');
  const common = {format: 'json', COMMAND: cometResolution?.command ?? `DES=${body.spkid};`, OBJ_DATA: 'YES', MAKE_EPHEM: 'YES',
    TLIST_TYPE: 'JD', REF_SYSTEM: 'ICRF', CSV_FORMAT: 'YES', TIME_DIGITS: 'FRACSEC'};
  const rawFiles = cometResolution ? [cometResolution.lookup] : [];
  const keyPrefixBase = cometResolution?.mode === 'explicit-apparition'
    ? `horizons-${body.spkid}-record-${cometResolution.chosenRow.recordId}` : `horizons-${body.spkid}`;
  const keyPrefix = scheduled.some(value => value.anchorQuantizationSeconds) ? keyPrefixBase + '-millisecond' : keyPrefixBase;
  async function horizons(key, query) {
    const value = await request(key, API, query, {offline, horizons: true});
    rawFiles.push(value.ref);
    assert.equal(value.document.signature?.source, 'NASA/JPL Horizons API', 'Unknown Horizons response source');
    assert(['1.2', '1.3'].includes(value.document.signature.version), 'Review changed Horizons API version');
    assert(typeof value.document.result === 'string' || typeof value.document.error === 'string', 'Malformed Horizons response');
    if (value.document.error || (typeof value.document.result === 'string' && !value.document.result.includes('$$SOE'))) {
      throw new ReferenceUnavailable(`Horizons reference unavailable for ${body.pdes}: ` +
        String(value.document.error ?? value.document.result).trim(), [...rawFiles]);
    }
    return value;
  }
  const observerBatches = [], rows = [];
  for (let offset = 0; offset < allTimes.length; offset += generationProtocol.observerBatchEpochs) {
    const batch = allTimes.slice(offset, offset + generationProtocol.observerBatchEpochs);
    const value = await horizons(`${keyPrefix}-observer-${offset}`, {...common, CENTER: protocol.center,
      EPHEM_TYPE: 'OBSERVER', TIME_TYPE: 'UT', TLIST: tlist(batch), QUANTITIES: '1,20,23,30',
      ANG_FORMAT: 'DEG', EXTRA_PREC: 'YES', CAL_FORMAT: 'JD'});
    observerBatches.push(value);
    rows.push(...observerRows(value.document, body, batch));
  }
  const observer = observerBatches[0];
  for (const batch of observerBatches) {
    assert.equal(sourceMatch(batch.document.result, 'Target body name'), sourceMatch(observer.document.result, 'Target body name'), 'Target source changed between batches');
    assert.equal(sourceMatch(batch.document.result, 'Center body name'), sourceMatch(observer.document.result, 'Center body name'), 'Observer ephemeris changed between batches');
  }
  const rowsByTime = new Map(allTimes.map((time, i) => [time, rows[i]]));
  const truthTimes = scheduled.flatMap(value => value.truthMinutes.map(minute => value.anchorJdUtc + minute / DAY_MINUTES)).sort((a, b) => a - b);
  const truthTdb = truthTimes.map(time => time + rowsByTime.get(time).tdbMinusUtcSeconds / DAY_SECONDS);
  const geometric = {...common, CENTER: '500@10', TIME_TYPE: 'TDB', TLIST: tlist(truthTdb), REF_PLANE: 'ECLIPTIC', OUT_UNITS: 'AU-D'};
  const elements = await horizons(keyPrefix + '-elements', {...geometric, EPHEM_TYPE: 'ELEMENTS'});
  const states = await horizons(keyPrefix + '-state', {...geometric, EPHEM_TYPE: 'VECTORS', VEC_TABLE: '2', VEC_CORR: 'NONE'});
  for (const value of [elements, states]) {
    assert.equal(sourceMatch(value.document.result, 'Target body name'), sourceMatch(observer.document.result, 'Target body name'),
      'Target orbit solution changed between observer and geometric queries');
    assert.equal(sourceMatch(value.document.result, 'Center body name'), sourceMatch(observer.document.result, 'Center body name'),
      'Sun/Earth ephemeris source differs between observer and geometric queries');
  }
  const parsedElements = elementRows(elements.document, body, truthTdb), parsedStates = stateRows(states.document, body, truthTdb);
  const truthByTime = new Map(truthTimes.map((time, i) => {
    consistent(parsedStates[i], parsedElements[i]);
    assert.equal(parsedStates[i].horizonsJdTdb, parsedElements[i].horizonsJdTdb, 'State and elements have different returned TDB epochs');
    return [time, {jdUtc: time, jdTt: time + TT_MINUS_UTC / DAY_SECONDS, jdTdb: truthTdb[i],
      state: parsedStates[i], elements: parsedElements[i]}];
  }));
  const targetSource = sourceMatch(observer.document.result, 'Target body name');
  const centerSource = sourceMatch(observer.document.result, 'Center body name');
  const observerHeader = observer.document.result.split('$$SOE')[0];
  const nongrav = Object.fromEntries(['A1', 'A2', 'A3', 'DT'].map(key => [key, body[key] === null ? null : numeric(body[key], key)]));
  const headerNongrav = [...observerHeader.matchAll(/\b(A1|A2|A3|AMRAT)\s*=\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?)(?=\s|$|[,;)])/g)]
    .map(match => ({parameter: match[1], value: numeric(match[2], 'Horizons force coefficient'), lexeme: match[2]}));
  const reasons = [], reasonCodes = [];
  const limited = (code, reason) => { reasonCodes.push(code); reasons.push(reason); };
  if (body.kind.startsWith('c')) limited('comet-force-model', 'Baseline planetary-gravity configuration does not assert parity with fitted comet outgassing laws.');
  if (['A1', 'A2', 'A3'].some(key => nongrav[key] !== null && nongrav[key] !== 0)) limited('explicit-sbdb-nongrav', 'SBDB snapshot has an explicit nonzero nongravitational acceleration parameter.');
  if (headerNongrav.some(item => item.value !== 0)) limited('explicit-horizons-nongrav', 'The Horizons header contains an explicit nonzero A1/A2/A3/AMRAT coefficient, independently of catalog metadata.');
  if (body.two_body === 'T') limited('catalog-two-body', 'SBDB marks a low-precision two-body orbit solution.');
  if (/non.gravitational|yarkovsky|thermal.recoil|outgassing/i.test(observerHeader)) limited('horizons-extra-force-declaration', 'Horizons explicitly declares a nongravitational/thermal/outgassing model; preserve its header without treating missing catalog coefficients as zero.');
  if (!/^JPL#/.test(targetSource ?? '') || !/^DE44[01]$/.test(centerSource ?? '')) limited('unknown-special-ephemeris-model', 'Horizons uses a special target or observer ephemeris source; its complete physical model is not established by the SBDB coefficients.');
  if (!/Small-body perts:\s+Yes/.test(observerHeader)) limited('unrecognized-gravity-header', 'The standard small-body perturbation-model header is absent or unrecognized.');
  const model = {catalogNongravitational: nongrav, catalogTwoBody: body.two_body, targetSource, observerCenterSource: centerSource,
    cometResolution: cometResolution ?? null,
    horizonsNongravitationalAssignments: headerNongrav,
    nullCoefficientMeaning: 'Unknown/not listed in this catalog snapshot; null is not evidence of zero acceleration.',
    reasonCodes, evidenceStatus: reasonCodes.length ? 'model-limited-or-unknown' : 'recognized-standard-gravitational-integration',
    exactHeaders: Object.fromEntries([['observer', observer], ['elements', elements], ['state', states]].map(([kind, record]) => {
      const header = record.document.result.split('$$SOE')[0];
      return [kind, {rawPath: record.ref.path, responseResultPrefixBefore: '$$SOE', sha256: sha256(header), bytes: Buffer.byteLength(header)}];
    })),
    forceMetadata: observerHeader.split('\n').filter(line => /non.gravitational|yarkovsky|thermal.recoil|outgassing|A1=|A2=|A3=|AMRAT=|ALN=|NK=|R0=|Small-body perts:|Small perturbers:/i.test(line))};
  return scheduled.map(schedule => {
    const astrometry = schedule.times.map(time => rowsByTime.get(time));
    const truthEpochs = schedule.truthMinutes.map(minute => truthByTime.get(schedule.anchorJdUtc + minute / DAY_MINUTES));
    const first = truthEpochs[0], epoch = truthEpochs[1], initialArc = schedule.arcs[0];
    return {id: `sb-${body.spkid}-${schedule.date}`, objectId: body.spkid,
      object: {spkid: body.spkid, number: body.kind === 'an' ? Number(body.pdes) : null, designation: body.pdes,
        name: body.name, fullName: body.full_name, class: body.class, kind: body.kind, stratum: body.stratum},
      split: body.split, knownRegression: body.knownRegression, role: schedule.role, purpose: schedule.purpose ?? null,
      observer: protocol.observer, geometry: protocol.geometry,
      anchorJdUtc: schedule.anchorJdUtc, nominalAnchorJdUtc: schedule.nominalAnchorJdUtc ?? schedule.anchorJdUtc,
      anchorQuantizationSeconds: schedule.anchorQuantizationSeconds ?? 0, anchorUtc: isoJd(schedule.anchorJdUtc),
      startJdUtc: first.jdUtc, startJdTt: first.jdTt, startJdTdb: first.jdTdb,
      epochJdUtc: epoch.jdUtc, epochJdTt: epoch.jdTt, epochJdTdb: epoch.jdTdb,
      initialState: first.state, initialElements: first.elements, state: epoch.state, elements: epoch.elements,
      observations: initialArc.observationIndices.map(index => astrometry[index]),
      holdout: initialArc.predictionIndices.map(index => astrometry[index]),
      astrometry, arcs: schedule.arcs, truthEpochs, model,
      applicability: {fit: true, forwardTruth: reasons.length ? 'model-limited' : 'strict',
        reason: reasons.length ? reasons.join(' ') : 'Planetary-gravity forward comparison; modest differences from independently realized JPL ephemeris/forces remain possible.',
        toleranceArcsec: reasons.length ? null : 0.1,
        inverseTruth: 'Short-arc element recovery is informational; exercise solver validity and numerical parity without assuming a unique true solution.'},
      rawFiles};
  });
}

async function main() {
  assert(process.argv.slice(2).every(value => value === '--offline'), 'Only --offline is supported');
  const offline = process.argv.includes('--offline');
  const previousCorpus = await existing(resolve(root, 'corpus.json'));
  if (offline) assert(previousCorpus && JSON.parse(previousCorpus).complete, 'Offline replay requires the previously completed corpus');
  const protocolText = await readFile(resolve(root, 'protocol.json'), 'utf8');
  const selectionText = await readFile(resolve(root, 'selection.json'), 'utf8');
  const cometResolutionText = await readFile(resolve(root, 'comet-record-selection.json'), 'utf8');
  const cometResolutions = JSON.parse(cometResolutionText);
  const acquisitionHistoryText = await readFile(resolve(root, 'acquisition-history.json'), 'utf8');
  const acquisitionHistory = JSON.parse(acquisitionHistoryText);
  assert.equal(cometResolutions.selectionSha256, sha256(selectionText), 'Comet resolutions refer to another catalog selection');
  const protocol = JSON.parse(protocolText), selection = JSON.parse(selectionText);
  assert.equal(sha256(protocolText), selection.protocolSha256, 'Frozen catalog protocol changed');
  assert.equal(selection.objects.length, 96);
  if (offline) assert(await existing(resolve(root, 'generation-protocol.json')), 'Missing frozen generation protocol');
  const generationProtocolSha256 = await immutableJson('generation-protocol.json', generationProtocol);
  const cases = [], unavailable = [], completedObjects = [];
  const sourceHashes = Object.fromEntries(await Promise.all(['fetch.mjs', 'catalog.mjs', 'io.mjs', 'resolve-comets.mjs'].map(async name => [name, sha256(await readFile(resolve(root, name)))])));
  async function save(complete) {
    if (offline && !complete) return;
    const uniqueRefs = new Map([...selection.rawFiles, ...acquisitionHistory.records.map(value => value.rawFile), ...cases.flatMap(item => item.rawFiles), ...unavailable.flatMap(item => item.rawFiles)].map(ref => [ref.path, ref]));
    const sentinelIds = protocol.catalog.strata.flatMap(stratum => {
      const body = selection.objects.find(item => item.stratum === stratum.id);
      const item = cases.find(value => value.objectId === body.spkid && value.role === 'core');
      return item ? [item.id] : [];
    });
    const output = {schemaVersion: 1, complete, provenance: {provider: 'NASA/JPL SBDB and Horizons',
      protocolFile: 'protocol.json', protocolSha256: sha256(protocolText), selectionFile: 'selection.json',
      selectionSha256: sha256(selectionText), selectionFrozenAt: selection.frozenAt, generatorSources: sourceHashes,
      generationProtocolFile: 'generation-protocol.json', generationProtocolSha256,
      cometRecordSelectionFile: 'comet-record-selection.json', cometRecordSelectionSha256: sha256(cometResolutionText),
      acquisitionHistoryFile: 'acquisition-history.json', acquisitionHistorySha256: sha256(acquisitionHistoryText),
      documentation: ['https://ssd-api.jpl.nasa.gov/doc/sbdb_query.html', 'https://ssd-api.jpl.nasa.gov/doc/sbdb_filter.html',
        'https://ssd-api.jpl.nasa.gov/doc/horizons.html', 'https://ssd.jpl.nasa.gov/horizons/manual.html'],
      observationCoordinates: 'Geocentric ICRF astrometric RA/Dec in decimal degrees, down-leg light-time only (Horizons quantity 1), UTC reception epochs, MPC 500 / Earth center. No ground-station visibility interpretation.',
      stateCoordinates: 'Geometric Sun-centered IAU76/J2000 ecliptic position au and velocity au/TDB-day, obliquity 84381.448 arcsec relative to ICRF. GM is copied from each element table. TT and TDB labels denote the same physical instant: TDB−UTC is Horizons quantity 30; TT−UTC=69.184s for the pinned dates. Their ~2 ms difference is not discarded.',
      noise: 'Zero-noise numerical references with finite Horizons angular/time output precision. Noise laws, astrometric quantization, biased/contaminated scenarios and seeds belong to the regression harness.',
      rawFiles: [...uniqueRefs.values()].sort((a, b) => a.path.localeCompare(b.path))},
      suite: {sentinelRule: 'First frozen catalog selection per stratum, first core anchor only; unavailable targets are omitted and remain explicit unavailable records. This selection is independent of solver outcomes.', sentinelIds,
        stationSupplement: {file: '../short-arcs/fixtures/observable-corpus.json', caseIds: ['observable-ceres-2026-09-01', 'observable-pallas-2026-09-01', 'observable-juno-2026-03-01', 'observable-juno-2026-09-01', 'observable-vesta-2026-09-01', 'observable-eros-2026-03-01', 'observable-achilles-2026-03-01'], role: 'Previously examined F52 known-regression station/visibility supplement'},
        defaultArcs: protocol.arcs.map(arc => arc.id)},
      counts: {plannedObjects: selection.objects.length, completedObjects: completedObjects.length,
        usableObjects: new Set(cases.map(item => item.objectId)).size, usableCases: cases.length,
        coreCases: cases.filter(item => item.role === 'core').length, temporalSupplementCases: cases.filter(item => item.role !== 'core').length,
        unavailableObjects: unavailable.length}, objects: selection.objects, cases, unavailable};
    const normalized = json(output);
    if (offline) assert.equal(sha256(normalized), sha256(previousCorpus), 'Offline replay differs from completed corpus; no file was overwritten');
    else await writeFile(resolve(root, 'corpus.json'), normalized);
  }
  for (const body of selection.objects) {
    try {
      const resolution = cometResolutions.records.find(value => value.objectId === body.spkid);
      assert(!body.kind.startsWith('c') || resolution, 'Missing frozen comet record resolution');
      const result = await fetchBody(protocol, body, offline, resolution);
      cases.push(...result);
      process.stdout.write(`${body.full_name.trim()}: ${result.length} cases, ${result[0].astrometry.length} astrometric epochs/case, all state/element checks passed\n`);
    } catch (error) {
      if (!(error instanceof ReferenceUnavailable)) throw error;
      // Keep every chosen catalog identity; do not substitute an easier target.
      const message = String(error.message);
      unavailable.push({objectId: body.spkid, designation: body.pdes, name: body.name, stratum: body.stratum,
        split: body.split, stage: 'independent-reference-acquisition', reason: message, rawFiles: error.rawFiles});
      process.stdout.write(`UNAVAILABLE ${body.full_name.trim()}: ${message}\n`);
    }
    completedObjects.push(body.spkid);
    await save(false);
  }
  assert(new Set(cases.map(item => item.objectId)).size >= 80 && cases.filter(item => item.role === 'core').length >= 160,
    'The substantial usable-corpus target was not reached; inspect acquisition failures before accepting this dataset');
  await save(true);
  process.stdout.write(`Completed ${cases.length} usable cases, ${new Set(cases.map(item => item.objectId)).size} objects; ${unavailable.length} explicit unavailable objects\n`);
}

main().catch(error => { process.stderr.write(error.stack + '\n'); process.exitCode = 1; });
