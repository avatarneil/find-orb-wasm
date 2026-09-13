// SPDX-License-Identifier: GPL-2.0-or-later
// Freeze catalog selection and object-level splits BEFORE any Horizons/solver run.
import assert from 'node:assert/strict';
import {readFile, writeFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {root, request, immutableJson, existing, sha256, json} from './io.mjs';

const fields = ['spkid', 'pdes', 'full_name', 'name', 'prefix', 'kind', 'class', 'epoch', 'a', 'e', 'q', 'i', 'tp', 'per',
  'data_arc', 'n_obs_used', 'condition_code', 'orbit_id', 'soln_date', 'two_body', 'source', 'A1', 'A2', 'A3', 'DT'];
const strata = [
  {id: 'atiras', count: 6, classes: 'IEO', priorities: ['163693']},
  {id: 'atens', count: 8, classes: 'ATE', priorities: ['99942']},
  {id: 'apollos', count: 10, classes: 'APO', priorities: ['101955', '1566', '3200'], limit: 512},
  {id: 'amors', count: 8, classes: 'AMO', priorities: ['433']},
  {id: 'inner-main-belt', count: 4, classes: 'IMB'},
  {id: 'main-belt-a2-to2p5', count: 6, classes: 'MBA', constraints: ['a|GE|2.0', 'a|LT|2.5'], priorities: ['4']},
  {id: 'main-belt-a2p5-to2p82', count: 6, classes: 'MBA', constraints: ['a|GE|2.5', 'a|LT|2.82'], priorities: ['1', '2', '3']},
  {id: 'main-belt-a2p82-to3p2', count: 6, classes: 'MBA', constraints: ['a|GE|2.82', 'a|LT|3.2']},
  {id: 'outer-belt-hilda-region', count: 6, classes: 'OMB', constraints: ['a|GE|3.7', 'a|LE|4.1'], priorities: ['153']},
  {id: 'jupiter-trojans', count: 6, classes: 'TJN', priorities: ['588']},
  {id: 'centaurs', count: 4, classes: 'CEN', priorities: ['2060', '5145']},
  {id: 'trans-neptunian', count: 4, classes: 'TNO', priorities: ['15760', '20000', '50000', '136199']},
  {id: 'short-period-comets', count: 6, classes: 'JFC,JFc,ETc', comet: true, numbered: true, priorities: ['2P', '67P']},
  {id: 'halley-type-comets', count: 4, classes: 'HTC', comet: true, numbered: true, priorities: ['1P']},
  {id: 'hyperbolic-comets', count: 4, classes: 'HYP', comet: true},
  {id: 'long-period-comets', count: 4, classes: 'COM', comet: true, constraints: ['e|GE|0.9', 'e|LT|1']},
  {id: 'low-eccentricity-belt', count: 2, classes: 'MBA', constraints: ['e|LT|0.02']},
  {id: 'retrograde-asteroids', count: 2, constraints: ['i|GT|90']},
];
export const protocol = {
  schemaVersion: 1, title: 'Find_Orb independent numerical regression corpus v1',
  purpose: 'Substantial deterministic software/mechanics regression coverage; not a simulated observational survey or an assertion that short arcs identify unique orbital elements.',
  observer: '500', center: '500@399', geometry: 'Geocentric astrometric angles; no horizon/daylight visibility interpretation. The separate F52 corpus provides real-station visibility coverage.',
  anchorsUtc: ['2026-02-01T00:00:00.000Z', '2026-08-01T00:00:00.000Z'],
  trackletDays: [0, 1, 2, 7, 14, 21, 30], exposureMinutes: [0, 20, 40, 60],
  arcs: [
    {id: 'one-hour', trackletDays: [0]},
    {id: 'two-night', trackletDays: [0, 1]},
    {id: 'three-night', trackletDays: [0, 1, 2]},
    {id: 'one-week', trackletDays: [0, 1, 2, 7]},
    {id: 'one-month', trackletDays: [0, 1, 2, 7, 14, 21, 30]},
  ],
  forecastDaysAfterEachArc: [1, 3, 7],
  catalog: {endpoint: 'https://ssd-api.jpl.nasa.gov/sbdb_query.api', fields, strata,
    minimumDataArcDays: 100, minimumObservationsUsed: 50,
    selection: 'Per stratum fetch first128 records ordered by numeric SPK-ID (Apollo first512), after declared class/element/arc constraints. Exclude comet fragments and D-prefix lost comets. Take listed priority identities first, then the smallest SPK-ID not already selected in a previous stratum. No solver output, residual or Horizons success enters selection; unavailable objects remain explicit failures, without substitution.',
    hildaCaveat: 'The semimajor-axis band selects Hilda-region outer-belt objects; no resonant-angle/libration classification is claimed.'},
  knownObjectDesignations: ['1', '2', '3', '4', '433', '588', '99942', '101955'],
  splitPolicy: 'All previously examined knownObjectDesignations are development/known-regression. Within each remaining stratum, sort by SHA256("find-orb-regression-v1:"+SPK-ID); first ceil(N/2) are development and remaining objects regression-holdout. Keep all epochs, arc lengths and realizations of an object in one split. Regression-holdout becomes a regression reference after it has been inspected; it is not an indefinitely reusable untouched method-selection sample.',
  supplements: [
    {pdes: '99942', id: 'apophis-2029-encounter', anchorUtc: '2029-04-12T00:00:00.000Z', purpose: 'Known close-approach temporal stress; always development/known-regression.'},
    {pdes: '2P', id: 'encke-perihelion', anchorRule: 'SBDB nominal perihelion tp (TDB) minus69.184seconds minus7days; this approximate UTC anchor defines a perihelion-centered stress window, not an independent precise perihelion-time estimate.', purpose: 'High-eccentricity/outgassing temporal stress; model-limited forward truth.'},
  ],
  limitations: [
    'Catalog ordering and named priorities favor established objects; this is not a population probability sample.',
    'Independent Horizons ephemerides are fitted numerical reference trajectories, not exact physical truth or observed astrometry.',
    'Planetary ephemerides, frame realization, massive-asteroid perturbations, nongravitational forces and special mission solutions can differ from Find_Orb. Preserve per-object physical applicability rather than silently enlarging error tolerances.',
    'Geocentric ranges and view angles include geometries that a ground telescope cannot observe. These cases test mechanics and software behavior; existing F52 samples test station and horizon behavior.',
    'Short-arc inverse problems can be nonidentifiable; parameter deltas against truth and nonlinear-family coverage require separate interpretation from native/WASM parity.',
  ],
};

export async function freezeCatalog({offline = false} = {}) {
  const protocolSha256 = await immutableJson('protocol.json', protocol);
  const used = new Set(), objects = [], rawFiles = [];
  for (const stratum of strata) {
    const constraints = ['data_arc|GE|100', 'n_obs_used|GE|50', ...(stratum.constraints ?? [])];
    const query = {fields: fields.join(','), 'full-prec': 'true', sort: 'spkid', limit: String(stratum.limit ?? 128),
      'sb-kind': stratum.comet ? 'c' : 'a', 'sb-xfrag': 'true', 'sb-cdata': JSON.stringify({AND: constraints}),
      ...(stratum.classes ? {'sb-class': stratum.classes} : {}), ...(stratum.numbered ? {'sb-ns': 'n'} : {})};
    const {document, ref} = await request('catalog-' + stratum.id, protocol.catalog.endpoint, query, {offline});
    assert.equal(document.signature?.source, 'NASA/JPL SBDB (Small-Body DataBase) Query API');
    assert.equal(document.signature.version, '1.0');
    assert.deepEqual(document.fields, fields);
    const rows = (document.data ?? []).map(row => Object.fromEntries(fields.map((field, i) => [field, row[i]])))
      .filter(row => row.prefix !== 'D').sort((a, b) => Number(a.spkid) - Number(b.spkid));
    const priority = (stratum.priorities ?? []).map(pdes => {
      const row = rows.find(item => item.pdes === pdes);
      assert(row, `Declared priority ${pdes} absent in ${stratum.id}; review catalog-only protocol before ephemeris acquisition`);
      return row;
    });
    const selected = [...priority, ...rows].filter(row => {
      if (used.has(String(row.spkid))) return false;
      used.add(String(row.spkid));
      return true;
    }).slice(0, stratum.count);
    // Only selected identities consume the cross-stratum exclusion set.
    used.clear(); for (const row of [...objects, ...selected]) used.add(String(row.spkid));
    assert.equal(selected.length, stratum.count, `${stratum.id}: insufficient catalog objects`);
    const fresh = selected.filter(row => !protocol.knownObjectDesignations.includes(row.pdes))
      .sort((a, b) => sha256('find-orb-regression-v1:' + a.spkid).localeCompare(sha256('find-orb-regression-v1:' + b.spkid)));
    const development = new Set(fresh.slice(0, Math.ceil(fresh.length / 2)).map(row => String(row.spkid)));
    for (const row of selected) objects.push({...row, spkid: String(row.spkid), stratum: stratum.id,
      name: row.name ?? row.pdes, knownRegression: protocol.knownObjectDesignations.includes(row.pdes),
      split: protocol.knownObjectDesignations.includes(row.pdes) || development.has(String(row.spkid)) ? 'development' : 'regression-holdout',
      catalogRaw: ref.path});
    rawFiles.push(ref);
    process.stdout.write(`${stratum.id}: froze ${selected.length} catalog identities\n`);
  }
  assert.equal(objects.length, 96);
  assert.equal(new Set(objects.map(row => row.spkid)).size, objects.length);
  const prior = await existing(resolve(root, 'selection.json'));
  const selection = {schemaVersion: 1, frozenAt: prior ? JSON.parse(prior).frozenAt : new Date().toISOString(),
    protocolSha256, objects, rawFiles};
  await immutableJson('selection.json', selection);
  return selection;
}

if (process.argv[1] && new URL(import.meta.url).pathname === resolve(process.argv[1])) {
  assert(process.argv.slice(2).every(value => value === '--offline'), 'Only --offline is supported');
  freezeCatalog({offline: process.argv.includes('--offline')}).then(selection =>
    process.stdout.write(`Frozen ${selection.objects.length} distinct objects before Horizons acquisition\n`))
    .catch(error => { process.stderr.write(error.stack + '\n'); process.exitCode = 1; });
}
