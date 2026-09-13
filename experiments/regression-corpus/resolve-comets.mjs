// SPDX-License-Identifier: GPL-2.0-or-later
// Resolve SAME comet identities from cached Horizons apparition lookup tables.
// Record numbers are not permanent identifiers; retain the complete lookup and
// chosen row, then use that explicit record consistently for every query.
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {gunzipSync} from 'node:zlib';
import {root, request, immutableJson, existing, sha256} from './io.mjs';

const selectionText = await readFile(resolve(root, 'selection.json'), 'utf8');
const selection = JSON.parse(selectionText), records = [];
const rule = 'For an exact frozen comet identity with multiple Horizons apparition records, retain only rows whose MATCH DESIG equals its frozen SPK-ID and whose Primary Desig exactly matches its frozen primary designation. Choose greatest numeric Epoch-yr, then greatest numeric Record# as deterministic tie-break. Freeze the row before resolved-query or solver evaluation; use Record# followed by a semicolon for all observer/state/elements queries. Unique primary-ID ephemerides keep their already-pinned command. Never substitute another identity or select by fit/propagation outcomes.';
for (const body of selection.objects.filter(value => value.kind.startsWith('c'))) {
  const key = `horizons-${body.spkid}-observer-0`;
  const cached = JSON.parse(gunzipSync(await readFile(resolve(root, 'raw', key + '.json.gz'))));
  assert.equal(cached.query.COMMAND, `DES=${body.spkid};`);
  const {document, ref} = await request(key, 'https://ssd.jpl.nasa.gov/api/horizons.api', cached.query, {offline: true, horizons: true});
  assert.equal(document.signature?.source, 'NASA/JPL Horizons API');
  assert(['1.2', '1.3'].includes(document.signature.version));
  assert.equal(typeof document.result, 'string');
  if (document.result.includes('$$SOE')) {
    records.push({objectId: body.spkid, designation: body.pdes, mode: 'unique-primary-id', command: `DES=${body.spkid};`, lookup: ref});
    continue;
  }
  assert(document.result.includes('Matching small-bodies:') && document.result.includes('Primary Desig'),
    `Unrecognized comet lookup for ${body.pdes}`);
  const candidates = document.result.split('\n').flatMap(line => {
    const match = line.match(/^\s*(\d+)\s+(-?\d+)\s+(\d+)\s+(\S+)\s+(.+?)\s*$/);
    return match ? [{recordId: match[1], epochYear: Number(match[2]), matchedDesignation: match[3], primaryDesignation: match[4], name: match[5], rawLine: line}] : [];
  }).filter(row => row.matchedDesignation === body.spkid && row.primaryDesignation === body.pdes);
  assert(candidates.length > 1, `No exact same-object apparition list for ${body.pdes}`);
  candidates.sort((a, b) => b.epochYear - a.epochYear || Number(b.recordId) - Number(a.recordId));
  records.push({objectId: body.spkid, designation: body.pdes, mode: 'explicit-apparition', command: candidates[0].recordId + ';',
    chosenRow: candidates[0], exactIdentityCandidates: candidates.length, lookup: ref});
  process.stdout.write(`${body.pdes}: ${candidates[0].recordId}; (Epoch-yr ${candidates[0].epochYear})\n`);
}
const prior = await existing(resolve(root, 'comet-record-selection.json'));
await immutableJson('comet-record-selection.json', {schemaVersion: 1,
  frozenAt: prior ? JSON.parse(prior).frozenAt : new Date().toISOString(), selectionSha256: sha256(selectionText),
  rule, documentation: 'https://ssd.jpl.nasa.gov/horizons/manual.html#small-bodies', records});
process.stdout.write(`Pinned ${records.length} same-object comet resolutions from cached primary responses\n`);
