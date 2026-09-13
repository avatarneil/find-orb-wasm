#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
// Summarize the archived baseline and the explicit light-deflection intervention.
import assert from 'node:assert/strict';
import {readFile,writeFile} from 'node:fs/promises';
import {gunzipSync} from 'node:zlib';
import {sha} from '../experiments/short-arcs/methods.mjs';
const root='results/regression-corpus';
const json=async path=>JSON.parse(await readFile(path,'utf8'));
const runs={},records={};
for(const name of ['forward-v1','sentinel-v1','forward-v2','sentinel-v2']) {
  const path=root+'/'+name,manifestBytes=await readFile(path+'/manifest.json'),m=JSON.parse(manifestBytes);
  const bytes=await readFile(path+'/results.json'),summaryBytes=await readFile(path+'/summary.json');
  assert.equal(sha(bytes),m.resultsSHA256);assert.equal(sha(summaryBytes),m.summarySHA256);
  const rows=JSON.parse(bytes),summary=JSON.parse(summaryBytes),replay=await json(root+'/checks/'+name+'-replay.json');
  assert.equal(replay.verified,true);assert.equal(replay.manifestSHA256,sha(manifestBytes));
  records[name]=rows;
  runs[name]={pairs:rows.length,passedPairs:rows.filter(r=>r.comparison.pass).length,failedPairs:summary.failedPairs,
    objects:new Set(rows.map(r=>r.objectId)).size,cases:new Set(rows.map(r=>r.caseId)).size,
    rawRecords:m.rawFiles,manifestSHA256:sha(manifestBytes),summaryFile:name+'/summary.json',replayFile:'checks/'+name+'-replay.json',
    validationScope:summary.validationScope,maxEngineDirectionDifferenceArcsec:Math.max(...rows.map(r=>r.comparison.maxDirectionDifferenceArcsec)),
    maxEngineRangeDifferenceAu:Math.max(...rows.map(r=>r.comparison.maxRangeDifferenceAu)),
    independentForwardReference:Object.fromEntries(['strict','model-limited'].map(mode=>{
      const selected=rows.filter(r=>r.kind==='forward'&&r.applicability.forwardTruth===mode);
      const worst=selected.toSorted((a,b)=>b.comparison.reference.candidateMaxArcsec-a.comparison.reference.candidateMaxArcsec)[0];
      return [mode,{cases:selected.length,maxArcsec:worst?.comparison.reference.candidateMaxArcsec??null,worstCase:worst?.caseId??null,
        absoluteGuardEnforced:mode==='strict'}];
    }))};
  const fitRows=rows.filter(r=>r.kind==='fit');
  if(fitRows.length) {
    const worst=fitRows.toSorted((a,b)=>b.candidate.predictions.at(-1).errorArcsec-a.candidate.predictions.at(-1).errorArcsec)[0];
    runs[name].fitReferenceDiagnostic={worstSevenDayCase:worst.caseId,arc:worst.arc,
      sevenDayErrorArcsec:worst.candidate.predictions.at(-1).errorArcsec,
      interpretation:'Informational truth error, not a passing accuracy claim. Geocentric short-arc fits can be nonidentifiable; physical/input-convention differences also remain.'};
  }
}
async function command(name,row,role) {
  const e=row[role].evidence,compressed=await readFile(root+'/'+name+'/'+e.rawFile);
  assert.equal(sha(compressed),e.gzipSHA256);const bytes=gunzipSync(compressed);assert.equal(sha(bytes),e.rawSHA256);
  const c=JSON.parse(bytes).command;assert.equal(sha(JSON.stringify(c)),e.commandSHA256);
  return {args:c.args,files:c.files,outputs:c.outputs};
}
let controlledCommands=0;
const oldManifest=await json(root+'/forward-v1/manifest.json'),newManifest=await json(root+'/forward-v2/manifest.json');
for(const role of ['baseline','candidate'])assert.equal(oldManifest.engines[role].manifestSHA256,newManifest.engines[role].manifestSHA256,'Same verified engine/data for convention intervention');
for(const [i,oldRow] of records['forward-v1'].entries()) {
  const newRow=records['forward-v2'][i];assert.equal(newRow.caseId,oldRow.caseId);
  for(const role of ['baseline','candidate']) {
    const oldCommand=await command('forward-v1',oldRow,role),newCommand=await command('forward-v2',newRow,role);
    const key='/job/job.env';assert.ok(!oldCommand.files[key].includes('DISABLE_LIGHT_BENDING='));
    assert.equal(newCommand.files[key].split('DISABLE_LIGHT_BENDING=1\n').length,2);
    newCommand.files[key]=newCommand.files[key].replace('DISABLE_LIGHT_BENDING=1\n','');
    assert.deepEqual(newCommand,oldCommand,'Only executable intervention is the emitted-coordinate switch');controlledCommands++;
  }
}
const chicago='sb-20000334-2026-08-01';
const a=records['forward-v1'].find(r=>r.caseId===chicago),b=records['forward-v2'].find(r=>r.caseId===chicago);
const tests=await readFile(root+'/checks/tests.log.txt','utf8');
const testCounts=Object.fromEntries(['tests','pass','fail','skipped'].map(k=>[k,Number(tests.match(new RegExp('^ℹ '+k+' (\\d+)$','m'))?.[1])]));
assert.ok(Object.values(testCounts).every(Number.isInteger));assert.equal(testCounts.fail,0);assert.equal(testCounts.skipped,0);
const checks={schemaVersion:1,corpus:await json(root+'/data-validation.json'),
  sourceSHA256:sha(await readFile(new URL(import.meta.url))),
  tests:{command:'npm run test:regression',...testCounts,log:'checks/tests.log.txt',sha256:sha(tests)},runs,
  coordinateConventionControl:{executableCommandsCompared:controlledCommands,
    onlyChange:'DISABLE_LIGHT_BENDING=1 in emitted ephemerides; the internal fit measurement model is unchanged.',
    chicago:{caseId:chicago,rows:a.candidate.predictions.map((p,i)=>({jdUtc:p.jdUtc,defaultErrorArcsec:p.errorArcsec,matchedConventionErrorArcsec:b.candidate.predictions[i].errorArcsec}))},
    interpretation:'The default-output reference disagreement includes differential solar light deflection. Preserve it as convention evidence; use v2 for matched forecast-coordinate comparisons.'},
  scope:'194 one-hour-endpoint independent-state propagation pairs, plus 19 sentinel propagation and 19 sentinel fit pairs (18 objects; one additional week-long arc). The full 5,820-call noise/arc plan was not run. Passing port parity does not assert accurate short-arc orbital recovery.',
  visual:{browser:'Chromium',desktopWidth:1400,mobileWidth:390,scriptErrors:[],mobileOverflow:false,apophisFilterCases:3,
    inspection:'Desktop and mobile report screenshots inspected; filters checked against the final 194-case corpus.'}};
await writeFile(root+'/checks.json',JSON.stringify(checks,null,2)+'\n');
console.log(JSON.stringify({tests:testCounts,controlledCommands,forward:runs['forward-v2'],sentinel:runs['sentinel-v2']},null,2));
