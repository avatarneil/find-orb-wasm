// SPDX-License-Identifier: GPL-2.0-or-later
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,rm,writeFile,readFile,unlink,copyFile} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {gzipSync,gunzipSync} from 'node:zlib';
import {sha} from '../../experiments/short-arcs/methods.mjs';
import {runSuite} from '../../experiments/regression-suite/run.mjs';
import {replaySuite} from '../../experiments/regression-suite/replay.mjs';
const start=2461072.5;
function fixture() {
  const times=[0,20/1440,40/1440,60/1440,1+1/24,3+1/24,7+1/24];
  const c={id:'replay-fixture',objectId:'20000001',object:{spkid:'20000001',name:'Replay fixture',class:'MBA'},split:'development',observer:'500',
    applicability:{fit:true,forwardTruth:'strict',reason:'Independent harness test fixture.',toleranceArcsec:.1},
    astrometry:times.map(d=>({jdUtc:start+d,RA:120+.1*d,Dec:10+.01*d,rangeAu:2})),
    truthEpochs:[{jdUtc:start+1/24,jdTt:start+1/24+69.184/86400,jdTdb:start+1/24+69.185/86400,
      state:{positionAu:[2,0,0],velocityAuPerDay:[0,.01,.001]},elements:{q:1,e:.5,i:10,a:2}}],
    arcs:[{id:'one-hour',observationIndices:[0,1,2,3],predictionIndices:[4,5,6],truthEpochIndex:0}]};
  return {complete:true,cases:[c],suite:{sentinelIds:[c.id]}};
}
function output(command) {
  const entries=Object.fromEntries(command.truth.map((p,i)=>[i,{JD:command.times[i],RA:p.RA,Dec:p.Dec,delta:2}]));
  return {exitCode:0,stdout:'',files:{'/job/elements.txt':'# Perturbers: 7fe JPL DE-440\n# Sigmas avail: 3\n',
    '/job/sky.json':JSON.stringify({ephemeris:{count:4,entries}}),
    '/job/elements.json':JSON.stringify({objects:{REG0001:{observations:{count:4,used:4},elements:{'central body':'Sun',frame:'J2000',
      q:1,e:.5,i:10,a:2,epoch:command.epochTt,rms_residual:.01}}}})}};
}
async function createArchive(t,{failure,original=false}={}) {
  const dir=await mkdtemp(join(tmpdir(),'orb-replay-test-'));t.after(()=>rm(dir,{recursive:true,force:true}));
  const corpus=join(dir,'corpus.json'),directory=join(dir,'archive');await writeFile(corpus,JSON.stringify(fixture()));
  let loads=0;
  const dependencies={loadEngine:async()=>{const candidate=++loads===2;return {execute:async command=>{
    if(candidate&&failure==='execution')throw new Error('Recorded process failed\nplatform-specific stack');
    const result=output(command);if(candidate&&failure==='validation')result.files['/job/sky.json']='{"ephemeris":{"count":0,"entries":{}}}';return result;
  }};},provenance:async()=>({manifestSHA256:'a'.repeat(64),coverage:{startExclusiveJd:failure==='construction'?start+1:start-1,endInclusiveJd:start+20}}),
  loadOriginal:async()=>({execute:async()=>{throw new Error('Original CPU-cap comparator unavailable');}}),log:()=>{}};
  const run=await runSuite({corpus,output:directory,arcs:'one-hour',...(original?{'original-native-dir':'original-diagnostic'}:{})},dependencies);
  return {dir,corpus,directory,run};
}
async function updateIndex(directory,change) {
  const resultPath=join(directory,'results.json'),summaryPath=join(directory,'summary.json'),manifestPath=join(directory,'manifest.json');
  const results=JSON.parse(await readFile(resultPath)),summary=JSON.parse(await readFile(summaryPath)),manifest=JSON.parse(await readFile(manifestPath));
  await change({results,summary,manifest});
  const resultsText=JSON.stringify(results,null,2)+'\n',summaryText=JSON.stringify(summary,null,2)+'\n';
  await writeFile(resultPath,resultsText);await writeFile(summaryPath,summaryText);
  manifest.resultsSHA256=sha(resultsText);manifest.summarySHA256=sha(summaryText);await writeFile(manifestPath,JSON.stringify(manifest,null,2)+'\n');
}
async function updateRaw(directory,row,role,change) {
  const evidence=row[role].evidence,path=join(directory,evidence.rawFile),raw=JSON.parse(gunzipSync(await readFile(path)));
  change(raw);const decoded=Buffer.from(JSON.stringify(raw)),bytes=gzipSync(decoded);
  await writeFile(path,bytes);Object.assign(evidence,{gzipSHA256:sha(bytes),rawSHA256:sha(decoded),commandSHA256:sha(JSON.stringify(raw.command))});
}
test('offline replay verifies complete archive and recomputes every scientific result',async t=>{
  const {directory,corpus,run}=await createArchive(t),manifestSHA256=sha(await readFile(join(directory,'manifest.json')));
  const replay=await replaySuite({directory,corpus,manifestSHA256});
  assert.equal(replay.verified,true);assert.equal(replay.scientificPass,true);assert.equal(replay.pairs,2);assert.equal(replay.rawFiles,4);
  assert.deepEqual(replay.summary,JSON.parse(JSON.stringify(run.summary)));assert.match(replay.archiveAuthenticity,/Externally/);
});
test('recorded execution and validation failures remain failures after replay',async t=>{
  for(const failure of ['execution','validation']) {
    const {directory,corpus}=await createArchive(t,{failure}),replay=await replaySuite({directory,corpus});
    assert.equal(replay.verified,true);assert.equal(replay.scientificPass,false);assert.equal(replay.summary.failedPairs,2);
    assert.equal(replay[failure==='execution'?'executionFailuresRetained':'validationFailuresRecomputed'],2);
  }
});
test('command-construction/coverage failures are recomputed without invented raw outputs',async t=>{
  const {directory,corpus}=await createArchive(t,{failure:'construction'}),replay=await replaySuite({directory,corpus});
  assert.equal(replay.verified,true);assert.equal(replay.scientificPass,false);assert.equal(replay.constructionFailuresRecomputed,2);assert.equal(replay.rawFiles,0);
});
test('optional original time-cap diagnostic failures are retained outside scientific pass',async t=>{
  const {directory,corpus}=await createArchive(t,{original:true}),replay=await replaySuite({directory,corpus});
  assert.equal(replay.scientificPass,true);assert.equal(replay.rawFiles,5);assert.equal(replay.executionFailuresRetained,1);
});
test('missing or corrupt raw output is rejected',async t=>{
  for(const corrupt of [false,true]) {
    const {directory,corpus,run}=await createArchive(t),path=join(directory,run.results[0].baseline.evidence.rawFile);
    if(corrupt){const bytes=await readFile(path);bytes[bytes.length-1]^=1;await writeFile(path,bytes);}else await unlink(path);
    await assert.rejects(()=>replaySuite({directory,corpus}),corrupt?/Compressed raw.*checksum/:/ENOENT/);
  }
});
test('raw command alteration is rejected even after its checksum chain is updated',async t=>{
  const {directory,corpus}=await createArchive(t);
  await updateIndex(directory,async({results})=>{
    await updateRaw(directory,results[0],'baseline',raw=>{raw.command.args.push('-j');});
  });
  await assert.rejects(()=>replaySuite({directory,corpus}),/Independently regenerated command.*checksum/);
});
test('invented metrics are rejected by recomputation even with matching saved/index hashes',async t=>{
  const {directory,corpus}=await createArchive(t);
  await updateIndex(directory,async({results})=>{
    await updateRaw(directory,results[0],'candidate',raw=>{raw.summary.predictions[1].errorArcsec=123;});
    results[0].candidate.predictions[1].errorArcsec=123;
  });
  await assert.rejects(()=>replaySuite({directory,corpus}),/Raw scientific validation independently recomputed/);
});
test('removing a failed pair cannot produce a complete archive',async t=>{
  const {directory,corpus}=await createArchive(t,{failure:'validation'});
  await updateIndex(directory,({results,summary,manifest})=>{results.pop();summary.failedPairs=1;manifest.completedPairs=1;});
  await assert.rejects(()=>replaySuite({directory,corpus}),/Every planned pair retained/);
});
test('changing a pair identity, orphaning output or changing declared pass status fails',async t=>{
  for(const mutation of ['identity','orphan','status']) {
    const {directory,corpus,run}=await createArchive(t);
    if(mutation==='orphan')await copyFile(join(directory,run.results[0].baseline.evidence.rawFile),join(directory,'raw','extra.json.gz'));
    else await updateIndex(directory,({results,manifest})=>{if(mutation==='identity')results[0].settings.seed=99;else manifest.status='failed';});
    await assert.rejects(()=>replaySuite({directory,corpus}),mutation==='identity'?/identity matches declared plan/:mutation==='orphan'?/raw inventory/:/pass\/fail status/);
  }
});
test('strict source, corpus, index, summary and external manifest hashes are enforced',async t=>{
  for(const target of ['source','corpus','results','summary','manifest']) {
    const {directory,corpus}=await createArchive(t);
    if(target==='source')await updateIndex(directory,({manifest})=>{manifest.files['experiments/regression-suite/core.mjs']='0'.repeat(64);});
    else if(target==='corpus')await writeFile(corpus,(await readFile(corpus))+'\n');
    else if(target==='results'||target==='summary'){const path=join(directory,target+'.json');await writeFile(path,(await readFile(path))+'\n');}
    await assert.rejects(()=>replaySuite({directory,corpus,...(target==='manifest'?{manifestSHA256:'0'.repeat(64)}:{})}),/checksum/);
  }
});
test('execution stack differences are normalized but failure category and message survive',async t=>{
  const {directory,corpus}=await createArchive(t,{failure:'execution'});
  await updateIndex(directory,async({results})=>{
    for(const row of results) {
      await updateRaw(directory,row,'candidate',raw=>{raw.summary.error='Error: Recorded process failed\nnew stack location';});
      row.candidate.error='Error: Recorded process failed\nother stack location';
    }
  });
  const replay=await replaySuite({directory,corpus});assert.equal(replay.executionFailuresRetained,2);assert.equal(replay.scientificPass,false);
  await updateIndex(directory,({results})=>{results[0].candidate.error='Error: Different failure';});
  await assert.rejects(()=>replaySuite({directory,corpus}),/Indexed engine summary/);
});
