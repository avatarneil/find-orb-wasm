// SPDX-License-Identifier: GPL-2.0-or-later
// Pure protocol and orchestration checks. No compiler, DE440, checkout, SDK,
// engine binary, Python or network is required; real engine runs are explicit CLI jobs.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,rm,writeFile,readFile,readdir} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {gunzipSync} from 'node:zlib';
import {sha} from '../../experiments/short-arcs/methods.mjs';
import {validateCorpus,makePlan,commandFor,evaluateOutput,comparePair,measurement,protocol,elementDifferences,validateCoverage} from '../../experiments/regression-suite/core.mjs';
import {configuration,parseOptions,runSuite,planSummary} from '../../experiments/regression-suite/run.mjs';
import {replaySuite} from '../../experiments/regression-suite/replay.mjs';

const clone=value=>structuredClone(value),start=2461072.5;
function fixture() {
  const daySets=[[0],[0,1,2,7]],arcIds=['one-hour','one-week'];
  const observationDays=[...new Set(daySets.flatMap(days=>days.flatMap(d=>[0,20,40,60].map(m=>d+m/1440))))];
  const days=[...new Set([...observationDays,...daySets.flatMap(d=>[1,3,7].map(x=>d.at(-1)+1/24+x))])].sort((a,b)=>a-b);
  const astrometry=days.map(d=>({jdUtc:start+d,RA:120+d*.1,Dec:10+d*.01,rangeAu:2,elongationDeg:90}));
  const state={positionAu:[2,0,0],velocityAuPerDay:[0,.01,.001]},elements={a:2,q:1,e:.5,i:10,arg_per:30,asc_node:20};
  const epoch=d=>({jdUtc:start+d,jdTt:start+d+69.184/86400,jdTdb:start+d+69.185/86400,state:clone(state),elements:clone(elements)});
  const truthEpochs=[epoch(0),...daySets.map(d=>epoch(d.at(-1)+1/24))];
  const arcs=daySets.map((daysForArc,j)=>({id:arcIds[j],observationIndices:daysForArc.flatMap(d=>[0,20,40,60].map(m=>days.indexOf(d+m/1440))),
    predictionIndices:[1,3,7].map(x=>days.indexOf(daysForArc.at(-1)+1/24+x)),truthEpochIndex:j+1}));
  const c={id:'fixture-body-2026',objectId:'20000001',object:{spkid:'20000001',name:'Fixture body',class:'MBA'},split:'development',observer:'500',astrometry,truthEpochs,arcs,
    applicability:{fit:true,forwardTruth:'strict',reason:'Synthetic control for harness tests.',toleranceArcsec:.1}};
  return {schemaVersion:1,complete:true,cases:[c],suite:{sentinelIds:[c.id]}};
}
function output(command) {
  const rows=command.truth.map((p,i)=>({JD:command.times[i],RA:p.RA,Dec:p.Dec,delta:p.rangeAu??2}));
  const elements={'central body':'Sun',frame:'J2000',q:1,e:.5,a:2,i:10,epoch:command.epochTt,rms_residual:.01,M:30,arg_per:30,asc_node:20};
  return {exitCode:0,stdout:'',files:{'/job/elements.txt':'# Perturbers: 7fe JPL DE-440\n# Sigmas avail: 3\n',
    '/job/sky.json':JSON.stringify({ephemeris:{count:rows.length,entries:Object.fromEntries(rows.map((r,i)=>[i,r]))}}),
    '/job/elements.json':JSON.stringify({objects:{[command.designation]:{observations:{count:command.observationCount,used:command.observationCount},elements}}})}};
}
function mutateJson(result,path,change) {const value=JSON.parse(result.files[path]);change(value);result.files[path]=JSON.stringify(value);return result;}
const settings={noise:'gaussian',seed:7};
test('schema rejects incomplete, malformed and contaminated future-label fixtures',()=>{
  assert.equal(validateCorpus(fixture()).cases.length,1);
  for(const change of [c=>{c.complete=false;},c=>{c.cases[0].astrometry[0].RA=NaN;},c=>{c.cases[0].arcs[0].predictionIndices[0]=1;},
    c=>{c.cases[0].arcs[0].observationIndices[1]=0;},c=>{c.cases[0].truthEpochs[1].jdTt+=1/86400;},
    c=>{c.cases[0].applicability.forwardTruth='unknown';},c=>{c.cases[0].applicability.toleranceArcsec=100;},c=>{c.suite.sentinelIds=['missing'];}]) {
    const bad=fixture();change(bad);assert.throws(()=>validateCorpus(bad));
  }
});
test('sentinel includes preselected short and longer arcs; full has deterministic counts',()=>{
  const c=fixture(),sentinel=makePlan(c,configuration({}));
  assert.deepEqual(sentinel.map(u=>u.arc.id),['one-hour','one-week']);assert.equal(sentinel[0].settings.length,1);
  const full=makePlan(c,configuration({mode:'full',seeds:'0,7'}));
  assert.equal(full.length,2);assert.deepEqual(full[0].settings,[{noise:'exact',seed:0},{noise:'gaussian',seed:0},{noise:'gaussian',seed:7}]);
  assert.equal(planSummary(full,configuration({mode:'full'})).totalCommands,16);
  assert.throws(()=>makePlan(c,configuration({cases:'missing'})));
  assert.throws(()=>makePlan(c,configuration({seeds:'0,NaN'})));
  assert.throws(()=>makePlan(c,configuration({arcs:'one-hour,one-hour'})));
});
test('noise is reproducible, shared across nested arcs, isolated by seed and case',()=>{
  const c=fixture().cases[0],p=measurement(c,0,settings);
  assert.deepEqual(p,measurement(c,0,settings));assert.notDeepEqual(p,measurement(c,0,{...settings,seed:8}));
  assert.notDeepEqual(p,measurement({...c,id:'other-body'},0,settings));
  assert.deepEqual(measurement(c,0,{noise:'exact',seed:77}),c.astrometry[0]);
  const one=commandFor(c,c.arcs[0],'fit',settings),week=commandFor(c,c.arcs[1],'fit',settings);
  assert.deepEqual(one.files['/job/observations.mpc'].trimEnd().split('\n'),week.files['/job/observations.mpc'].trimEnd().split('\n').slice(0,5));
  assert.ok(one.files['/job/observations.mpc'].trimEnd().split('\n').slice(1).every(r=>r.length===80&&r.endsWith('500')));
});
test('commands preserve independent state epoch and arbitrary UTC prediction grid',()=>{
  const c=fixture().cases[0];
  for(const kind of ['forward','fit']) {
    const command=commandFor(c,c.arcs[1],kind,settings);
    assert.equal(command.count,4);assert.equal(command.epochTt,c.truthEpochs[2].jdTt);
    assert.deepEqual(command.times.map(t=>Math.round((t-command.times[0])*24)),[0,24,72,168]);
    assert.match(command.files['/job/job.env'],/EPHEM_STEP_SIZE=ttimes.txt/);
    assert.match(command.files['/job/job.env'],/EPHEMERIS_TIMESCALE=UTC/);assert.ok(command.args.includes('-C500'));
    assert.equal(command.files['/job/times.txt'].trim().split('\n').length,4);
    if(kind==='fit'){assert.ok(command.args.includes('-tEJD'+c.truthEpochs[2].jdTt));assert.ok(!command.args.some(s=>s.startsWith('-v')));}
    else assert.ok(command.args.some(s=>s.startsWith('-vJD'+c.truthEpochs[2].jdTt+',')));
  }
});
test('v2 aligns forecast light deflection with Horizons while disclosing the unchanged fit model',()=>{
  assert.equal(protocol.revision,2);assert.match(protocol.amendment.scope,/Forecast ephemerides only/);
  const c=fixture().cases[0];
  for(const kind of ['forward','fit']) {
    const command=commandFor(c,c.arcs[0],kind);
    assert.equal(command.files['/job/job.env'].split('\n').filter(line=>line==='DISABLE_LIGHT_BENDING=1').length,1);
    assert.match(command.skyFrame,/differential solar light deflection disabled/);
    assert.match(command.lightDeflection.reference,/Horizons quantity 1 omits/);
    assert.match(command.lightDeflection.forecast,/ephemerides only/);
    if(kind==='fit') {
      assert.match(command.lightDeflection.fitting,/remains enabled/);
      assert.match(command.lightDeflection.fitting,/report-only/);
      assert.match(command.lightDeflection.fitting,/not pure synthetic CCD astrometry/);
    } else assert.equal(command.lightDeflection.fitting,null);
  }
});
test('output validation fails missing/nonfinite/count/force/time/element corruption',()=>{
  const c=fixture().cases[0],command=commandFor(c,c.arcs[0],'fit');assert.equal(evaluateOutput(command,output(command)).valid,true);
  const changes=[r=>{r.exitCode=1;},r=>{r.files['/job/elements.txt']='# Perturbers: 400 JPL DE-440\n';},
    r=>mutateJson(r,'/job/sky.json',d=>d.ephemeris.count--),r=>mutateJson(r,'/job/sky.json',d=>d.ephemeris.entries[0].RA=null),
    r=>mutateJson(r,'/job/sky.json',d=>d.ephemeris.entries[0].JD+=.000001),r=>mutateJson(r,'/job/sky.json',d=>d.ephemeris.entries[0].delta=0),
    r=>mutateJson(r,'/job/elements.json',d=>d.objects.REG0001.observations.used--),r=>mutateJson(r,'/job/elements.json',d=>d.objects.REG0001.elements.epoch+=.1),
    r=>mutateJson(r,'/job/elements.json',d=>d.objects.REG0001.elements.M=null),r=>mutateJson(r,'/job/elements.json',d=>d.objects.REG0001.elements.a='NaN'),
    r=>mutateJson(r,'/job/elements.json',d=>d.objects.REG0001.elements['central body']='Earth')];
  for(const change of changes){const r=output(command);change(r);assert.throws(()=>evaluateOutput(command,r));}
});
test('parabolic semimajor-axis absence is explicit; primary finite invariants still required',()=>{
  const c=fixture().cases[0],command=commandFor(c,c.arcs[0],'fit'),r=output(command);
  mutateJson(r,'/job/elements.json',d=>{d.objects.REG0001.elements.e=1;delete d.objects.REG0001.elements.a;});
  const summary=evaluateOutput(command,r);assert.equal(summary.elements.inverseA,0);assert.equal(summary.elements.semimajorAxisStatus,'absent-at-parabolic-boundary');
  assert.equal(summary.elements.a,null);assert.ok(Number.isFinite(summary.truthElementErrors.e));
  mutateJson(r,'/job/elements.json',d=>{d.objects.REG0001.elements.e=.999;});assert.throws(()=>evaluateOutput(command,r));
});
test('parity compares actual directions, including equal opposing errors around truth',()=>{
  const c=fixture().cases[0],command=commandFor(c,c.arcs[0],'fit'),b=evaluateOutput(command,output(command)),candidate=clone(b);
  for(let i=0;i<b.predictions.length;i++){b.predictions[i].RA-=1/3600;candidate.predictions[i].RA+=1/3600;b.predictions[i].errorArcsec=candidate.predictions[i].errorArcsec=1;}
  const result=comparePair(b,candidate,{kind:'fit',applicability:c.applicability});
  assert.equal(result.pass,false);assert.ok(result.maxDirectionDifferenceArcsec>1.9);assert.equal(result.rows[0].errorChangeArcsec,0);
});
test('fit report mode does not suppress structural, forward parity or strict source-floor gates',()=>{
  const c=fixture().cases[0],command=commandFor(c,c.arcs[0],'fit'),b=evaluateOutput(command,output(command)),candidate=clone(b);
  candidate.predictions[1].RA+=.01;candidate.predictions[1].errorArcsec=36;candidate.elements.e+=.01;
  const report=comparePair(b,candidate,{kind:'fit',applicability:c.applicability,fitGate:'report'});
  assert.equal(report.pass,true);assert.equal(report.parity,false);assert.equal(report.rows[1].degraded,true);assert.equal(report.elementParity,false);
  assert.equal(comparePair(b,{valid:false},{kind:'fit',applicability:c.applicability,fitGate:'report'}).pass,false);
  assert.equal(comparePair(b,candidate,{kind:'forward',applicability:c.applicability,fitGate:'report'}).pass,false);
  const same=clone(b);same.predictions[0].errorArcsec=.2;
  assert.equal(comparePair(same,same,{kind:'forward',applicability:c.applicability,fitGate:'report'}).pass,false);
  const modelLimited={...c.applicability,forwardTruth:'model-limited',toleranceArcsec:null};
  const limited=comparePair(same,same,{kind:'forward',applicability:modelLimited});assert.equal(limited.pass,true);assert.equal(limited.reference.enforced,false);
});
test('primary-element parity and wrapped orientation differences are distinct from truth recovery',()=>{
  const c=fixture().cases[0],command=commandFor(c,c.arcs[0],'fit'),b=evaluateOutput(command,output(command)),candidate=clone(b);
  candidate.elements.q+=.00001;assert.equal(comparePair(b,candidate,{kind:'fit',applicability:c.applicability}).elementParity,false);
  const delta=elementDifferences({...b.elements,arg_per:359.99},{...b.elements,arg_per:.01});assert.ok(Math.abs(delta.arg_per-.02)<1e-10);
  assert.ok(b.truthElementErrors&&b.truthStateElementErrorsWithFindOrbGM);
});
test('coverage checks input observations, state epochs and prediction epochs',()=>{
  const c=fixture().cases[0],command=commandFor(c,c.arcs[1],'fit');
  assert.ok(validateCoverage(command,{startExclusiveJd:start-1,endInclusiveJd:start+20}));
  assert.throws(()=>validateCoverage(command,{startExclusiveJd:start+1,endInclusiveJd:start+20}));
  assert.throws(()=>validateCoverage(command,{startExclusiveJd:start-1,endInclusiveJd:start+10}));
});
test('CLI rejects ambiguous/unknown controls and keeps full planning separate from execution',()=>{
  assert.equal(configuration(parseOptions(['--mode','full']))['dry-run'],true);
  assert.equal(configuration(parseOptions(['--mode','full','--execute']))['dry-run'],false);
  assert.throws(()=>parseOptions(['--budget']));assert.throws(()=>parseOptions(['--bogus','1']));
  assert.throws(()=>parseOptions(['--mode','full','--mode','sentinel']));assert.throws(()=>configuration({'dry-run':true,execute:true}));
  assert.throws(()=>configuration({'baseline-kind':'native-original'}));assert.throws(()=>configuration({budget:'1e999'}));
  assert.throws(()=>configuration({checks:'unknown'}));
});
test('selected check planning counts actual forward, fit and optional original jobs',()=>{
  const corpus=fixture(),units=makePlan(corpus,configuration({mode:'full'}));
  const forward=planSummary(units,configuration({checks:'forward','original-native-dir':'unused'}));
  assert.equal(forward.forwardPairs,2);assert.equal(forward.fitPairs,0);assert.equal(forward.totalCommands,4);assert.equal(forward.originalTimeCappedDiagnostics,0);
  const fit=planSummary(units,configuration({checks:'fit','original-native-dir':'diagnostic'}));
  assert.equal(fit.forwardPairs,0);assert.equal(fit.fitPairs,4);assert.equal(fit.totalCommands,12);assert.equal(fit.originalTimeCappedDiagnostics,4);
});
async function workspace(t) {
  const dir=await mkdtemp(join(tmpdir(),'orb-regression-test-'));t.after(()=>rm(dir,{recursive:true,force:true}));
  const corpus=join(dir,'corpus.json');await writeFile(corpus,JSON.stringify(fixture()));return {dir,corpus};
}
test('colliding display names retain distinct SPK IDs through counts, grouping and replay',async t=>{
  const {dir,corpus}=await workspace(t),data=fixture(),second=clone(data.cases[0]),anotherGeometry=clone(data.cases[0]);
  second.id='another-object';second.objectId=second.object.spkid='20000002';anotherGeometry.id='same-object-another-geometry';
  data.cases.push(second,anotherGeometry);await writeFile(corpus,JSON.stringify(data));
  const config=configuration({mode:'full',arcs:'one-hour',noise:'exact'}),plan=planSummary(makePlan(data,config),config);
  assert.equal(plan.caseCount,3);assert.equal(plan.objectCount,2);
  const validation=await runSuite({corpus,'validate-corpus':true});assert.equal(validation.validation.objects,2);
  const outputPath=join(dir,'colliding-names'),deps={loadEngine:async()=>({execute:async command=>output(command)}),
    provenance:async()=>({manifestSHA256:'a'.repeat(64),coverage:{startExclusiveJd:start-1,endInclusiveJd:start+50}}),log:()=>{}};
  const run=await runSuite({corpus,output:outputPath,mode:'full',execute:true,arcs:'one-hour',noise:'exact'},deps);
  assert.equal(new Set(run.results.map(row=>row.objectId)).size,2);assert.equal(new Set(run.results.map(row=>row.object)).size,1);
  for(const group of run.summary.groups) {
    assert.deepEqual(group.objects,['20000001','20000002']);
    assert.deepEqual(group.objectLabels,{'20000001':'Fixture body','20000002':'Fixture body'});
  }
  const replay=await replaySuite({directory:outputPath,corpus});assert.equal(replay.verified,true);assert.equal(replay.scientificPass,true);
  delete data.cases[0].objectId;assert.equal(validateCorpus(data).cases.length,3,'SPK-ID alias alone is accepted');
  data.cases[0].objectId='20000099';assert.throws(()=>validateCorpus(data),/Object ID aliases agree/);
});
test('dry-run and whole-corpus validation require no engine loads or output directory',async t=>{
  const {corpus}=await workspace(t),dependencies={loadEngine:()=>{throw new Error('must not load');}};
  const plan=await runSuite({corpus,mode:'full'},dependencies);assert.equal(plan.dryRun,true);assert.equal(plan.plan.totalCommands,12);
  const valid=await runSuite({corpus,'validate-corpus':true},dependencies);assert.equal(valid.validation.valid,true);
});
test('complete fake paired run archives replayable bytes and refuses evidence overwrite',async t=>{
  const {dir,corpus}=await workspace(t),out=join(dir,'nested','evidence');let calls=0;
  const dependencies={loadEngine:async()=>({execute:async command=>{calls++;return output(command);}}),
    provenance:async()=>({manifestSHA256:'a'.repeat(64),coverage:{startExclusiveJd:start-1,endInclusiveJd:start+50}}),log:()=>{}};
  const run=await runSuite({corpus,output:out},dependencies);
  assert.equal(run.summary.pass,true);assert.equal(run.summary.pairs,4);assert.equal(calls,8);assert.equal(run.manifest.rawFiles,8);
  for(const row of run.results)for(const role of ['baseline','candidate']) {
    const evidence=row[role].evidence,bytes=await readFile(join(out,evidence.rawFile)),decoded=gunzipSync(bytes);
    assert.equal(sha(bytes),evidence.gzipSHA256);assert.equal(sha(decoded),evidence.rawSHA256);
    assert.equal(sha(JSON.stringify(JSON.parse(decoded).command)),evidence.commandSHA256);
  }
  assert.equal(sha(await readFile(join(out,'results.json'))),run.manifest.resultsSHA256);
  assert.equal((await readdir(join(out,'raw'))).length,8);
  await assert.rejects(()=>runSuite({corpus,output:out},dependencies),/EEXIST/);
});
test('execution failures remain paired evidence and fail the suite rather than disappear',async t=>{
  const {dir,corpus}=await workspace(t);let loads=0;
  const dependencies={loadEngine:async()=>{const candidate=++loads===2;return {execute:async command=>{if(candidate)throw new Error('fake failure');return output(command);}};},
    provenance:async()=>({manifestSHA256:'b'.repeat(64),coverage:{startExclusiveJd:start-1,endInclusiveJd:start+50}}),log:()=>{}};
  const run=await runSuite({corpus,output:join(dir,'fail')},dependencies);
  assert.equal(run.summary.pass,false);assert.equal(run.summary.failedPairs,4);assert.equal(run.summary.complete,true);
  assert.match(run.results[0].candidate.error,/fake failure/);assert.equal(run.manifest.status,'failed');
});
test('explicit baseline lock mismatch fails before any solver execution',async t=>{
  const {dir,corpus}=await workspace(t);let calls=0;
  const deps={loadEngine:async()=>({execute:async()=>{calls++;}}),provenance:async()=>({manifestSHA256:'a'.repeat(64)})};
  await assert.rejects(()=>runSuite({corpus,output:join(dir,'lock'),'baseline-sha256':'b'.repeat(64)},deps),/immutable baseline/);
  assert.equal(calls,0);assert.equal(JSON.parse(await readFile(join(dir,'lock','manifest.json'))).status,'failed-before-execution');
});
test('forward-only and fit-only execution expose omitted checks rather than claim full validation',async t=>{
  const {dir,corpus}=await workspace(t);
  for(const checks of ['forward','fit']) {
    const kinds=[],deps={loadEngine:async()=>({execute:async command=>{kinds.push(command.kind);return output(command);}}),
      provenance:async()=>({manifestSHA256:'a'.repeat(64),coverage:{startExclusiveJd:start-1,endInclusiveJd:start+50}}),log:()=>{}};
    const run=await runSuite({corpus,checks,output:join(dir,checks)},deps);
    assert.equal(run.summary.pass,true);assert.deepEqual(kinds,Array(4).fill(checks));
    assert.equal(run.summary.validationScope.fullSelectedProtocolPassed,false);assert.equal(run.manifest.plan.totalCommands,4);
  }
});
