// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {stateCommand} from '../../benchmark/cases.mjs';
import {EPHEMERIS} from '../../build/pins.mjs';
import {angularOffset,mpcRecord,normalGenerator,quantile,separationArcsec,stateElements} from '../short-arcs/methods.mjs';
export const protocol=JSON.parse(readFileSync(new URL('./protocol.json',import.meta.url),'utf8'));
const finite=(value,label)=>assert.ok(typeof value==='number'&&Number.isFinite(value),'Finite '+label);
const identifier=(value,label)=>assert.match(value,/^[A-Za-z0-9][A-Za-z0-9._-]*$/,'Safe '+label);
export function objectId(c) {
  const id=c.objectId??c.object?.spkid;
  assert.ok(typeof id==='string'&&/^[1-9]\d*$/.test(id),'Immutable decimal SPK object ID');
  if(c.objectId!==undefined&&c.object?.spkid!==undefined)assert.equal(c.objectId,c.object.spkid,'Object ID aliases agree');
  return id;
}
export function validatePoint(point) {
  for(const key of ['jdUtc','RA','Dec'])finite(point?.[key],key);
  assert.ok(point.RA>=0&&point.RA<360&&Math.abs(point.Dec)<=90,'RA/Dec in degrees');
}
export function stateArray(state) {
  const values=[...(state?.positionAu??[]),...(state?.velocityAuPerDay??[])];
  assert.equal(values.length,6,'Six Cartesian state coordinates');
  values.forEach((v,i)=>finite(v,'state '+i));assert.ok(Math.hypot(...values.slice(0,3))>0,'Nonzero heliocentric position');
  return values;
}
export function validateCorpus(corpus) {
  assert.equal(corpus.complete,true,'Completed corpus acquisition required; partial corpora cannot pass');
  assert.ok(Array.isArray(corpus.cases)&&corpus.cases.length,'Nonempty corpus');
  const ids=new Set();
  for(const c of corpus.cases) {
    identifier(c.id,'case ID');assert.ok(!ids.has(c.id),'Unique case ID');ids.add(c.id);
    assert.equal(c.observer,'500','Regression corpus uses geocentric reception astrometry');
    objectId(c);
    assert.ok(typeof c.object?.name==='string'&&c.object.name,'Object display name');
    assert.ok(typeof c.object.class==='string'&&c.object.class,'Object class');
    assert.ok(c.applicability?.fit===true,'Unsupported fit must not be silently skipped');
    assert.ok(['strict','model-limited'].includes(c.applicability.forwardTruth),'Explicit physical-model applicability');
    assert.ok(typeof c.applicability.reason==='string'&&c.applicability.reason,'Applicability reason');
    if(c.applicability.forwardTruth==='strict')assert.equal(c.applicability.toleranceArcsec,protocol.gates.strictForwardTruthArcsec,'Frozen strict reference tolerance');
    else assert.equal(c.applicability.toleranceArcsec,null,'Model-limited reference has no invented absolute tolerance');
    assert.ok(Array.isArray(c.astrometry)&&c.astrometry.length,'Astrometry bank');
    c.astrometry.forEach((p,i)=>{validatePoint(p);if(i)assert.ok(p.jdUtc>c.astrometry[i-1].jdUtc,'Sorted unique astrometry epochs');});
    assert.ok(Array.isArray(c.truthEpochs)&&c.truthEpochs.length,'Independent truth states');
    for(const t of c.truthEpochs) {
      for(const key of ['jdUtc','jdTt','jdTdb'])finite(t[key],key);stateArray(t.state);
      assert.ok(Math.abs(t.jdTt-t.jdTdb)<.01/86400,'TT and TDB epochs refer to same physical instant');
      assert.ok(Math.abs(t.jdTt-t.jdUtc-69.184/86400)<1e-9,'Pinned TT minus UTC convention');
      for(const key of ['q','e','i'])finite(t.elements?.[key],'truth element '+key);
      assert.ok(t.elements.q>0&&t.elements.e>=0&&t.elements.i>=0&&t.elements.i<=180,'Physical truth elements');
    }
    const arcs=new Set();assert.ok(Array.isArray(c.arcs)&&c.arcs.length,'Arc definitions');
    for(const arc of c.arcs) {
      identifier(arc.id,'arc ID');assert.ok(!arcs.has(arc.id),'Unique arc ID');arcs.add(arc.id);
      for(const key of ['observationIndices','predictionIndices']) {
        assert.ok(Array.isArray(arc[key])&&arc[key].length>=(key==='observationIndices'?4:1),'Nonempty '+key);
        arc[key].forEach((v,i)=>assert.ok(Number.isInteger(v)&&v>=0&&v<c.astrometry.length&&(!i||v>arc[key][i-1]),'Sorted valid '+key));
      }
      assert.ok(Number.isInteger(arc.truthEpochIndex)&&c.truthEpochs[arc.truthEpochIndex],'Valid truth epoch index');
      const last=c.astrometry[arc.observationIndices.at(-1)].jdUtc,t=c.truthEpochs[arc.truthEpochIndex];
      assert.ok(Math.abs(t.jdUtc-last)<protocol.gates.epochToleranceDays,'State at last exposure');
      assert.equal(arc.predictionIndices.length,3,'Three prediction horizons');
      arc.predictionIndices.forEach((index,i)=>assert.ok(Math.abs(c.astrometry[index].jdUtc-last-[1,3,7][i])<protocol.gates.epochToleranceDays,'Independent +1/+3/+7-day future predictions'));
    }
  }
  const sentinel=corpus.suite?.sentinelIds;
  assert.ok(Array.isArray(sentinel)&&sentinel.length&&new Set(sentinel).size===sentinel.length,'Frozen unique sentinel IDs');
  sentinel.forEach(id=>assert.ok(ids.has(id),'Sentinel exists in corpus'));
  return corpus;
}
export function makePlan(corpus,config) {
  validateCorpus(corpus);assert.ok(['sentinel','full'].includes(config.mode),'Known mode');
  const selected=config.cases?config.cases.split(','):(config.mode==='sentinel'?corpus.suite.sentinelIds:corpus.cases.map(c=>c.id));
  assert.equal(new Set(selected).size,selected.length,'Unique selected cases');
  const noises=(config.noise??(config.mode==='sentinel'?'exact':'exact,gaussian')).split(',');
  assert.ok(noises.length&&new Set(noises).size===noises.length&&noises.every(n=>['exact','gaussian'].includes(n)),'Known unique noise scenarios');
  const seeds=(config.seeds??'0').split(',').map(s=>{assert.match(s,/^\d+$/,'Integer noise seed');return Number(s);});
  assert.ok(seeds.length&&new Set(seeds).size===seeds.length&&seeds.every(Number.isSafeInteger),'Unique safe seeds');
  const units=[];
  for(const id of selected) {
    const c=corpus.cases.find(c=>c.id===id);assert.ok(c,'Selected case exists: '+id);
    let arcs=config.arcs?.split(',');
    if(!arcs||config.arcs==='all')arcs=(config.arcs==='all'||config.mode==='full')?c.arcs.map(a=>a.id):['one-hour',...(id===corpus.suite.sentinelIds[0]?['one-week']:[])];
    assert.equal(new Set(arcs).size,arcs.length,'Unique selected arcs');
    for(const id of arcs) {
      const arc=c.arcs.find(a=>a.id===id);assert.ok(arc,'Selected arc exists: '+id);
      units.push({c,arc,settings:noises.flatMap(noise=>(noise==='exact'?[0]:seeds).map(seed=>({noise,seed})))});
    }
  }
  assert.ok(units.length,'Nonempty run plan');return units;
}
// Seed each bank entry independently, so reordering cases or selecting a subset
// never changes the measurement used by any nested arc or paired engine.
export function measurement(c,index,{noise,seed}) {
  const point=c.astrometry[index];if(noise==='exact')return {...point};
  assert.equal(noise,'gaussian');const gaussian=normalGenerator('regression-v1:'+c.id+':'+index+':'+seed);
  return angularOffset(point,protocol.observationSigmaArcsec*gaussian(),protocol.observationSigmaArcsec*gaussian());
}
function timeGrid(command,truth) {
  const env=command.files['/job/job.env'].split('\n').filter(line=>!/^EPHEM_(START|STEPS|STEP_SIZE)=/.test(line));
  // Upstream limits the step-size string to 80 bytes. Both verified loaders set
  // cwd to the private job directory; keep this filename relative so macOS's
  // long temporary paths cannot overflow the native parser.
  command.files['/job/job.env']=[...env,'EPHEM_START=JD'+truth[0].jdUtc,'EPHEM_STEPS='+truth.length,'EPHEM_STEP_SIZE=ttimes.txt'].join('\n')+'\n';
  command.files['/job/times.txt']=truth.map(p=>'JD'+p.jdUtc.toFixed(12)).join('\n')+'\n';
  return {...command,count:truth.length,times:truth.map(p=>p.jdUtc),truth};
}
export function commandFor(c,arc,kind,settings={noise:'exact',seed:0},budget=100) {
  assert.ok(['forward','fit'].includes(kind),'Known command kind');
  assert.ok(Number.isInteger(budget)&&budget>=11&&budget<=10000,'Ranging batch capacity');
  const epoch=c.truthEpochs[arc.truthEpochIndex];
  const truth=[c.astrometry[arc.observationIndices.at(-1)],...arc.predictionIndices.map(i=>c.astrometry[i])];
  let command=stateCommand(stateArray(epoch.state),{epoch:epoch.jdTt,start:truth[0].jdUtc,count:truth.length,step:'1d',scale:'UTC',sky:true});
  command.args=command.args.map(s=>s==='-CF52'?'-C'+c.observer:s);
  if(kind==='fit') {
    command.args=['/job/observations.mpc',...command.args.filter(s=>!s.startsWith('-o')&&!s.startsWith('-v')),'-tEJD'+epoch.jdTt];
    command.files['/job/observations.mpc']='COM Posn sigma '+protocol.observationSigmaArcsec+'\n'+arc.observationIndices.map(i=>mpcRecord(measurement(c,i,settings),'REG0001',c.observer)).join('\n')+'\n';
    command.files['/job/job.env']+=['MAX_SR_ORBITS='+budget,'SETTINGS=N,4,12,0,2,1','SETTINGS2=1,99,0,0,0','IOD_TIMEOUT=0','SIGMA_MULTIPLIER=1'].join('\n')+'\n';
    command.outputs.push('/job/elements.json');
  }
  return {...timeGrid(command,truth),kind,designation:'REG0001',epochTt:epoch.jdTt,observationCount:arc.observationIndices.length,
    inputTimesUtc:arc.observationIndices.map(i=>c.astrometry[i].jdUtc),
    truthElements:epoch.elements,truthStateElementsWithFindOrbGM:stateElements(stateArray(epoch.state)),
    stateFrame:'heliocentric geometric IAU76/J2000 ecliptic AU and AU/day at TT',skyFrame:'ICRF geocentric light-time-only astrometric degrees, UTC reception',
    ephemeris:EPHEMERIS.name};
}
export function evaluateOutput(command,result) {
  assert.equal(result?.exitCode,0,'Successful engine exit');
  const text=result.files?.['/job/elements.txt'];assert.equal(typeof text,'string','Elements output exists');
  const force=/^# Perturbers:\s+([0-9a-f]+).*JPL DE-440.*$/im.exec(text);
  assert.ok(force&&(parseInt(force[1],16)&0x7fe)===0x7fe,'Full planetary force model and DE440');
  assert.ok(!/fallback|failed to open.*(?:\.440|ephemeris)/i.test(result.stdout??''),'No reported ephemeris fallback');
  const ephemeris=JSON.parse(result.files['/job/sky.json']).ephemeris;
  assert.ok(ephemeris&&typeof ephemeris.entries==='object'&&ephemeris.entries!==null&&!Array.isArray(ephemeris.entries),'Sky entries object');
  assert.ok(Number.isInteger(ephemeris.count),'Integer sky count');
  const sky=Object.values(ephemeris.entries).sort((a,b)=>a.JD-b.JD);
  assert.equal(ephemeris.count,sky.length,'Reported sky count');assert.equal(sky.length,command.times.length,'Requested sky count');
  const predictions=sky.map((row,i)=>{
    for(const key of ['JD','RA','Dec','delta'])finite(row[key],'sky '+key);
    assert.ok(row.RA>=0&&row.RA<360&&Math.abs(row.Dec)<=90&&row.delta>0,'Physical sky coordinates/range');
    assert.ok(Math.abs(row.JD-command.times[i])<protocol.gates.epochToleranceDays,'Requested UTC reception time grid');
    const errorArcsec=separationArcsec(row,command.truth[i]);finite(errorArcsec,'angular error');
    return {jdUtc:row.JD,RA:row.RA,Dec:row.Dec,rangeAu:row.delta,errorArcsec};
  });
  const summary={valid:true,predictions,forceMask:force[1],uncertaintyMethod:Number(/^# Sigmas avail: (\d+)/m.exec(text)?.[1]??0),phases:result.phases??null};
  if(command.kind==='fit') {
    const fit=JSON.parse(result.files['/job/elements.json']).objects?.[command.designation];assert.ok(fit,'Requested fitted object');
    assert.equal(fit.observations?.count,command.observationCount,'All input observations parsed');
    assert.ok(Number.isInteger(fit.observations.used)&&fit.observations.used>=3&&fit.observations.used<=fit.observations.count,'Valid observation-use count');
    if(protocol.gates.requireAllInputObservationsUsed)assert.equal(fit.observations.used,command.observationCount,'No silently excluded input observations');
    const elements=fit.elements;for(const key of ['q','e','i','epoch','rms_residual'])finite(elements?.[key],'element '+key);
    assert.equal(elements['central body'],'Sun','Heliocentric fitted elements');assert.equal(elements.frame,'J2000','J2000 fitted element frame');
    for(const key of ['a','M','n','arg_per','asc_node','Tp','P','Q','weighted_rms_residual'])
      if(Object.hasOwn(elements,key))finite(elements[key],'emitted element '+key);
    if(elements.e!==1)finite(elements.a,'nonparabolic semimajor axis');
    assert.ok(elements.q>=0&&elements.e>=0&&elements.i>=0&&elements.i<=180&&elements.rms_residual>=0,'Physical finite elements');
    assert.ok(Math.abs(elements.epoch-command.epochTt)<protocol.gates.epochToleranceDays,'Matched fit TT epoch');
    // Semimajor axis may legitimately be absent/infinite at e=1. Require finite
    // inverse-a derived from q/e, without falsely demanding a unique true orbit.
    assert.ok(elements.q>0,'Positive perihelion');const inverseA=(1-elements.e)/elements.q;finite(inverseA,'inverse semimajor axis');
    summary.observations={count:fit.observations.count,used:fit.observations.used};
    summary.elements={q:elements.q,e:elements.e,i:elements.i,epoch:elements.epoch,rmsArcsec:elements.rms_residual,inverseA,
      a:elements.a??null,semimajorAxisStatus:elements.a===undefined?'absent-at-parabolic-boundary':'finite',
      ...Object.fromEntries(['M','n','arg_per','asc_node','Tp'].filter(k=>Object.hasOwn(elements,k)).map(k=>[k,elements[k]]))};
    summary.truthElementErrors=elementDifferences(summary.elements,{...command.truthElements,inverseA:(1-command.truthElements.e)/command.truthElements.q});
    summary.truthStateElementErrorsWithFindOrbGM=elementDifferences(summary.elements,command.truthStateElementsWithFindOrbGM);
    summary.elementTruthInterpretation='Descriptive error at matched physical epoch; no unique short-arc recovery requirement. Horizons elements use recorded table GM; state-derived comparison uses upstream Gaussian K. Node/perihelion angles become ill-conditioned for circular or coplanar orbits.';
  }
  return summary;
}
export function elementDifferences(a,b) {
  const differences=Object.fromEntries(['q','e','i','inverseA'].map(key=>[key,Math.abs(a[key]-b[key])]));
  for(const key of ['arg_per','asc_node'])if(Number.isFinite(a[key])&&Number.isFinite(b[key]))differences[key]=Math.abs(((a[key]-b[key]+540)%360+360)%360-180);
  return differences;
}
export function comparePair(baseline,candidate,{kind,applicability,fitGate='parity'}) {
  assert.ok(['parity','report'].includes(fitGate),'Known fit gate');
  const failures=[];if(!baseline.valid||!candidate.valid)return {pass:false,failures:['Engine execution or structural validation failed'],comparable:false};
  assert.equal(baseline.predictions.length,candidate.predictions.length,'Paired prediction count');
  const rows=baseline.predictions.map((b,i)=>{
    const c=candidate.predictions[i];assert.ok(Math.abs(b.jdUtc-c.jdUtc)<protocol.gates.epochToleranceDays,'Paired epochs');
    const differenceArcsec=separationArcsec(b,c),rangeDifferenceAu=Math.abs(b.rangeAu-c.rangeAu);
    const allowance=protocol.pairedAccuracyAllowance.absoluteArcsec+protocol.pairedAccuracyAllowance.relativeFraction*b.errorArcsec;
    return {jdUtc:b.jdUtc,differenceArcsec,rangeDifferenceAu,baselineErrorArcsec:b.errorArcsec,candidateErrorArcsec:c.errorArcsec,
      errorChangeArcsec:c.errorArcsec-b.errorArcsec,allowanceArcsec:allowance,degraded:c.errorArcsec>b.errorArcsec+allowance};
  });
  const maxDirectionDifferenceArcsec=Math.max(...rows.map(r=>r.differenceArcsec)),maxRangeDifferenceAu=Math.max(...rows.map(r=>r.rangeDifferenceAu));
  const elementDeltas=kind==='fit'?elementDifferences(baseline.elements,candidate.elements):null;
  const elementParity=kind!=='fit'||Object.entries(protocol.gates.elementParity).every(([key,limit])=>elementDeltas[key]<=limit);
  const parity=elementParity&&maxDirectionDifferenceArcsec<=protocol.gates[kind+'ParityArcsec']&&maxRangeDifferenceAu<=protocol.gates[kind+'RangeParityAu']&&
    (kind==='forward'||baseline.observations.used===candidate.observations.used);
  if(!parity&&(kind==='forward'||fitGate==='parity'))failures.push(kind+' engine parity exceeded frozen tolerance');
  const reference={applicability,baselineMaxArcsec:Math.max(...rows.map(r=>r.baselineErrorArcsec)),candidateMaxArcsec:Math.max(...rows.map(r=>r.candidateErrorArcsec)),enforced:kind==='forward'&&applicability.forwardTruth==='strict'};
  if(reference.enforced&&Math.max(reference.baselineMaxArcsec,reference.candidateMaxArcsec)>applicability.toleranceArcsec)failures.push('Independent forward-state reference floor exceeded frozen tolerance');
  return {pass:!failures.length,comparable:true,failures,parity,elementParity,elementDeltas,reference,maxDirectionDifferenceArcsec,maxRangeDifferenceAu,rows};
}
export function validateCoverage(command,coverage) {
  assert.ok(coverage&&Number.isFinite(coverage.startExclusiveJd)&&Number.isFinite(coverage.endInclusiveJd),'Verified ephemeris date coverage');
  const requested=[command.epochTt,...[...command.times,...(command.inputTimesUtc??[])].map(t=>t+69.184/86400)];
  assert.ok(requested.every(t=>t>coverage.startExclusiveJd&&t<=coverage.endInclusiveJd),'Requested state and reception epochs inside ephemeris interval');
  // Actual light-time/integration queries can extend beyond requested epochs;
  // the strict WASM reader remains the authority for those internal queries.
  return {minimumRequestedTtJd:Math.min(...requested),maximumRequestedTtJd:Math.max(...requested),coverage};
}
export function summarize(rows) {
  const groups=new Map();
  for(const row of rows) {
    const key=[row.class,row.arc,row.kind,row.applicability.forwardTruth].join('|');
    if(!groups.has(key))groups.set(key,{class:row.class,arc:row.arc,kind:row.kind,applicability:row.applicability.forwardTruth,runs:0,objects:new Set(),objectLabels:new Map(),failed:0,parityFailures:0,errors:[],changes:[],degraded:0});
    const id=objectId(row),g=groups.get(key);g.runs++;g.objects.add(id);g.objectLabels.set(id,row.object);g.failed+=!row.comparison.pass;g.parityFailures+=row.comparison.parity===false;
    for(const p of row.comparison.rows?.slice(1)??[]){g.errors.push(p.candidateErrorArcsec);g.changes.push(p.errorChangeArcsec);g.degraded+=p.degraded;}
  }
  return {pass:rows.length>0&&rows.every(r=>r.comparison.pass),pairs:rows.length,failedPairs:rows.filter(r=>!r.comparison.pass).length,
    groups:[...groups.values()].map(g=>({...g,objects:[...g.objects],objectLabels:Object.fromEntries(g.objectLabels),errors:undefined,changes:undefined,
      futurePredictionCount:g.errors.length,medianCandidateErrorArcsec:g.errors.length?quantile(g.errors,.5):null,p95CandidateErrorArcsec:g.errors.length?quantile(g.errors,.95):null,
      medianPairedErrorChangeArcsec:g.changes.length?quantile(g.changes,.5):null})),
    interpretation:'Repeated geometries/arcs/noise of one object are correlated. Counts are coverage, not independent samples; paired accuracy flags are descriptive, not posterior calibration or proof of element identifiability.'};
}
