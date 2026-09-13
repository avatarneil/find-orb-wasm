#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir,access} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {gzipSync} from 'node:zlib';
import os from 'node:os';
import {loadNative,loadWasm} from '../../benchmark/engines.mjs';
import {skyRows} from '../../benchmark/accuracy.mjs';
import {fitCommand,elementErrors,stateElements,quantile,skyEnsembleMetrics,separationArcsec,sha,finiteFields} from './methods.mjs';
import {patches} from './patches.mjs';
import {selectPredictive,familyRows} from './predictive.mjs';

export function candidateRows(text) {
  if(!text.trim())return [];
  const lines=text.trim().split('\n'),header=lines.shift().split(',');
  assert.deepEqual(header,['source_index','epoch_tt_jd','x_au','y_au','z_au','vx_au_day','vy_au_day','vz_au_day','heuristic_score','weighted_rms','n_residuals','rparam','vparam']);
  return lines.map(line=>{
    const values=finiteFields(line,header.length);
    const row=Object.fromEntries(header.map((key,i)=>[key,values[i]]));
    return {...row,state:values.slice(2,8),invariants:stateElements(values.slice(2,8))};
  });
}
export function offsetEnsemble(text,nominal) {
  const lines=text.trim().split('\n'),epoch=/^# JD ([0-9.]+)/.exec(lines[0]),count=/^# (\d+) points;/.exec(lines[2]);
  assert.ok(epoch&&count);assert.ok(Math.abs(Number(epoch[1])-nominal.JD)<.00000051);
  assert.equal(lines.length,Number(count[1])+3);
  const cos=Math.cos(nominal.Dec*Math.PI/180);assert.ok(Math.abs(cos)>1e-6,'offset inversion too close to celestial pole');
  return lines.slice(3).map(line=>{
    const [dx,dy]=finiteFields(line,2,/\s+/);
    // Invert upstream calc_sr_dist_and_posn_ang's coordinate differences,
    // not an exponential-map approximation. Only its 0.1-arcsec quantization remains.
    const Dec=nominal.Dec+dy/3600;assert.ok(Math.abs(Dec)<=90.00002);
    return {RA:((nominal.RA+dx/(3600*cos))%360+360)%360,Dec:Math.max(-90,Math.min(90,Dec))};
  });
}
function intervals(rows,truth) {
  if(!rows.length)return null;
  return Object.fromEntries(['inverseA','q','e','i'].map(key=>{
    const values=rows.map(r=>r.invariants[key]),value=key==='inverseA'?1/truth.a:truth[key];
    const lo=quantile(values,.05),hi=quantile(values,.95),min=Math.min(...values),max=Math.max(...values);
    return [key,{min,max,lo,hi,truth:value,inSupport:value>=min&&value<=max,inCentral90:value>=lo&&value<=hi}];
  }));
}
export function evaluate(c,command,result) {
  assert.equal(result.exitCode,0);
  const fit=JSON.parse(result.files['/job/elements.json']).objects[command.designation];assert.ok(fit);
  assert.equal(fit.observations.count,command.observationCount);
  const e=fit.elements,text=result.files['/job/elements.txt'];
  const force=/^# Perturbers:\s+([0-9a-f]+).*JPL DE-440.*$/im.exec(text);
  const method=Number(/^# Sigmas avail: (\d+)/m.exec(text)?.[1]??0);
  const valid=fit.observations.used>=3&&Boolean(force)&&(parseInt(force[1],16)&0x7fe)===0x7fe;
  const summary={valid,observations:fit.observations,uncertaintyMethod:method,
    excluded:command.observationCount-fit.observations.used,elements:e,phases:result.phases,
    invalidReason:valid?null:'Fewer than three used observations or full planetary force model absent.'};
  if(!valid)return summary;
  assert.ok(['a','q','e','i','epoch','rms_residual'].every(k=>Number.isFinite(e[k])));
  assert.ok(Math.abs(e.epoch-c.epochJdTt)<1e-7,'matched truth/fit TT epoch');
  summary.elementErrors=elementErrors(e,c.elements);
  const sky=skyRows(result);assert.equal(sky.length,command.count);
  for(let i=0;i<sky.length;i++) {
    assert.ok([sky[i].JD,sky[i].RA,sky[i].Dec].every(Number.isFinite));
    assert.ok(Math.abs(sky[i].JD-command.start-i*command.stepDays)<1e-7);
  }
  const offsets=Object.entries(result.files).filter(([name])=>name.startsWith('/job/offsets/'));
  const families=offsets.map(([,text])=>{
    const jd=Number(/^# JD ([0-9.]+)/.exec(text)?.[1]),nominal=sky.find(s=>Math.abs(s.JD-jd)<.00000051);
    assert.ok(nominal);return {jd:nominal.JD,points:offsetEnsemble(text,nominal)};
  });
  summary.predictions=c.holdout.filter(t=>t.jdUtc>command.lastObservationJdUtc+1e-7).map(truth=>{
    const nominal=sky.find(s=>Math.abs(s.JD-truth.jdUtc)<1e-7);assert.ok(nominal);
    const family=families.find(f=>Math.abs(f.jd-truth.jdUtc)<1e-7);
    return {jdUtc:truth.jdUtc,daysAfterOriginalArc:truth.jdUtc-c.epochJdUtc,errorArcsec:separationArcsec(nominal,truth),
      nominal:{RA:nominal.RA,Dec:nominal.Dec,delta:nominal.delta,sigPos:nominal.sigPos??null},
      ensemble:family?skyEnsembleMetrics(family.points,truth):null};
  });
  const candidates=candidateRows(result.files['/job/candidates.csv']||''),accepted=candidates.filter(c=>c.heuristic_score<.7);
  if(method===3&&Object.hasOwn(command.files,'/job/candidates.csv'))
    assert.ok(candidates.length>0,'experimental SR fit must emit candidates; reject a stale or uninstrumented binary');
  // MPC time quantization can move the first epoch by 0.0432 s. A later first
  // retained observation is a different osculating epoch, not comparable here.
  const epochMatched=candidates.every(row=>Math.abs(row.epoch_tt_jd-c.startJdTt)<.0000006);
  summary.candidates={generated:candidates.length,accepted:accepted.length,epochMatched,
    acceptedIntervals:epochMatched?intervals(accepted,c.initialElements):null,
    allGeneratedIntervals:epochMatched?intervals(candidates,c.initialElements):null};
  // Only a retained SR family certifies that the selector branch supplied the
  // reported nominal; later full improvement can replace an SR initial solution.
  summary.selectorApplied=method===3&&accepted.length>10;
  summary.eligibleSelectorComparison=summary.selectorApplied&&summary.excluded===0;
  if(summary.selectorApplied&&families.length)assert.equal(families[0].points.length,accepted.length,'exported accepted family matches prediction family');
  if(summary.selectorApplied&&Object.hasOwn(command.files,'/job/family.csv')) {
    const ordered=familyRows(result.files['/job/family.csv']);assert.equal(ordered.length,accepted.length);
  }
  const batches=result.files['/job/batches.csv']?.trim();
  summary.search={configuredInitialBatchCapacity:Number(/MAX_SR_ORBITS=(\d+)/.exec(command.files['/job/job.env'])[1]),batches:[],attemptedTotal:null};
  if(batches) {
    const lines=batches.split('\n'),columns=lines.shift().split(',');
    assert.deepEqual(columns,['starting_orbit','n_observations','max_orbits','attempted','successful','epoch_tt_jd']);
    summary.search.batches=lines.map(line=>{
      const values=finiteFields(line,columns.length);
      return Object.fromEntries(columns.map((key,i)=>[key,values[i]]));
    });
    summary.search.attemptedTotal=summary.search.batches.reduce((n,b)=>n+b.attempted,0);
  }
  if(summary.selectorApplied&&Object.hasOwn(command.files,'/job/batches.csv'))assert.ok(summary.search.batches.length>0,'instrumented SR run records actual work');
  return summary;
}

export async function runExperiment(options={}) {
  const defaults={engine:'native-experiment',split:'development',corpus:'experiments/short-arcs/fixtures/observable-corpus.json',
    scenarios:'exact,gaussian,biased,contaminated',replicates:'0,1,2',budgets:'100,500',selections:'position,phase6d,min-rms,predictive1d',arcs:'one-hour',output:'results/local/short-arcs/development'};
  const config={...defaults,...options},corpusText=await readFile(config.corpus,'utf8'),corpus=JSON.parse(corpusText);
  let trackletsSHA256=null;
  if(config.arcs.includes('tracklets')) {
    const text=await readFile(new URL('./fixtures/followup-tracklets.json',import.meta.url),'utf8'),extra=JSON.parse(text);
    trackletsSHA256=sha(text);for(const c of corpus.cases)c.followupTracklets=extra.cases.find(t=>t.id===c.id||t.caseId===c.id);
  }
  if(!['development','held-out','all'].includes(config.split))throw new Error('Invalid split.');
  const experimental=config.engine.endsWith('-experiment');
  let engine;
  if(config.engine==='native-experiment')engine=await loadNative('.native-engine-short-arcs');
  else if(config.engine==='wasm-experiment')engine=await loadWasm('dist-short-arcs');
  else if(config.engine==='native-baseline')engine=await loadNative('.native-engine');
  else if(config.engine==='wasm-baseline')engine=await loadWasm('dist-compact');
  else throw new Error('Invalid engine.');
  if(experimental) {
    const evidence=JSON.parse(await readFile(join(engine.root,'short-arc-experiment.json'),'utf8'));
    assert.equal(evidence.patchesSHA256,sha(JSON.stringify(patches)),'experimental binary built with current checked patches');
  }
  const plans=[];
  for(const c of corpus.cases.filter(c=>config.split==='all'||c.split===config.split))
    for(const scenario of config.scenarios.split(','))
      for(const replicate of config.replicates.split(',').map(Number)) {
        if(scenario==='exact'&&replicate!==0)continue;
        for(const budget of config.budgets.split(',').map(Number))
          for(const selection of config.selections.split(','))for(const arc of config.arcs.split(','))
            plans.push({c,scenario,replicate,budget,selection,arc});
      }
  const output=resolve(config.output);await mkdir(output,{recursive:true});
  // Prevent silently overwriting previous evidence; use a distinct output folder.
  try {await access(join(output,'manifest.json'));throw new Error('Evidence directory already used.');}
  catch(error){if(error.code!=='ENOENT')throw error;}
  const manifest={schemaVersion:1,config,corpusSHA256:sha(corpusText),protocolSHA256:sha(await readFile(new URL('./protocol.json',import.meta.url))),
    trackletsSHA256,predictiveSHA256:sha(await readFile(new URL('./predictive.mjs',import.meta.url))),
    methodsSHA256:sha(await readFile(new URL('./methods.mjs',import.meta.url))),runnerSHA256:sha(await readFile(fileURLToPath(import.meta.url))),
    patchesSHA256:sha(JSON.stringify(patches)),engine:engine.manifest,
    host:{platform:os.platform(),arch:os.arch(),node:process.version,cpu:os.cpus()[0]?.model},startedAt:new Date().toISOString(),plannedRuns:plans.length};
  await writeFile(join(output,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
  const results=[];
  for(const {c,...settings}of plans) {
    const id=[c.id,settings.scenario,settings.replicate,settings.budget,settings.selection,settings.arc].join('_');
    let command=null,raw,summary,predictionRaw=null,predictionCommand=null,stage='command';
    try {
      command=fitCommand(c,{...settings,experimental});stage='execution';raw=await engine.execute(command);stage='validation';summary=evaluate(c,command,raw);
      if(settings.selection==='predictive1d') {
        stage='predictive-selection';({summary,predictionRaw,predictionCommand}=await selectPredictive(c,command,raw,summary,engine,{offsetEnsemble,candidateRows}));
      }
    } catch(error){summary={...summary,valid:false,errorStage:stage,solverCompleted:Boolean(raw),error:String(error.stack||error)};}
    const bytes=Buffer.from(JSON.stringify({id,caseId:c.id,settings,command,result:raw??null,predictionCommand,predictionRaw,summary}));
    await writeFile(join(output,id+'.json.gz'),gzipSync(bytes,{level:9}));
    const row={id,caseId:c.id,object:c.object.name,split:c.split,settings,...summary,rawSHA256:sha(bytes),rawFile:id+'.json.gz'};
    // Residual rows remain in raw evidence, keeping the comparison index compact.
    if(row.observations)row.observations={count:row.observations.count,used:row.observations.used};
    results.push(row);await writeFile(join(output,'results.json'),JSON.stringify(results,null,2)+'\n');
    console.log(JSON.stringify({i:results.length,n:plans.length,id,valid:summary.valid,used:summary.observations?.used,
      a:summary.elements?.a,error1d:summary.predictions?.find(p=>Math.abs(p.daysAfterOriginalArc-1)<1e-6)?.errorArcsec,error:summary.error?.split('\n')[0]}));
  }
  manifest.completedAt=new Date().toISOString();manifest.completedRuns=results.length;
  await writeFile(join(output,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
  return {manifest,results};
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const options={};for(let i=2;i<process.argv.length;i+=2) {
    const key=process.argv[i]?.slice(2);if(!['engine','split','corpus','scenarios','replicates','budgets','selections','arcs','output'].includes(key)||!process.argv[i+1])
      throw new Error('Usage: node experiments/short-arcs/run.mjs --engine native-experiment|wasm-experiment|native-baseline|wasm-baseline --split development|held-out|all --corpus PATH --scenarios CSV --replicates CSV --budgets CSV --selections CSV --arcs CSV --output PATH');
    options[key]=process.argv[i+1];
  }
  await runExperiment(options);
}
