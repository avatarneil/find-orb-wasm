#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import assert from 'node:assert/strict';
import {median,sha,separationArcsec} from './methods.mjs';
const json=async path=>JSON.parse(await readFile(path,'utf8'));
const models=['position','phase6d','min-rms','predictive1d'];
const pAt=(row,day)=>row.predictions?.find(p=>Math.abs(p.daysAfterOriginalArc-day)<1e-6);
const med=values=>values.length?median(values):null;
const pairKey=r=>[r.caseId,r.settings.scenario,r.settings.replicate,r.settings.budget].join('|');
export function compareForecasts(a,b) {
  assert.ok(a.length>0);assert.equal(a.length,b.length,'matched forecast count');
  const separation=a.map((p,i)=>{
    assert.ok(Math.abs(p.jdUtc-b[i].jdUtc)<1e-7,'matched comparison epoch');
    assert.ok([p.nominal.RA,p.nominal.Dec,b[i].nominal.RA,b[i].nominal.Dec].every(Number.isFinite));
    return separationArcsec(p.nominal,b[i].nominal);
  });
  return Math.max(...separation);
}
export async function analyze(root='results/local/short-arcs') {
  const groups=['development-v2','heldout-v2','followup-v2','tracklets-v3','heldout-wasm-v2'];
  const inputs={},data={};
  for(const group of groups) {
    const text=await readFile(join(root,group,'results.json'),'utf8');data[group]=JSON.parse(text);
    inputs[group]={resultsSHA256:sha(text),manifest:await json(join(root,group,'manifest.json'))};
  }
  const selection=[...data['development-v2'],...data['heldout-v2']],base=new Map(selection.filter(r=>r.settings.selection==='position').map(r=>[pairKey(r),r]));
  const primary=[];
  for(const split of ['development','held-out'])for(const budget of [100,500])for(const model of models) {
    const planned=selection.filter(r=>r.split===split&&r.settings.budget===budget&&r.settings.scenario==='gaussian'&&r.settings.selection===model);
    const rows=planned.filter(r=>r.valid&&r.eligibleSelectorComparison),pairs=rows.map(r=>[r,base.get(pairKey(r))]).filter(([,b])=>b?.valid&&b.eligibleSelectorComparison);
    primary.push({split,budget,model,planned:planned.length,eligible:rows.length,objects:[...new Set(rows.map(r=>r.object))],
      median1dArcsec:med(rows.map(r=>pAt(r,1).errorArcsec)),median7dArcsec:med(rows.map(r=>pAt(r,7).errorArcsec)),
      maximum7dArcsec:rows.length?Math.max(...rows.map(r=>pAt(r,7).errorArcsec)):null,
      medianInverseAError:med(rows.map(r=>r.elementErrors.inverseA)),medianEError:med(rows.map(r=>r.elementErrors.e)),
      medianQErrorAu:med(rows.map(r=>r.elementErrors.q)),medianInclinationErrorDeg:med(rows.map(r=>r.elementErrors.i)),
      wins7d:pairs.filter(([r,b])=>pAt(r,7).errorArcsec<pAt(b,7).errorArcsec-1e-6).length,
      ties7d:pairs.filter(([r,b])=>Math.abs(pAt(r,7).errorArcsec-pAt(b,7).errorArcsec)<1e-6).length,
      pairedMedianErrorRatio:med(pairs.map(([r,b])=>pAt(r,7).errorArcsec/pAt(b,7).errorArcsec)),
      medianTotalMs:med(rows.map(r=>r.phases.totalMs)),
      actualAttempts:[...new Set(rows.map(r=>r.search.attemptedTotal))],
      median90Radius7dArcsec:med(rows.map(r=>pAt(r,7).ensemble.radius90Arcsec)),
      included90Radius7d:rows.filter(r=>pAt(r,7).ensemble.inside90Radius).length});
  }
  const followups=[];
  for(const rows of [data['followup-v2'],data['tracklets-v3']])for(const budget of [100,500])for(const arc of [...new Set(rows.map(r=>r.settings.arc))]) {
    const planned=rows.filter(r=>r.settings.scenario==='gaussian'&&r.settings.budget===budget&&r.settings.arc===arc);
    const pairs=planned.filter(r=>r.valid&&r.excluded===0).map(r=>[r,base.get(pairKey(r))]).filter(([,b])=>b?.valid&&b.excluded===0);
    followups.push({arc,budget,planned:planned.length,eligible:pairs.length,caseIds:[...new Set(pairs.map(([r])=>r.caseId))],
      objects:[...new Set(pairs.map(([r])=>r.object))],
      medianBaseline7dArcsec:med(pairs.map(([,b])=>pAt(b,7).errorArcsec)),median7dArcsec:med(pairs.map(([r])=>pAt(r,7).errorArcsec)),
      medianPairedImprovement:med(pairs.map(([r,b])=>pAt(b,7).errorArcsec/pAt(r,7).errorArcsec)),
      wins7d:pairs.filter(([r,b])=>pAt(r,7).errorArcsec<pAt(b,7).errorArcsec).length,
      medianBaselineInverseAError:med(pairs.map(([,b])=>b.elementErrors.inverseA)),medianInverseAError:med(pairs.map(([r])=>r.elementErrors.inverseA)),
      pairs:pairs.map(([r,b])=>({caseId:r.caseId,object:r.object,replicate:r.settings.replicate,
        baseline7dArcsec:pAt(b,7).errorArcsec,error7dArcsec:pAt(r,7).errorArcsec,method:r.uncertaintyMethod,attempts:r.search.attemptedTotal}))});
  }
  const support=[];
  for(const budget of [100,500]) {
    const rows=selection.filter(r=>r.valid&&r.settings.selection==='position'&&r.settings.scenario==='gaussian'&&r.settings.budget===budget);
    support.push({budget,n:rows.length,dimensions:Object.fromEntries(['inverseA','e','q','i'].map(key=>[key,{
      fullSupport:rows.filter(r=>r.candidates.allGeneratedIntervals?.[key].inSupport).length,
      acceptedSupport:rows.filter(r=>r.candidates.acceptedIntervals?.[key].inSupport).length,
      central90:rows.filter(r=>r.candidates.acceptedIntervals?.[key].inCentral90).length}]))});
  }
  const stress=['exact','gaussian','biased','contaminated'].map(scenario=>{
    const rows=selection.filter(r=>r.settings.selection==='position'&&r.settings.budget===100&&r.settings.scenario===scenario),valid=rows.filter(r=>r.valid);
    return {scenario,n:rows.length,valid:valid.length,excluded:rows.filter(r=>r.excluded>0).length,
      median7dArcsec:med(valid.map(r=>pAt(r,7).errorArcsec)),medianInverseAError:med(valid.map(r=>r.elementErrors.inverseA))};
  });
  const controls=await json(join(root,'controls-v2/summary.json')),controlAssessment=await json(join(root,'controls-v2/assessment.json'));
  const ident=await json(join(root,'identifiability-v1/results.json'));
  const identifiability={protocol:ident.protocol,cases:ident.cases.map(c=>({id:c.id,object:c.object.name,
    arcs:Object.fromEntries(Object.entries(c.arcs).map(([name,a])=>[name,{
      singularValues:a.decompositions[1].singularValues,resolved:a.stepSensitivity.singularModesResolvedUnderTestedSteps,
      conditionNumber:a.stepSensitivity.conditionNumber,weakSubspacePrincipalCosines:a.stepSensitivity.weakSubspacePrincipalCosines,
      weakModes:a.decompositions[1].weakestModes,weakSubspace:a.decompositions[1].weakTwoModeSubspace}])),
    nextNight:c.nextNightComparison}))};
  const wasm=data['heldout-wasm-v2'].map(r=>{
    const native=base.get(pairKey(r));
    assert.ok(native&&r.valid&&native.valid,'paired held-out fits valid');
    const maxSkySeparationArcsec=compareForecasts(r.predictions,native.predictions);
    const maxElementDifference=Math.max(...['a','e','i','M','arg_per','asc_node','q','epoch'].map(k=>Math.abs(r.elements[k]-native.elements[k])));
    return {id:r.id,valid:true,maxSkySeparationArcsec,maxElementDifference,
      maxTruthErrorMagnitudeDifferenceArcsec:Math.max(...r.predictions.map((p,i)=>Math.abs(p.errorArcsec-native.predictions[i].errorArcsec))),
      tolerances:{skyArcsec:.001,primaryElements:1e-6},passed:maxSkySeparationArcsec<=.001&&maxElementDifference<=1e-6};
  });
  const comparisonRows=selection.map(r=>({id:r.id,caseId:r.caseId,object:r.object,split:r.split,settings:r.settings,valid:r.valid,
    eligible:r.eligibleSelectorComparison??false,excluded:r.excluded??null,errorStage:r.errorStage??null,invalidReason:r.invalidReason??r.error??null,
    elements:r.elements?Object.fromEntries(['a','e','q','i','rms_residual','weighted_rms_residual'].map(k=>[k,r.elements[k]])):null,
    elementErrors:r.elementErrors??null,predictions:r.predictions??[],attempted:r.search?.attemptedTotal??null,totalMs:r.phases?.totalMs??null}));
  const output={schemaVersion:1,createdAt:new Date().toISOString(),inputs,primary,followups,support,stress,identifiability,
    controls:{executions:controls.executedRecords,failures:controls.executionFailures,strictComparisonsPassed:controls.comparisonsPassed,
      strictComparisonsFailed:controls.comparisonsFailed,maxTruthSkyErrorArcsec:Math.max(...controls.records.filter(r=>r.kind==='truth-propagation'&&!r.error).map(r=>r.maxSeparationArcsec)),
      assessment:controlAssessment},heldoutWasm:wasm,comparisonRows,
    limitations:['Only six observable objects, seven arcs; held-out split has three objects and four arcs. Noise replicates and repeated Juno epochs are not independent objects.',
      'Three nightly tracklets are an exploratory observational intervention on four visibility-selected objects, not an improvement from the same one-hour data.',
      'Finite-difference resolution is empirical; full solver/compiler and global orbital uniqueness are unproved.',
      'Heuristic candidate intervals are not posterior probabilities. Runtime observations include concurrent correctness work, not controlled performance measurements.']};
  await mkdir('results/short-arcs',{recursive:true});await writeFile('results/short-arcs/analysis.json',JSON.stringify(output,null,2)+'\n');
  return output;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))await analyze(process.argv[2]);
