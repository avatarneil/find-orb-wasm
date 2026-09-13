// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {direction,elementErrors,separationArcsec,finiteFields} from './methods.mjs';
import {stateCommand} from '../../benchmark/cases.mjs';
import {skyRows,parseVectors} from '../../benchmark/accuracy.mjs';

// For a fixed empirical measure, argmin_i mean_j ||u_i-u_j||^2 equals
// argmin_i ||u_i-mean_j u_j||^2. This selects an actual candidate and uses no
// truth. Equal weights describe the heuristic family, not posterior probability.
export function predictiveIndex(points) {
  if(!points.length)throw new Error('Empty prediction family.');
  const vectors=points.map(direction),mean=vectors.reduce((a,v)=>a.map((x,i)=>x+v[i]/vectors.length),[0,0,0]);
  let best=0,loss=Infinity;
  for(let i=0;i<vectors.length;i++) {
    const score=vectors[i].reduce((s,x,j)=>s+(x-mean[j])**2,0);
    if(!Number.isFinite(score))throw new Error('Nonfinite predictive selection loss.');
    if(score<loss){best=i;loss=score;}
  }
  return {index:best,squaredChordLoss:loss,meanDirection:mean};
}
export function familyRows(text) {
  const lines=text.trim().split('\n'),header=lines.shift();
  assert.equal(header,'family_index,epoch_tt_jd,x_au,y_au,z_au,vx_au_day,vy_au_day,vz_au_day');
  return lines.map((line,index)=>{
    const row=finiteFields(line,8);assert.equal(row[0],index);
    return {index,epochJdTt:row[1],state:row.slice(2)};
  });
}
export async function selectPredictive(c,command,raw,summary,engine,{offsetEnsemble,candidateRows}) {
  if(!summary.valid||!summary.selectorApplied)return {summary:{...summary,predictive:{applied:false,reason:'No retained statistical-ranging family.'}},predictionRaw:null,predictionCommand:null};
  const target=c.epochJdUtc+1,nominal=skyRows(raw).find(p=>Math.abs(p.JD-target)<1e-7);assert.ok(nominal);
  const offset=Object.entries(raw.files).find(([name,text])=>name.startsWith('/job/offsets/')&&Math.abs(Number(/^# JD ([0-9.]+)/.exec(text)?.[1])-target)<.00000051);assert.ok(offset);
  const points=offsetEnsemble(offset[1],nominal),family=familyRows(raw.files['/job/family.csv']);assert.equal(points.length,family.length);
  const chosen=predictiveIndex(points),candidate=family[chosen.index];
  const original=candidateRows(raw.files['/job/candidates.csv']).find(row=>row.state.every((x,i)=>x===candidate.state[i]));assert.ok(original,'selected state maps exactly to an exported successful candidate');
  // The -v CLI path fixes the element epoch to the supplied vector epoch; -tE
  // does not override it. Propagate once in TT, then start a fresh sky command
  // with that state at the common fitted/truth epoch. Preserve both raw steps.
  const transferCommand=stateCommand(candidate.state,{epoch:candidate.epochJdTt,start:c.epochJdTt,count:1,step:'1d',scale:'TT'});
  const transferRaw=await engine.execute(transferCommand),stateAtFitEpoch=parseVectors(transferRaw.files['/job/vectors.txt'],transferCommand)[0];
  const predictionCommand=stateCommand(stateAtFitEpoch,{epoch:c.epochJdTt,start:command.start,count:command.count,step:'6h',scale:'UTC',sky:true});
  predictionCommand.outputs.push('/job/elements.json');
  const predictionRaw=await engine.execute(predictionCommand),sky=skyRows(predictionRaw);
  const object=JSON.parse(predictionRaw.files['/job/elements.json']).objects.CER0001;assert.ok(object);
  assert.ok(Math.abs(object.elements.epoch-c.epochJdTt)<1e-7);
  // Cross-check the index mapping through an independent propagation command.
  // Offset quantization is 0.1 arcsec in each coordinate; allow that rounding.
  const mapped=sky.find(p=>Math.abs(p.JD-target)<1e-7);assert.ok(mapped);
  const mappingError=separationArcsec(mapped,points[chosen.index]);assert.ok(mappingError<.09,'ordered family maps to the same propagated sky candidate');
  const elements={...object.elements,rms_residual:null,weighted_rms_residual:original.weighted_rms,n_resids:original.n_residuals};
  const predictions=summary.predictions.map(p=>{
    const estimate=sky.find(s=>Math.abs(s.JD-p.jdUtc)<1e-7),truth=c.holdout.find(t=>Math.abs(t.jdUtc-p.jdUtc)<1e-7);assert.ok(estimate&&truth);
    return {...p,errorArcsec:separationArcsec(estimate,truth),nominal:{RA:estimate.RA,Dec:estimate.Dec,delta:estimate.delta,sigPos:null}};
  });
  return {summary:{...summary,elements,elementErrors:elementErrors(elements,c.elements),predictions,
    phases:{...summary.phases,totalMs:summary.phases.totalMs+transferRaw.phases.totalMs+predictionRaw.phases.totalMs,
      predictivePropagationMs:transferRaw.phases.totalMs+predictionRaw.phases.totalMs},
    predictive:{applied:true,targetJdUtc:target,...chosen,mappingErrorArcsec:mappingError,probabilityCalibrated:false,
      description:'Actual candidate minimizing empirical squared chord distance at +1 day; uniform heuristic family measure; unweighted RMS not recomputed.'}},
    predictionRaw:{...predictionRaw,transferRaw,transferCommand},predictionCommand};
}
