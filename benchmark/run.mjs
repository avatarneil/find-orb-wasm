#!/usr/bin/env node
import {mkdir,readFile,writeFile} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {cpus,platform,arch,release} from 'node:os';
import {loadWasm,loadNative} from './engines.mjs';
import {loadCases} from './cases.mjs';
import {validate,compare} from './accuracy.mjs';
const median=values=>{const sorted=values.slice().sort((a,b)=>a-b),n=sorted.length;return n%2?sorted[(n-1)/2]:(sorted[n/2-1]+sorted[n/2])/2;};
export async function benchmark({dist=resolve('dist'),native=resolve('.native-engine'),output=resolve('results/baseline.json'),repetitions=3,warmup=1,only=null}={}) {
  if(!Number.isInteger(repetitions)||repetitions<1||!Number.isInteger(warmup)||warmup<0) throw new Error('Repetitions >=1 and warmup >=0 are required.');
  const engines=[await loadNative(native),await loadNative(native,'fo'),await loadWasm(dist)];
  const cases=(await loadCases()).filter(c=>!only||only.split(',').includes(c.id));if(!cases.length)throw new Error('No benchmark cases selected.');
  const report={schema:1,createdAt:new Date().toISOString(),host:{platform:platform(),arch:arch(),release:release(),cpu:cpus()[0]?.model,node:process.version},
    methodology:{repetitions,warmup,freshRuntimePerCommand:true,execution:'Node.js WebAssembly versus native executable; no browser worker transfer time',
      wasmSolve:'callMain only; V8 JIT may continue warming during repetitions',nativeSolve:'process launch + dynamic loader + command; OS file cache is warm after warmup',
      setup:'Pack read and cryptographic verification measured separately once, excluded from per-command timing',
      comparison:'Accuracy parity uses native-count (same SR candidate count); native-original retains upstream half-second CPU cap and is separately reported',
      limitations:['One host; timing is not a universal speed claim.','Numerical regression and external-reference checks are not formal proof.','No non-gravitational forces or asteroid perturber ephemeris.']},
    fixtures:JSON.parse(await readFile(new URL('./fixtures/provenance.json',import.meta.url),'utf8')),
    engines:Object.fromEntries(engines.map(e=>[e.id,{root:e.root,manifest:e.manifest,setup:e.setup}])),cases:[]};
  await mkdir(dirname(output),{recursive:true});
  for(const command of cases) {
    console.log('Benchmark '+command.id);const entry={id:command.id,kind:command.kind,command,engines:{}};
    let reference;
    for(const engine of engines) {
      const samples=[];
      for(let i=-warmup;i<repetitions;i++) {
        const result=await engine.execute(command),accuracy=validate(command,result);
        if(engine.id==='native-count'&&!reference) reference=result;
        if(engine.id!=='native-original')Object.assign(accuracy,compare(command,result,reference));
        if(i>=0)samples.push({...result,accuracy});
      }
      const phases={};for(const key of Object.keys(samples[0].phases)) {
        const values=samples.map(s=>s.phases[key]);phases[key]={median:median(values),min:Math.min(...values),max:Math.max(...values),samples:values};
      }
      entry.engines[engine.id]={phases,samples};console.log('  '+engine.id+' total '+phases.totalMs.median.toFixed(2)+' ms');
    }
    report.cases.push(entry);await writeFile(output,JSON.stringify(report,null,2)+'\n');
  }
  return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const options={};for(let i=2;i<process.argv.length;i+=2) {
    const key=process.argv[i].slice(2),value=process.argv[i+1];if(!['dist','native','output','repetitions','warmup','only'].includes(key)||!value)throw new Error('Options: --dist --native --output --repetitions --warmup --only');
    options[key]=['repetitions','warmup'].includes(key)?Number(value):key==='only'?value:resolve(value);
  }
  await benchmark(options);
}
