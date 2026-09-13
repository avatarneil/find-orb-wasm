#!/usr/bin/env node
import assert from 'node:assert/strict';
import {mkdir,readFile,writeFile} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {cpus,platform,arch,release} from 'node:os';
import {loadWasm,loadNative} from './engines.mjs';
import {loadCases} from './cases.mjs';
import {validate,compare} from './accuracy.mjs';
const median=xs=>{const s=xs.slice().sort((a,b)=>a-b);return s.length%2?s[(s.length-1)/2]:(s[s.length/2-1]+s[s.length/2])/2;};
const statistics=values=>({median:median(values),min:Math.min(...values),max:Math.max(...values),samples:values});
const options={before:resolve('dist-baseline'),after:resolve('dist'),native:resolve('.native-engine'),output:resolve('results/paired.json'),repetitions:8,warmup:2};
for(let i=2;i<process.argv.length;i+=2) {
  const key=process.argv[i].slice(2),value=process.argv[i+1];
  if(!Object.hasOwn(options,key)||!value)throw new Error('Options: --before --after --native --output --repetitions --warmup');
  options[key]=['repetitions','warmup'].includes(key)?Number(value):resolve(value);
}
assert.ok(Number.isInteger(options.repetitions)&&options.repetitions>=4&&options.repetitions%2===0,'Use an even repetition count >=4 for balanced AB/BA order.');
assert.ok(Number.isInteger(options.warmup)&&options.warmup>=1);
assert.equal(typeof globalThis.gc,'function','Run paired benchmarks with node --expose-gc to isolate each command from the preceding variant garbage.');
const engines={before:await loadWasm(options.before),after:await loadWasm(options.after),
  'native-count':await loadNative(options.native),'native-original':await loadNative(options.native,'fo')};
assert.deepEqual(engines.before.manifest.sources,engines.after.manifest.sources,'same upstream source pins');
const report={schema:1,createdAt:new Date().toISOString(),host:{platform:platform(),arch:arch(),release:release(),cpu:cpus()[0]?.model,node:process.version},
  methodology:{repetitions:options.repetitions,warmup:options.warmup,order:'Per case, AB then BA alternating; fresh runtimes each command; sequential execution',
    measurement:'Node.js; WASM solve phase callMain, native processAndSolve includes process spawn; setup verification excluded from per-job totals',
    garbageCollection:'Synchronous GC before every WASM command, outside measured phases; its separate housekeeping time is retained in every sample. This prevents prior-variant allocations from shifting GC cost into the next command.',
    precision:'WASM binary128 long double vs host ABI native long double; inspect native manifest for mantissa bits',
    interpretation:'Reported speedup is median of paired before/after total-time ratios; min/max are observed sample spread, not a confidence interval',
    limitations:['One machine and Node version; browser timing may differ.','Run on an otherwise idle machine; background CPU contention is not controlled by this script.','Numeric output checks and reference tolerances do not prove the complete orbit solver.']},
  fixtures:JSON.parse(await readFile(new URL('./fixtures/provenance.json',import.meta.url),'utf8')),
  engines:Object.fromEntries(Object.entries(engines).map(([id,e])=>[id,{root:e.root,manifest:e.manifest,setup:e.setup}])),cases:[]};
await mkdir(dirname(options.output),{recursive:true});
for(const command of await loadCases()) {
  console.log('Paired '+command.id);
  const entry={id:command.id,kind:command.kind,command,engines:{before:{samples:[]},after:{samples:[]},'native-count':{samples:[]},'native-original':{samples:[]}}};
  const reference=await engines['native-count'].execute(command);validate(command,reference);
  for(let i=-options.warmup;i<options.repetitions;i++) {
    const pair={};
    for(const id of i%2?['after','before']:['before','after']) {
      const gcStart=performance.now();globalThis.gc();const beforeCommandGCms=performance.now()-gcStart;
      const result=await engines[id].execute(command);
      result.housekeeping={beforeCommandGCms};
      result.accuracy={...validate(command,result),...compare(command,result,reference)};pair[id]=result;
      if(i>=0)entry.engines[id].samples.push(result);
    }
    compare(command,pair.after,pair.before);
  }
  for(const id of ['native-count','native-original'])for(let i=-options.warmup;i<options.repetitions;i++) {
    const result=await engines[id].execute(command);result.accuracy=validate(command,result);
    if(id==='native-count')Object.assign(result.accuracy,compare(command,result,reference));
    if(i>=0)entry.engines[id].samples.push(result);
  }
  for(const data of Object.values(entry.engines))data.phases=Object.fromEntries(Object.keys(data.samples[0].phases).map(key=>[key,statistics(data.samples.map(s=>s.phases[key]))]));
  entry.pairedSpeedup=statistics(entry.engines.before.samples.map((sample,i)=>sample.phases.totalMs/entry.engines.after.samples[i].phases.totalMs));
  report.cases.push(entry);await writeFile(options.output,JSON.stringify(report,null,2)+'\n');
  console.log('  '+entry.engines.before.phases.totalMs.median.toFixed(2)+' -> '+entry.engines.after.phases.totalMs.median.toFixed(2)+' ms; paired '+entry.pairedSpeedup.median.toFixed(2)+'x');
}
