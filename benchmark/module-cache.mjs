#!/usr/bin/env node
// Run modes in separate Node processes so retained modules cannot warm controls.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {loadWasm,loadNative} from './engines.mjs';
import {loadCases} from './cases.mjs';
import {validate,compare} from './accuracy.mjs';
const options={mode:'current',gc:'natural',output:'results/module-cache-current-natural.json'};
for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].slice(2);if(!Object.hasOwn(options,key)||!process.argv[i+1])throw new Error('Options: --mode current|retained --gc natural|controlled --output PATH');options[key]=process.argv[i+1];}
assert.ok(['current','retained'].includes(options.mode));assert.ok(['natural','controlled'].includes(options.gc));
if(options.gc==='controlled')assert.equal(typeof global.gc,'function','Use node --expose-gc.');
// Bypass the distribution's prepare step in this experiment only, so the
// unretained control remains reproducible after retention becomes the default.
const wasm=await loadWasm(resolve('dist'),{retainModule:options.mode==='retained',prepareRuntime:false}),native=await loadNative(resolve('.native-engine'));
const report={schema:1,createdAt:new Date().toISOString(),...options,node:process.version,manifest:wasm.manifest,setup:wasm.setup,
  methodology:'Separate process per configuration;2warmups+4samples per case; GC housekeeping outside timed command, recorded separately. Distribution runtime.prepare is bypassed to isolate module retention only. Every instance/heap/filesystem stays fresh.',cases:[]};
await mkdir(dirname(resolve(options.output)),{recursive:true});
for(const command of await loadCases()) {
  const reference=await native.execute(command);validate(command,reference);const samples=[];
  for(let i=-2;i<4;i++) {
    let beforeCommandGCms=0;
    if(options.gc==='controlled'){const start=performance.now();global.gc();beforeCommandGCms=performance.now()-start;}
    const result=await wasm.execute(command);result.accuracy={...validate(command,result),...compare(command,result,reference)};
    if(i>=0)samples.push({...result,housekeeping:{beforeCommandGCms}});
  }
  const sorted=samples.map(s=>s.phases.totalMs).sort((a,b)=>a-b),median=(sorted[1]+sorted[2])/2;
  report.cases.push({id:command.id,command,samples,medianTotalMs:median});
  await writeFile(options.output,JSON.stringify(report,null,2)+'\n');console.log(options.mode+'/'+options.gc+' '+command.id+' '+median.toFixed(2)+'ms');
}
