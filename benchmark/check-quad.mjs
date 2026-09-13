#!/usr/bin/env node
// Compare complete IEEE binary128 result bits against pinned compiler-rt.
import assert from 'node:assert/strict';
import {mkdir,readFile,writeFile,access} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {resolve,join} from 'node:path';
import {run} from '../build/build.mjs';
const root=resolve('.'),sdk=join(root,'.wasm-toolchain'),em=join(sdk,'upstream/emscripten/emcc');
const work=join(root,'.performance-quad/check');await mkdir(work,{recursive:true});
const env={...process.env},sdkPython=join(sdk,'python/3.13.3_64bit/bin/python3');
try{await access(sdkPython);env.EMSDK_PYTHON=sdkPython;}catch{/* Linux uses its host Python. */}
const flags=['-O3','-fno-fast-math','-ffp-contract=off'];
const original=join(sdk,'upstream/emscripten/system/lib/compiler-rt/lib/builtins/multf3.c');
const candidate=join(root,'.performance-quad/recipe/build/quad/multf3.c');
await run(em,[...flags,'-D__multf3=reference_multf3','-c',original,'-o',join(work,'original.o')],root,env);
await run(em,[...flags,'-D__multf3=candidate_multf3','-c',candidate,'-o',join(work,'candidate.o')],root,env);
await run(em,[...flags,join(root,'tests/accuracy/quad-kernel.c'),join(work,'original.o'),join(work,'candidate.o'),
  '-sMODULARIZE=1','-sENVIRONMENT=node','-sEXPORTED_FUNCTIONS=_run_random,_run_edges,_run_perf','-sASSERTIONS=1','--no-entry','-o',join(work,'check.cjs')],root,env);
const factory=createRequire(import.meta.url)(join(work,'check.cjs'));
const engine=await factory({wasmBinary:await readFile(join(work,'check.wasm'))});
const start=performance.now();assert.equal(engine._run_edges(),0,'all boundary/sign/NaN pair products match bitwise');
const seeds=[0x12345678,0xdeadbeef,0x9e3779b9,0xabcdef01];
for(const seed of seeds)assert.equal(engine._run_random(seed,250000),0,'random binary128 pair products match bitwise for seed '+seed);
const elapsedMs=performance.now()-start,performanceSamples={fullWidth:{reference:[],candidate:[]},widenedDouble:{reference:[],candidate:[]}};
for(const narrowed of [0,1])for(let i=-1;i<5;i++)for(const candidate of i%2?[1,0]:[0,1]) {
  const start=performance.now();const checksum=engine._run_perf(candidate,12345678,1000000,narrowed),elapsed=performance.now()-start;
  if(i>=0)performanceSamples[narrowed?'widenedDouble':'fullWidth'][candidate?'candidate':'reference'].push({elapsedMs:elapsed,checksum});
}
const report={schema:1,kernel:'benchmark/quad-wide-multiply.h',reference:'Pinned SDK compiler-rt multf3.c, unmodified',
  edgePairs:192**2,randomPairs:1000000,seeds,passed:true,elapsedMs,performanceSamples,
  method:'Exact 128-bit result representation equality, including NaN payload/sign; full original rounding and special-value code retained'};
await mkdir(join(root,'results'),{recursive:true});await writeFile(join(root,'results/quad-differential.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report,null,2));
