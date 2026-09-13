#!/usr/bin/env node
import assert from 'node:assert/strict';
import {readFile,writeFile} from 'node:fs/promises';
import {compare} from './accuracy.mjs';
const [beforeFile,afterFile,output]=process.argv.slice(2);
if(!beforeFile||!afterFile)throw new Error('Usage: node benchmark/compare.mjs BEFORE.json AFTER.json [OUTPUT.json]');
const before=JSON.parse(await readFile(beforeFile,'utf8')),after=JSON.parse(await readFile(afterFile,'utf8'));
assert.deepEqual(before.fixtures,after.fixtures,'same observations/reference fixtures');
assert.deepEqual(before.engines.wasm.manifest.sources,after.engines.wasm.manifest.sources,'same upstream pins');
const result={before:beforeFile,after:afterFile,statistic:'Ratio of separately measured medians; observed ranges are not confidence intervals',cases:before.cases.map(a=>{
  const b=after.cases.find(b=>b.id===a.id);assert.ok(b,'matching case '+a.id);assert.deepEqual(a.command,b.command,'same command');
  const initial=a.engines.wasm.phases,final=b.engines.wasm.phases;
  // Also compare candidate directly to baseline, beyond each report's native oracle.
  const accuracy=compare(a.command,b.engines.wasm.samples[0],a.engines.wasm.samples[0]);
  return {id:a.id,beforeMs:initial.totalMs.median,afterMs:final.totalMs.median,speedup:initial.totalMs.median/final.totalMs.median,
    beforeRangeMs:[initial.totalMs.min,initial.totalMs.max],afterRangeMs:[final.totalMs.min,final.totalMs.max],
    beforeMountMs:initial.mountMs.median,afterMountMs:final.mountMs.median,
    beforeSolveMs:initial.solveMs.median,afterSolveMs:final.solveMs.median,accuracy};
})};
if(output)await writeFile(output,JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
