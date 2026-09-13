import {test} from 'node:test';
import {resolve} from 'node:path';
import {readdir} from 'node:fs/promises';
import assert from 'node:assert/strict';
import {loadWasm,loadNative} from '../../benchmark/engines.mjs';
import {loadCases} from '../../benchmark/cases.mjs';
import {validate,compare} from '../../benchmark/accuracy.mjs';
const wasm=await loadWasm(resolve(process.env.FIND_ORB_DIST||'dist'));
const native=await loadNative(resolve(process.env.FIND_ORB_NATIVE||'.native-engine'));
for(const command of await loadCases())test(command.id,{timeout:120000},async t=>{
  const reference=await native.execute(command);validate(command,reference);
  assert.deepEqual((await readdir(resolve(native.root,'data'))).sort(),Object.keys(native.manifest.dataSHA256).sort(),'native runs must not write cached solutions beside reference data');
  const result=await wasm.execute(command);t.diagnostic(JSON.stringify({...validate(command,result),...compare(command,result,reference)}));
});
