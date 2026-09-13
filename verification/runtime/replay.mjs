// GPL-2.0-or-later. Raw-bit adapters preserve production function instructions.
import {readFile} from 'node:fs/promises';
import assert from 'node:assert/strict';
const jobs=JSON.parse(await readFile(process.argv[2],'utf8'));
const records=[];
for(const job of jobs) {
  const bytes=await readFile(job.module);
  assert.ok(WebAssembly.validate(bytes),'host validation');
  const module=await WebAssembly.compile(bytes),imports={};
  for(const item of WebAssembly.Module.imports(module)) {
    assert.equal(item.kind,'function');
    (imports[item.module]??={})[item.name]=()=>{throw new Error('Unexpected imported call: '+item.name);};
  }
  const instance=new WebAssembly.Instance(module,imports),api=instance.exports;
  const stack=api.emscripten_stack_get_current();
  api.__set_stack_limits(stack,1024);
  const view=new DataView(api.memory.buffer),observed=[];
  for(const test of job.cases) {
    view.setBigUint64(4096,0n,true);view.setBigUint64(4104,0n,true);
    const lo=BigInt(test.lo),hi=BigInt(test.hi);
    let result;
    if(test.name==='__trunctfdf2') result=BigInt.asUintN(64,api[test.name](lo,hi));
    else {
      if(test.name==='__extenddftf2') api[test.name](4096,lo);
      else api[test.name](4096,lo,hi,test.shift);
      result=view.getBigUint64(4096,true)|(view.getBigUint64(4104,true)<<64n);
    }
    assert.equal(api.emscripten_stack_get_current(),stack,'stack restored');
    if(job.kind==='mutant') assert.notEqual(result,BigInt(test.expected),'actual mutated instructions must fail');
    else assert.equal(result,BigInt(test.expected),'original production result');
    if(job.kind!=='original') observed.push({...test,actual:String(result)});
  }
  records.push({kind:job.kind,count:job.cases.length,observed});
}
console.log(JSON.stringify({passed:true,node:process.version,records}));
