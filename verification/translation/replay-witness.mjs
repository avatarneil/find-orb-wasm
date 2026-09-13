// GPL-2.0-or-later. Replay a concrete negative-control witness in actual WASM.
import {readFile} from 'node:fs/promises';
const [original,mutant,name,inputFile]=process.argv.slice(2);
const arrays=JSON.parse(await readFile(inputFile,'utf8'));
function bits(value){const a=new ArrayBuffer(8),v=new DataView(a);v.setFloat64(0,value,true);return v.getBigUint64(0,true).toString(16).padStart(16,'0');}
async function execute(path){
  const {instance}=await WebAssembly.instantiate(await readFile(path),{});
  const view=new DataView(instance.exports.memory.buffer);
  const addresses=arrays.map((values,i)=>{
    const address=4096+i*64;
    values.forEach((value,j)=>view.setFloat64(address+j*8,value,true));
    return address;
  });
  const result=instance.exports[name](...addresses);
  return {result:result===undefined?null:bits(result),
    arrays:addresses.map(address=>[0,1,2].map(j=>view.getBigUint64(address+j*8,true).toString(16).padStart(16,'0')))};
}
const before=await execute(original),after=await execute(mutant);
if(JSON.stringify(before)===JSON.stringify(after))throw new Error('Mutation witness did not change actual WASM behavior');
console.log(JSON.stringify({before,after}));
