// GPL-2.0-or-later. Actual WebAssembly execution for negative controls only.
import fs from 'node:fs';
const [good,bad,fixture]=process.argv.slice(2);
const cells=JSON.parse(fs.readFileSync(fixture,'utf8'));
async function run(file){
  const bytes=fs.readFileSync(file);
  if(!WebAssembly.validate(bytes))throw Error('Invalid witness module');
  const {instance}=await WebAssembly.instantiate(bytes);
  const memory=new Uint8Array(instance.exports.memory.buffer);
  for(const cell of cells)memory.set(Buffer.from(cell.bytes,'hex'),cell.address);
  instance.exports.run();
  return [[1024,656],[8192,72]].map(([address,size])=>({address,bytes:Buffer.from(memory.slice(address,address+size)).toString('hex')}));
}
const [left,right]=await Promise.all([run(good),run(bad)]);
const differences=[];
for(let region=0;region<left.length;region++){
 const a=left[region],b=right[region];
 for(let i=0;i<a.bytes.length;i+=2)if(a.bytes.slice(i,i+2)!==b.bytes.slice(i,i+2)){
  differences.push({address:a.address+i/2,original:a.bytes.slice(i,i+2),mutated:b.bytes.slice(i,i+2)});
  if(differences.length===24)break;
 }
 if(differences.length===24)break;
}
console.log(JSON.stringify({different:differences.length>0,observed:'Caller-visible cache and output; stack scratch excluded',firstChangedBytes:differences}));
