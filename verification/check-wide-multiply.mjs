#!/usr/bin/env node
// GPL-2.0-or-later. Independent BigInt oracle for the actual C limb helper.
import {readFile, writeFile, mkdir, readdir} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {spawn} from 'node:child_process';
import {resolve, join} from 'node:path';
import {fileURLToPath} from 'node:url';

const root=resolve(fileURLToPath(new URL('../',import.meta.url)));
const contract=JSON.parse(await readFile(join(root,'verification/wide-multiply-contract.json'),'utf8'));
const source=join(root,contract.path), sdk=join(root,'.wasm-toolchain');
if(createHash('sha256').update(await readFile(source)).digest('hex')!==contract.sha256)
  throw new Error('Wide multiplication source changed; review the model before updating its contract.');
const output=process.argv[2] ? resolve(process.argv[2]) : join(root,'results/local/wide-multiply-compiler.json');
const work=join(root,'results/local/wide-multiply-compiler');
await mkdir(work,{recursive:true});
const run=(program,args,input='')=>new Promise((yes,no)=>{
  const child=spawn(program,args,{cwd:root,env:{...process.env,EM_CONFIG:join(sdk,'.emscripten')},stdio:['pipe','pipe','pipe']});
  let stdout='',stderr='';
  const timer=setTimeout(()=>child.kill('SIGKILL'),180000);
  child.stdout.on('data',chunk=>stdout+=chunk);child.stderr.on('data',chunk=>stderr+=chunk);
  child.once('error',error=>{clearTimeout(timer);no(error);});
  child.once('exit',(code,signal)=>{clearTimeout(timer);code===0?yes(stdout):no(new Error(`${program} failed (${signal||code}): ${stderr}`));});
  child.stdin.on('error',error=>{if(error.code!=='EPIPE')no(error);});
  child.stdin.end(input);
});
const cpp=join(work,'wide-probe.cpp');
await writeFile(cpp,`#include <stdint.h>
typedef unsigned __int128 rep_t;
#include ${JSON.stringify(source)}
static_assert(sizeof(rep_t)==16 && sizeof(uint32_t)==4 && sizeof(uint64_t)==8,"Required integer widths");
extern "C" void wide_product(const uint32_t *a,const uint32_t *b,uint32_t *out) {
  rep_t x=0,y=0,hi,lo;
  for(unsigned i=0;i<4;++i){x|=(rep_t)a[i]<<(32*i);y|=(rep_t)b[i]<<(32*i);}
  wideMultiply(x,y,&hi,&lo);
  for(unsigned i=0;i<4;++i){out[i]=(uint32_t)(lo>>(32*i));out[i+4]=(uint32_t)(hi>>(32*i));}
}
extern "C" uint32_t *scratch(){static uint32_t values[16];return values;}
#ifndef __EMSCRIPTEN__
#include <stdio.h>
int main(){
  unsigned long long ah,al,bh,bl;
  while(scanf("%llx %llx %llx %llx",&ah,&al,&bh,&bl)==4){
    uint32_t a[4]={(uint32_t)al,(uint32_t)(al>>32),(uint32_t)ah,(uint32_t)(ah>>32)};
    uint32_t b[4]={(uint32_t)bl,(uint32_t)(bl>>32),(uint32_t)bh,(uint32_t)(bh>>32)},out[8];
    wide_product(a,b,out);
    for(int i=7;i>=0;--i)printf("%08x",out[i]);
    putchar('\\n');
  }
}
#endif
`);
const mask128=(1n<<128n)-1n,mask64=(1n<<64n)-1n;
const edges=[0n,1n,2n,mask128,mask128-1n,0xaaaaaaaabbbbbbbbccccccccddddddddn,0x55555555555555555555555555555555n];
for(let i=1n;i<128n;i+=31n){edges.push((1n<<i)-1n,1n<<i,(1n<<i)+1n);}
const cases=[];
for(const a of edges)for(const b of edges)cases.push([a,b]);
for(let i=0n;i<128n;i++)for(let j=0n;j<128n;j++)cases.push([1n<<i,1n<<j]);
let state=0x25a73e8f967bac41n;
function random64(){state^=state<<13n;state&=mask64;state^=state>>7n;state^=state<<17n;state&=mask64;return state;}
for(let i=0;i<10000;i++)cases.push([(random64()<<64n)|random64(),(random64()<<64n)|random64()]);
for(let i=0;i<4000;i++){
  const full=(random64()<<64n)|random64(),shifted=random64()<<64n;
  cases.push([full,shifted],[shifted,full]);
}
for(let i=0;i<2000;i++)cases.push([random64()<<64n,random64()<<64n]);
const nativeInput=cases.map(([a,b])=>[a>>64n,a&mask64,b>>64n,b&mask64].map(x=>x.toString(16)).join(' ')).join('\n')+'\n';
const compiler=process.env.CXX||'clang++',native=join(work,'native');
await run(compiler,['-O3','-std=c++17','-fsanitize=address,undefined','-fno-sanitize-recover=all',cpp,'-o',native]);
const nativeResults=(await run(native,[],nativeInput)).trim().split('\n');
if(nativeResults.length!==cases.length)throw new Error('Native case count mismatch');
const hashes={};
function checkResults(label,results){
  const hash=createHash('sha256');
  for(let i=0;i<cases.length;i++){
    const actual=results(i),expected=cases[i][0]*cases[i][1];
    if(actual!==expected)throw new Error(`${label} case ${i}: ${actual.toString(16)} != ${expected.toString(16)}`);
    hash.update(actual.toString(16).padStart(64,'0')+'\n');
  }
  hashes[label]=hash.digest('hex');
  console.log(`${label}: ${cases.length} exact BigInt products passed`);
}
checkResults('nativeO3Sanitized',i=>BigInt('0x'+nativeResults[i]));
const pythonDirs=await readdir(join(sdk,'python'));
const python=join(sdk,'python',pythonDirs.sort().at(-1),'bin/python3');
const emcc=join(sdk,'upstream/emscripten/emcc.py');
for(const optimization of ['O0','O3']){
  const wasm=join(work,optimization+'.wasm');
  await run(python,[emcc,'-'+optimization,'-std=c++17',cpp,'-sSTANDALONE_WASM=1','-Wl,--no-entry',
    '-sEXPORTED_FUNCTIONS=["_wide_product","_scratch"]','-o',wasm]);
  const {instance}=await WebAssembly.instantiate(await readFile(wasm),{});
  instance.exports._initialize?.();
  const pointer=instance.exports.scratch();
  const view=new Uint32Array(instance.exports.memory.buffer,pointer,16);
  checkResults('wasm'+optimization,i=>{
    let [a,b]=cases[i];
    for(let k=0;k<4;k++){view[k]=Number(a&0xffffffffn);view[k+4]=Number(b&0xffffffffn);a>>=32n;b>>=32n;}
    instance.exports.wide_product(pointer,pointer+16,pointer+32);
    let result=0n;for(let k=7;k>=0;k--)result=(result<<32n)|BigInt(view[k+8]);
    return result;
  });
}
if(new Set(Object.values(hashes)).size!==1)throw new Error('Compiler result hashes differ');
const report={schema:1,source:contract,cases:cases.length,
  corpus:{edgePairs:edges.length**2,oneHotPairs:128**2,deterministicRandomPairs:10000,
    forcedZeroLow64Pairs:10000,
    genericInputs:cases.filter(([a,b])=>(a&mask64)!==0n&&(b&mask64)!==0n).length,
    swapInputs:cases.filter(([a])=>(a&mask64)===0n).length,
    specializedInputs:cases.filter(([a,b])=>(a&mask64)===0n||(b&mask64)===0n).length},
  oracle:'JavaScript BigInt exact unbounded multiplication; unsigned raw128 inputs',hashes,
  scope:'Actual header compiled native O3 address/undefined sanitizers and wasm O0/O3; finite machine-code corpus, not proof of compiler or linked solver.'};
await mkdir(resolve(output,'..'),{recursive:true});await writeFile(output,JSON.stringify(report,null,2)+'\n');
console.log('Report: '+output);
