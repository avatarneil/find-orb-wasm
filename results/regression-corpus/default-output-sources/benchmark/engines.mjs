// GPL-2.0-or-later. Measure the built runtime, including fresh-job isolation.
import {readFile,writeFile,mkdir,mkdtemp,rm,readdir} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {spawn} from 'node:child_process';
import {createHash} from 'node:crypto';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import vm from 'node:vm';
import assert from 'node:assert/strict';
import {SOURCE_PINS,EPHEMERIS} from '../build/pins.mjs';
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const now=()=>performance.now();
export async function loadWasm(directory,{retainModule=false,prepareRuntime=true}={}) {
  const start=now(),root=resolve(directory);
  const manifest=JSON.parse(await readFile(join(root,'manifest.json'),'utf8'));
  const data=await readFile(join(root,manifest.pack.filename)),pack=data.buffer.slice(data.byteOffset,data.byteOffset+data.byteLength);
  const wasm=await readFile(join(root,'fo.wasm')),glue=await readFile(join(root,'fo.cjs'));
  const worker=await readFile(join(root,'find-orb-worker.js'),'utf8');
  if(hash(glue)!==manifest.glueSHA256||hash(worker)!==manifest.workerSHA256) throw new Error('Built glue/worker snapshot checksum mismatch.');
  const begin=worker.indexOf('/* GPL-2.0-or-later. Portable low-level runtime'),end=worker.indexOf('/* Appended to pinned compiler glue');
  if(begin<0||end<=begin) throw new Error('Cannot locate built runtime snapshot.');
  // Compile the unchanged embedded runtime in this realm so binary views retain
  // their constructors. Avoid evaluating the unrelated worker event loop.
  const context={exports:{}};
  vm.compileFunction(worker.slice(begin,end),['module','crypto','WebAssembly'])(context,globalThis.crypto,globalThis.WebAssembly);
  const runtime=context.exports,factory=createRequire(import.meta.url)(join(root,'fo.cjs'));
  const readMs=now()-start,verifyStart=now();await runtime.verify(manifest,pack,wasm);
  const setup={readMs,verifyMs:now()-verifyStart,totalMs:now()-start};
  let preparedFactory=factory;
  if(typeof runtime.prepare==='function'&&!retainModule&&prepareRuntime) {
    const start=now();preparedFactory=await runtime.prepare(factory,wasm);
    setup.compileModuleMs=now()-start;setup.totalMs+=setup.compileModuleMs;
  }
  let compiledModule=null;
  if(retainModule){const start=now();compiledModule=await WebAssembly.compile(wasm);setup.compileModuleMs=now()-start;setup.totalMs+=setup.compileModuleMs;}
  let timing=null;
  // Stable factory identity preserves any runtime compilation cache. Each call
  // still creates a fresh module instance, as the distribution runtime requests.
  const instrumented=async options=>{
    const instance=await preparedFactory(compiledModule?{...options,instantiateWasm(imports,receive){
      const instance=new WebAssembly.Instance(compiledModule,imports);receive(instance,compiledModule);return instance.exports;
    }}:options);timing.instantiated=now();
    const callMain=instance.callMain;
    instance.callMain=(...args)=>{timing.mounted=now();try{return callMain(...args);}finally{timing.solved=now();}};
    return instance;
  };
  return {id:retainModule?'wasm-retained-module':'wasm',root,manifest,setup,pack,wasm,
    async execute(command) {
      if(timing)throw new Error('Benchmark loader runs one command at a time.');
      const begin=now();timing={};
      try {
        const result=await runtime.execute(instrumented,manifest,pack,wasm,command.args,command.files,command.outputs);
        const end=now(),{instantiated,mounted,solved}=timing;
        return {...result,phases:{instantiateMs:instantiated-begin,mountMs:mounted-instantiated,solveMs:solved-mounted,collectMs:end-solved,totalMs:end-begin}};
      } finally {timing=null;}
    }};
}
export async function loadNative(directory,binary='fo-count') {
  const root=resolve(directory),manifest=JSON.parse(await readFile(join(root,'engine.json'),'utf8'));
  assert.deepEqual(manifest.sources,SOURCE_PINS,'pinned native sources');
  assert.deepEqual(manifest.ephemeris,EPHEMERIS,'pinned native ephemeris');
  if(manifest.sourceLockSHA256&&hash(await readFile(join(root,'source-lock.json')))!==manifest.sourceLockSHA256)throw new Error('Native source-lock checksum mismatch.');
  if(hash(await readFile(join(root,binary)))!==manifest.binaries[binary]) throw new Error('Native binary checksum mismatch.');
  if(hash(await readFile(join(root,EPHEMERIS.filename)))!==EPHEMERIS.sha256)throw new Error('Native ephemeris checksum mismatch.');
  assert.deepEqual((await readdir(join(root,'data'))).sort(),Object.keys(manifest.dataSHA256).sort(),'no extra native reference data');
  const dataFiles={};
  for(const [name,expected]of Object.entries(manifest.dataSHA256)) {
    if(!/^[A-Za-z0-9_.-]+$/.test(name)||name.includes('..'))throw new Error('Invalid native data path: '+name);
    const bytes=await readFile(join(root,'data',name));
    if(hash(bytes)!==expected)throw new Error('Native data checksum mismatch: '+name);
    dataFiles[name]=bytes;
  }
  return {id:binary==='fo'?'native-original':'native-count',root,manifest,binary,
    async execute(command) {
      const start=now(),directory=await mkdtemp(join(tmpdir(),'find-orb-benchmark-'));
      const nativeData=join(directory,'engine-data');
      const translate=text=>text.replaceAll('/engine/data/',nativeData+'/').replaceAll('/engine/',root+'/').replaceAll('/job/',directory+'/');
      try {
        // Upstream can write sof.txt beside -x data despite -O and -i. Clone
        // verified inputs for every process so a prior fit never contaminates it.
        await mkdir(nativeData);
        await Promise.all(Object.entries(dataFiles).map(([name,bytes])=>writeFile(join(nativeData,name),bytes)));
        for(const path of command.outputs.filter(name=>name.endsWith('/'))) await mkdir(translate(path),{recursive:true});
        for(const [name,text] of Object.entries(command.files)) await writeFile(translate(name),translate(text));
        const mounted=now();let stdout='';
        await new Promise((yes,no)=>{
          const child=spawn(join(root,binary),command.args.map(translate),{cwd:directory,stdio:['ignore','pipe','pipe'],shell:false});
          const timer=setTimeout(()=>child.kill('SIGKILL'),120000);
          for(const stream of [child.stdout,child.stderr]) stream.on('data',chunk=>{stdout+=chunk;if(stdout.length>1000000)child.kill('SIGKILL');});
          child.once('error',error=>{clearTimeout(timer);no(error);});
          child.once('close',(code,signal)=>{clearTimeout(timer);code===0?yes():no(new Error('Native failed '+(signal||code)+': '+stdout.slice(-3000)));});
        });
        const solved=now(),files={};
        for(const name of command.outputs) {
          if(name.endsWith('/')) {
            for(const child of await readdir(translate(name))) files[name+child]=await readFile(translate(name+child),'utf8');
          } else files[name]=await readFile(translate(name),'utf8');
        }
        const end=now();return {files,stdout,exitCode:0,phases:{mountMs:mounted-start,processAndSolveMs:solved-mounted,collectMs:end-solved,totalMs:end-start}};
      } finally {await rm(directory,{recursive:true,force:true});}
    }};
}
