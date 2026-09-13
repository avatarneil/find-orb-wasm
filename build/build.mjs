#!/usr/bin/env node
// Standalone build: no imports from the consuming application; no global installs.
import {spawn,execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {createHash} from 'node:crypto';
import {readFile,writeFile,mkdir,readdir,copyFile} from 'node:fs/promises';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {SOURCE_PINS,EPHEMERIS,DATA_FILES,EMSDK} from './pins.mjs';
import {patches} from './patches.mjs';
export const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const here=dirname(fileURLToPath(import.meta.url));
const capture=promisify(execFile);
export async function run(command,args,cwd,env=process.env) {
  await new Promise((yes,no) => {
    const child=spawn(command,args,{cwd,env,stdio:'inherit',shell:false});
    const timer=setTimeout(() => child.kill('SIGKILL'),600000);
    child.once('error',e => {clearTimeout(timer); no(e);});
    child.once('exit',(code,signal) => {clearTimeout(timer); code===0 ? yes() : no(new Error(command+' failed: '+(signal || code)));});
  });
}
export async function build({sdk,work,dist,ephemeris}) {
  for (const path of [sdk,work,dist]) if (!/^[A-Za-z0-9_./-]+$/.test(path) || path.length>170) throw new Error('Use short paths without spaces; upstream makefiles do not quote paths.');
  await mkdir(work,{recursive:true});
  const em=join(sdk,'upstream/emscripten');
  await run(join(em,'emcc'),['--version'],work);
  const version=await readFile(join(em,'emscripten-version.txt'),'utf8');
  if (version.trim().replaceAll('"','')!==EMSDK.version) throw new Error('Emscripten '+EMSDK.version+' is required.');
  const prefix=join(work,'install'); await mkdir(prefix,{recursive:true});
  const env={...process.env,PATH:em+':'+process.env.PATH,SOURCE_DATE_EPOCH:'1788998400',TZ:'UTC',LC_ALL:'C'};
  for (const [name,commit] of Object.entries(SOURCE_PINS)) {
    const source=join(work,'sources',name);
    await mkdir(source,{recursive:true});
    if (!(await readdir(source)).length) {
      await run('git',['init',source],work);
      await run('git',['fetch','--depth','1','https://github.com/Bill-Gray/'+name+'.git',commit],source);
      await run('git',['checkout','--detach','FETCH_HEAD'],source);
      // Some upstream makefiles hard-code ar; emar must index wasm objects.
      const makefile=join(source,'makefile');
      await writeFile(makefile,(await readFile(makefile,'utf8')).replace(/\tar /g,'\temar '));
    }
    const head=(await capture('git',['rev-parse','HEAD'],{cwd:source})).stdout.trim();
    if (head!==commit) throw new Error('Source revision mismatch: '+name);
    if (name==='find_orb') for (const patch of patches) {
      const file=join(source,patch.file),original=await readFile(file,'utf8');
      if (original.includes(patch.to)) continue;
      if (original.split(patch.from).length!==2) throw new Error('Upstream patch context changed: '+patch.file);
      await writeFile(file,original.replace(patch.from,patch.to));
    }
    const changed=(await capture('git',['diff','HEAD','--name-only'],{cwd:source})).stdout.trim().split('\n').filter(Boolean);
    for (const file of changed) {
      let expected=(await capture('git',['show','HEAD:'+file],{cwd:source,maxBuffer:10000000})).stdout;
      if (file==='makefile') expected=expected.replace(/\tar /g,'\temar ');
      if (name==='find_orb') for (const patch of patches.filter(p => p.file===file)) expected=expected.replace(patch.from,patch.to);
      if (await readFile(join(source,file),'utf8')!==expected) throw new Error('Unexpected modified source: '+name+'/'+file+'; use a fresh --work directory.');
    }
    // Rebuild dependencies too; never trust stale or foreign .o/.a files.
    const args=['-j2','-B','PREFIX='+prefix,'NO_ERRORS=1','CC='+join(em,'emcc'),'CXX='+join(em,'em++'),
      'CPP='+join(em,'em++'),'LIBEXE='+join(em,'emar')];
    if (name==='find_orb') {
      const flags=['-O3','-g2','-sMODULARIZE=1','-sEXPORT_NAME=createFindOrb','-sENVIRONMENT=worker,node',
        '-sEXPORTED_RUNTIME_METHODS=FS,callMain','-sALLOW_MEMORY_GROWTH=1','-sMAXIMUM_MEMORY=536870912',
        '-sSTACK_SIZE=8388608','-sINITIAL_MEMORY=33554432','-sEXIT_RUNTIME=1','-sFORCE_FILESYSTEM=1',
        '-sASSERTIONS=1','-sSTACK_OVERFLOW_CHECK=2',join(here,'platform.cpp')];
      await run('make',[...args,'ADDED_CXXFLAGS=-UCONFIG_DIR_AUTOCOPY -ffp-contract=off',
        'FO_EXE=fo.js','LDFLAGS='+flags.join(' '),'fo.js'],source,env);
    } else {
      const target=name==='lunar' ? 'liblunar.a' : name==='jpl_eph' ? 'libjpl.a' : 'libsatell.a';
      await run('make',[...args,target],source,env);
      if (name==='sat_code') {
        await copyFile(join(source,target),join(prefix,'lib',target));
        await copyFile(join(source,'norad.h'),join(prefix,'include/norad.h'));
      } else await run('make',[...args,'install'],source,env);
    }
  }
  await mkdir(dist,{recursive:true});
  const notices=join(dist,'licenses');await mkdir(notices,{recursive:true});
  for (const [from,to] of [
    ['LICENSE','Emscripten-LICENSE.txt'],['AUTHORS','Emscripten-AUTHORS.txt'],
    ['system/lib/libc/musl/COPYRIGHT','musl-COPYRIGHT.txt'],
    ['system/lib/compiler-rt/LICENSE.TXT','compiler-rt-LICENSE.txt'],
    ['system/lib/libcxx/LICENSE.TXT','libcxx-LICENSE.txt'],
    ['system/lib/libcxxabi/LICENSE.TXT','libcxxabi-LICENSE.txt'],
    ['system/lib/libunwind/LICENSE.TXT','libunwind-LICENSE.txt'],
    ['system/lib/llvm-libc/LICENSE.TXT','llvm-libc-LICENSE.txt'],
  ]) await copyFile(join(em,from),join(notices,to));
  const source=join(work,'sources/find_orb'), data={};
  const chunks=[], entries={}; let offset=0;
  function add(name,bytes) {
    entries[name]={offset,size:bytes.length,sha256:digest(bytes)}; offset+=bytes.length; chunks.push(bytes);
  }
  for (const name of DATA_FILES) {
    let bytes; try {bytes=await readFile(join(source,name));}
    catch (e) {if (e.code==='ENOENT' && /^[a-z]findorb\.txt$/.test(name)) continue; throw e;}
    data[name]=digest(bytes); add('data/'+name,bytes);
  }
  let eph;
  if (ephemeris) eph=await readFile(ephemeris);
  else {
    const response=await fetch(EPHEMERIS.url,{signal:AbortSignal.timeout(180000)});
    if (!response.ok) throw new Error('DE440 download failed: '+response.status);
    eph=Buffer.from(await response.arrayBuffer());
  }
  if (digest(eph)!==EPHEMERIS.sha256) throw new Error('DE440 checksum mismatch.');
  add(EPHEMERIS.filename,eph);
  const pack=Buffer.concat(chunks); await writeFile(join(dist,'find-orb.data'),pack);
  for (const name of ['fo.js','fo.wasm']) await copyFile(join(source,name),join(dist,name));
  await copyFile(join(source,'fo.js'),join(dist,'fo.cjs'));
  const wasm=await readFile(join(dist,'fo.wasm')), glue=await readFile(join(dist,'fo.js'));
  const manifest={schema:1,sources:SOURCE_PINS,ephemeris:EPHEMERIS,emscripten:EMSDK,
    binarySHA256:digest(wasm),glueSHA256:digest(glue),dataSHA256:data,entries,
    pack:{filename:'find-orb.data',size:pack.length,sha256:digest(pack)},
    numericalPolicy:'wasm32; binary64 double, software binary128 long double; no fast-math; fp-contract=off in Find_Orb',
    patchesSHA256:digest(await readFile(join(here,'patches.mjs'))),platformSHA256:digest(await readFile(join(here,'platform.cpp'))),
    searchPolicy:'Complete configured statistical-ranging candidate count; external worker timeout rejects incomplete jobs',configAutocopy:false};
  const workerSource='const FIND_ORB_MANIFEST='+JSON.stringify(manifest)+';\nconst FIND_ORB_WASM_BASE64='+JSON.stringify(wasm.toString('base64'))+';\n'+
    glue.toString()+'\n'+await readFile(join(here,'../src/runtime.js'),'utf8')+'\n'+await readFile(join(here,'../src/worker.js'),'utf8');
  manifest.workerSHA256=digest(workerSource);
  await writeFile(join(dist,'find-orb-worker.js'),workerSource);
  await writeFile(join(dist,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
  // Include our complete build recipe/runtime alongside patched upstream source.
  // Omit build products and git metadata, never the corresponding source files.
  await run('tar',['-czf',join(dist,'corresponding-source.tar.gz'),'--exclude=.git','--exclude=*.o','--exclude=*.a',
    '--exclude=fo.js','--exclude=fo.wasm','-C',work,'sources','-C',join(here,'..'),'build','src','package.json','README.md','LICENSE','EMSCRIPTEN-LICENSE.txt',
    '-C',dist,'licenses'],work);
  console.log('Built WebAssembly: '+wasm.length+' bytes WASM, '+pack.length+' bytes data.');
  return manifest;
}
if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const options={sdk:resolve('.wasm-toolchain'),work:resolve('.wasm-engine'),dist:resolve(here,'../dist')};
  for (let i=2;i<process.argv.length;i+=2) {
    const key=process.argv[i].slice(2);
    if (!['sdk','work','dist','ephemeris'].includes(key) || !process.argv[i+1]) throw new Error('Options: --sdk --work --dist --ephemeris (paths).');
    options[key]=resolve(process.argv[i+1]);
  }
  await build(options);
}
