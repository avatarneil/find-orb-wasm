#!/usr/bin/env node
// Standalone build: no imports from the consuming application; no global installs.
import {spawn,execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {createHash} from 'node:crypto';
import {readFile,writeFile,mkdir,readdir,copyFile,lstat,mkdtemp} from 'node:fs/promises';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {SOURCE_PINS,EPHEMERIS,DATA_FILES,EMSDK} from './pins.mjs';
import {patches} from './patches.mjs';
export const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const here=dirname(fileURLToPath(import.meta.url));
const capture=promisify(execFile);
export async function copyLockedFiles(source,target,files) {
  for (const [file,hash] of Object.entries(files)) {
    if (file.startsWith('/') || file.includes('\\') || file.split('/').some(part=>!part || part==='..' || part==='.'))
      throw new Error('Unsafe source-lock path: '+file);
    const from=join(source,file),to=join(target,file);
    const info=await lstat(from);
    if (!info.isFile()) throw new Error('Source archive integrity mismatch: '+file);
    const bytes=await readFile(from);
    if (digest(bytes)!==hash) throw new Error('Source archive integrity mismatch: '+file);
    await mkdir(dirname(to),{recursive:true});await writeFile(to,bytes,{mode:info.mode&0o777});
  }
}
export function cleanBuildEnvironment(input) {
  const env={...input};
  for (const key of Object.keys(env)) if (key.endsWith('FLAGS') || key.startsWith('EMCC_') ||
    /^(CC|CXX|CPP|LD|AR|RANLIB|NM|MAKEFILES|MAKEOVERRIDES|MAKELEVEL|CPATH|C_INCLUDE_PATH|CPLUS_INCLUDE_PATH|LIBRARY_PATH)$/.test(key)) delete env[key];
  return env;
}
export async function run(command,args,cwd,env=process.env) {
  await new Promise((yes,no) => {
    const child=spawn(command,args,{cwd,env,stdio:'inherit',shell:false});
    const timer=setTimeout(() => child.kill('SIGKILL'),600000);
    child.once('error',e => {clearTimeout(timer); no(e);});
    child.once('exit',(code,signal) => {clearTimeout(timer); code===0 ? yes() : no(new Error(command+' failed: '+(signal || code)));});
  });
}
export async function build({sdk,work,dist,ephemeris,sources}) {
  for (const path of [sdk,work,dist,...(sources?[sources]:[])]) if (!/^[A-Za-z0-9_./-]+$/.test(path) || path.length>170) throw new Error('Use short paths without spaces; upstream makefiles do not quote paths.');
  await mkdir(work,{recursive:true});
  let sourceLock={schema:1,sources:SOURCE_PINS,patchesSHA256:digest(JSON.stringify(patches)),files:{}};
  if (sources) {
    if (!ephemeris) throw new Error('An offline source rebuild requires --ephemeris with the pinned full DE440 file.');
    if ((await readdir(work)).length) throw new Error('Use an empty --work directory for an archive rebuild.');
    sourceLock=JSON.parse(await readFile(join(sources,'../source-lock.json'),'utf8'));
    if (sourceLock.schema!==1 || JSON.stringify(sourceLock.sources)!==JSON.stringify(SOURCE_PINS) ||
        sourceLock.patchesSHA256!==digest(JSON.stringify(patches))) throw new Error('Source archive revision/patch mismatch.');
    for (const name of Object.keys(SOURCE_PINS)) {
      const files=sourceLock.files?.[name];
      if (!files || !Object.keys(files).length) throw new Error('Incomplete source archive lock.');
      await copyLockedFiles(join(sources,name),join(work,'sources',name),files);
    }
  }
  const em=join(sdk,'upstream/emscripten');
  // Emscripten requires Python 3.10+. Prefer its locally installed interpreter
  // even when the system python3 is Apple's older version.
  const sdkPython=join(sdk,'python/3.13.3_64bit/bin/python3');
  const env={...cleanBuildEnvironment(process.env),PATH:em+':'+process.env.PATH,SOURCE_DATE_EPOCH:'1788998400',TZ:'UTC',LC_ALL:'C',EM_CONFIG:join(sdk,'.emscripten')};
  // Inherited make/compiler options must not override the recorded FP policy
  // or add unrecorded headers, object files, or makefiles to the build.
  try {await readFile(sdkPython);env.EMSDK_PYTHON=sdkPython;} catch { /* Linux SDK can use the host Python. */ }
  await run(join(em,'emcc'),['--version'],work,env);
  const version=await readFile(join(em,'emscripten-version.txt'),'utf8');
  if (version.trim().replaceAll('"','')!==EMSDK.version) throw new Error('Emscripten '+EMSDK.version+' is required.');
  const compileRoot=await mkdtemp(join(work,'compile-'));
  const prefix=join(compileRoot,'install'); await mkdir(prefix,{recursive:true});
  const strictFP=' -fno-fast-math -ffp-contract=off';
  for (const [name,commit] of Object.entries(SOURCE_PINS)) {
    const source=join(work,'sources',name);
    await mkdir(source,{recursive:true});
    if (!sources) {
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
    const tracked=(await capture('git',['ls-files','-z'],{cwd:source,maxBuffer:10000000})).stdout.split('\0').filter(Boolean);
    sourceLock.files[name]={};
    for (const file of tracked) sourceLock.files[name][file]=digest(await readFile(join(source,file)));
    }
    // Compile only the checked input files in a fresh tree. ar's replacement
    // mode otherwise retains foreign archive members even with make -B.
    const buildSource=join(compileRoot,'sources',name);
    await copyLockedFiles(source,buildSource,sourceLock.files[name]);
    const args=['-j2','-B','PREFIX='+prefix,'NO_ERRORS=1','CC='+join(em,'emcc')+strictFP,'CXX='+join(em,'em++')+strictFP,
      'CPP='+join(em,'em++')+strictFP,'LIBEXE='+join(em,'emar')];
    if (name==='find_orb') {
      const flags=['-O3','-g2','-sMODULARIZE=1','-sEXPORT_NAME=createFindOrb','-sENVIRONMENT=worker,node',
        '-sEXPORTED_RUNTIME_METHODS=FS,callMain','-sALLOW_MEMORY_GROWTH=1','-sMAXIMUM_MEMORY=536870912',
        '-sSTACK_SIZE=8388608','-sINITIAL_MEMORY=33554432','-sEXIT_RUNTIME=1','-sFORCE_FILESYSTEM=1',
        '-sASSERTIONS=1','-sSTACK_OVERFLOW_CHECK=2',join(here,'platform.cpp')];
      await run('make',[...args,'ADDED_CXXFLAGS=-UCONFIG_DIR_AUTOCOPY -ffp-contract=off',
        'FO_EXE=fo.js','LDFLAGS='+flags.join(' '),'fo.js'],buildSource,env);
    } else {
      const target=name==='lunar' ? 'liblunar.a' : name==='jpl_eph' ? 'libjpl.a' : 'libsatell.a';
      await run('make',[...args,target],buildSource,env);
      if (name==='sat_code') {
        await copyFile(join(buildSource,target),join(prefix,'lib',target));
        await copyFile(join(buildSource,'norad.h'),join(prefix,'include/norad.h'));
      } else await run('make',[...args,'install'],buildSource,env);
    }
  }
  await mkdir(dist,{recursive:true});
  const lockText=JSON.stringify(sourceLock,null,2)+'\n';
  await writeFile(join(dist,'source-lock.json'),lockText);
  const notices=join(dist,'licenses');await mkdir(notices,{recursive:true});
  for (const name of await readdir(join(here,'../licenses'))) await copyFile(join(here,'../licenses',name),join(notices,name));
  for (const name of ['NOTICE','LICENSE','provenance.json']) await copyFile(join(here,'..',name),join(dist,name));
  for (const [from,to] of [
    ['LICENSE','Emscripten-LICENSE.txt'],['AUTHORS','Emscripten-AUTHORS.txt'],
    ['system/lib/libc/musl/COPYRIGHT','musl-COPYRIGHT.txt'],
    ['system/lib/compiler-rt/LICENSE.TXT','compiler-rt-LICENSE.txt'],
    ['system/lib/libcxx/LICENSE.TXT','libcxx-LICENSE.txt'],
    ['system/lib/libcxxabi/LICENSE.TXT','libcxxabi-LICENSE.txt'],
    ['system/lib/libunwind/LICENSE.TXT','libunwind-LICENSE.txt'],
    ['system/lib/llvm-libc/LICENSE.TXT','llvm-libc-LICENSE.txt'],
  ]) await copyFile(join(em,from),join(notices,to));
  const source=join(compileRoot,'sources/find_orb'), data={};
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
  const manifest={schema:1,sources:SOURCE_PINS,sourceLockSHA256:digest(lockText),ephemeris:EPHEMERIS,emscripten:EMSDK,
    binarySHA256:digest(wasm),glueSHA256:digest(glue),dataSHA256:data,entries,
    pack:{filename:'find-orb.data',size:pack.length,sha256:digest(pack)},
    numericalPolicy:'wasm32; binary64 double, software binary128 long double; no fast-math; fp-contract=off in all four source projects',
    strictEphemeris:true,ephemerisPolicy:'required; actual JPL queries fail closed outside (start, end] or on evaluation error',
    referenceMount:'copy-on-write MEMFS; fresh module, heap and filesystem per command',
    compilationPolicy:'One retained immutable WebAssembly.Module per worker; fresh instance, imports, globals and memory per command',
    patchesSHA256:digest(await readFile(join(here,'patches.mjs'))),strictEphemerisPatchesSHA256:digest(await readFile(join(here,'../data/patches.mjs'))),platformSHA256:digest(await readFile(join(here,'platform.cpp'))),
    searchPolicy:'Complete configured statistical-ranging candidate count; external worker timeout rejects incomplete jobs',configAutocopy:false};
  const workerSource='const FIND_ORB_MANIFEST='+JSON.stringify(manifest)+';\nconst FIND_ORB_WASM_BASE64='+JSON.stringify(wasm.toString('base64'))+';\n'+
    glue.toString()+'\n'+await readFile(join(here,'../src/runtime.js'),'utf8')+'\n'+await readFile(join(here,'../src/worker.js'),'utf8');
  manifest.workerSHA256=digest(workerSource);
  await writeFile(join(dist,'find-orb-worker.js'),workerSource);
  await writeFile(join(dist,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
  // Include our complete build recipe/runtime alongside patched upstream source.
  // Omit build products and git metadata, never the corresponding source files.
  const developmentSources=[];
  for (const path of ['benchmark','verification','scripts','tests','docs','results','package-lock.json','playwright.config.mjs']) {
    try {await lstat(join(here,'..',path));developmentSources.push(path);} catch(error) {if(error.code!=='ENOENT')throw error;}
  }
  await run('tar',['-czf',join(dist,'corresponding-source.tar.gz'),'--exclude=.git','--exclude=*.o','--exclude=*.a',
    '--exclude=fo.js','--exclude=fo.wasm','--exclude=__pycache__','--exclude=results/local','--exclude=*.cpuprofile',
    '-C',compileRoot,'sources','-C',join(here,'..'),'build','src','data','package.json','README.md','LICENSE','NOTICE','provenance.json','EMSCRIPTEN-LICENSE.txt',...developmentSources,
    '-C',dist,'licenses','source-lock.json'],work);
  console.log('Built WebAssembly: '+wasm.length+' bytes WASM, '+pack.length+' bytes data.');
  return manifest;
}
if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const options={sdk:resolve('.wasm-toolchain'),work:resolve('.wasm-engine'),dist:resolve(here,'../dist')};
  for (let i=2;i<process.argv.length;i+=2) {
    const key=process.argv[i].slice(2);
    if (!['sdk','work','dist','ephemeris','sources'].includes(key) || !process.argv[i+1]) throw new Error('Options: --sdk --work --dist --ephemeris --sources (paths).');
    options[key]=resolve(process.argv[i+1]);
  }
  await build(options);
}
