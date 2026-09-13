#!/usr/bin/env node
// GPL-2.0-or-later. Native reference build from the same immutable upstream pins.
import {execFile,spawn} from 'node:child_process';
import {promisify} from 'node:util';
import {createHash} from 'node:crypto';
import {mkdir,readdir,readFile,writeFile,copyFile,symlink,access,mkdtemp} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {SOURCE_PINS,EPHEMERIS,DATA_FILES} from './pins.mjs';
import {copyLockedFiles,cleanBuildEnvironment} from './build.mjs';
const capture=promisify(execFile);
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
async function run(command,args,cwd) {
  const env=cleanBuildEnvironment(process.env);
  await new Promise((yes,no)=>{
    const child=spawn(command,args,{cwd,env,stdio:'inherit',shell:false});
    const timer=setTimeout(()=>child.kill('SIGKILL'),600000);
    child.once('error',error=>{clearTimeout(timer);no(error);});
    child.once('exit',(code,signal)=>{clearTimeout(timer);code===0?yes():no(new Error(command+' failed: '+(signal||code)));});
  });
}
export async function buildNative({root=resolve('.native-engine'),ephemeris=resolve('.cache',EPHEMERIS.filename)}={}) {
  if (!['darwin','linux'].includes(process.platform)) throw new Error('Native reference supports macOS and Linux.');
  if (!/^[A-Za-z0-9_./-]+$/.test(root)||root.length>170) throw new Error('Choose a short build path without spaces.');
  await mkdir(root,{recursive:true});
  const existingData=await readdir(join(root,'data')).catch(error=>{if(error.code==='ENOENT')return [];throw error;});
  for(const name of existingData)if(!DATA_FILES.includes(name))throw new Error('Unexpected native data file: '+name+'; use a fresh --root.');
  const compileRoot=await mkdtemp(join(root,'compile-'));
  const prefix=join(compileRoot,'install'),data=join(root,'data'),sourceLock={schema:1,sources:SOURCE_PINS,files:{}};
  const installedData=new Set();
  await mkdir(prefix,{recursive:true});await mkdir(data,{recursive:true});
  for (const [name,commit] of Object.entries(SOURCE_PINS)) {
    const source=join(root,'sources',name);await mkdir(source,{recursive:true});
    if (!(await readdir(source)).length) {
      await run('git',['init',source],root);
      await run('git',['fetch','--depth','1','https://github.com/Bill-Gray/'+name+'.git',commit],source);
      await run('git',['checkout','--detach','FETCH_HEAD'],source);
    }
    if ((await capture('git',['rev-parse','HEAD'],{cwd:source})).stdout.trim()!==commit) throw new Error('Source pin mismatch: '+name);
    if ((await capture('git',['diff','HEAD','--name-only'],{cwd:source})).stdout.trim()) throw new Error('Native upstream source must be pristine: '+name);
    const tracked=(await capture('git',['ls-files','-z'],{cwd:source,maxBuffer:10000000})).stdout.split('\0').filter(Boolean);
    sourceLock.files[name]={};for(const filename of tracked)sourceLock.files[name][filename]=sha(await readFile(join(source,filename)));
    const buildSource=join(compileRoot,'sources',name);
    await copyLockedFiles(source,buildSource,sourceLock.files[name]);
    const args=['-j2','-B','PREFIX='+prefix,'NO_ERRORS=1','CC=cc','CXX=c++','CPP=c++'];
    if (name==='find_orb') {
      await run('make',[...args,'ADDED_CXXFLAGS=-UCONFIG_DIR_AUTOCOPY -fno-fast-math -ffp-contract=off','fo'],buildSource);
      await copyFile(join(buildSource,'fo'),join(root,'fo'));
      // A separately identified comparator removes only the CPU-dependent SR cap.
      const filename=join(buildSource,'orb_func.cpp'),original=await readFile(filename,'utf8');
      const from='   for( i = 0; i < max_orbits && clock( ) < end_clock; i++)';
      const to='   for( i = 0; i < max_orbits; i++)';
      if (original.split(from).length!==2) throw new Error('Count comparator patch context changed.');
      try {
        await writeFile(filename,original.replace(from,to));
        await run('make',['-j2','PREFIX='+prefix,'NO_ERRORS=1','CC=cc','CXX=c++','CPP=c++','ADDED_CXXFLAGS=-UCONFIG_DIR_AUTOCOPY -fno-fast-math -ffp-contract=off','fo'],buildSource);
        await copyFile(join(buildSource,'fo'),join(root,'fo-count'));
      } finally {await writeFile(filename,original);}
      await writeFile(join(root,'count-comparator.patch'),JSON.stringify({file:'orb_func.cpp',from,to},null,2)+'\n');
      for (const filename of DATA_FILES) {
        try {await copyFile(join(buildSource,filename),join(data,filename));installedData.add(filename);}
        catch(error) {if(error.code==='ENOENT'&&/^[a-z]findorb\.txt$/.test(filename)) continue;throw error;}
      }
    } else {
      const target={lunar:'liblunar.a',jpl_eph:'libjpl.a',sat_code:'libsatell.a'}[name];
      await run('make',[...args,target],buildSource);
      if (name==='sat_code') {
        await copyFile(join(buildSource,target),join(prefix,'lib',target));
        await copyFile(join(buildSource,'norad.h'),join(prefix,'include','norad.h'));
      } else await run('make',['PREFIX='+prefix,'CC=cc','CXX=c++','CPP=c++','install'],buildSource);
    }
  }
  // Reference and WASM share one verified download; no redundant 100 MB fetch.
  if (sha(await readFile(ephemeris))!==EPHEMERIS.sha256) throw new Error('Reference ephemeris checksum mismatch.');
  const target=join(root,EPHEMERIS.filename);
  try {await access(target);} catch {await symlink(ephemeris,target);}
  if (sha(await readFile(target))!==EPHEMERIS.sha256) throw new Error('Installed ephemeris checksum mismatch.');
  const hashes={};for(const filename of await readdir(data)) {
    if(!installedData.has(filename))throw new Error('Unexpected native data file: '+filename+'; use a fresh --root.');
    hashes[filename]=sha(await readFile(join(data,filename)));
  }
  const lockText=JSON.stringify(sourceLock,null,2)+'\n';await writeFile(join(root,'source-lock.json'),lockText);
  const macros=(await capture('c++',['-dM','-E','-x','c++','/dev/null'])).stdout;
  const longDoubleMantissaBits=Number(/^#define __LDBL_MANT_DIG__ (\d+)$/m.exec(macros)?.[1]);
  const manifest={schema:1,sources:SOURCE_PINS,sourceLockSHA256:sha(lockText),ephemeris:EPHEMERIS,dataSHA256:hashes,
    binaries:Object.fromEntries(await Promise.all(['fo','fo-count'].map(async name=>[name,sha(await readFile(join(root,name)))]))),
    compiler:(await capture('c++',['--version'])).stdout.trim(),platform:process.platform,arch:process.arch,longDoubleMantissaBits,
    numericalPolicy:'Upstream native defaults; Find_Orb -fno-fast-math -ffp-contract=off; dependency defaults (baseline policy)',
    searchPolicy:{fo:'Unmodified original upstream CPU-time-limited statistical ranging','fo-count':'Only statistical-ranging loop changed to complete configured candidate count'},
    configAutocopy:false,builtAt:new Date().toISOString()};
  await writeFile(join(root,'engine.json'),JSON.stringify(manifest,null,2)+'\n');return manifest;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const options={};for(let i=2;i<process.argv.length;i+=2) {
    const key=process.argv[i].slice(2);if(!['root','ephemeris'].includes(key)||!process.argv[i+1]) throw new Error('Usage: node build/native.mjs [--root PATH] [--ephemeris PATH]');
    options[key]=resolve(process.argv[i+1]);
  }
  await buildNative(options);
}
