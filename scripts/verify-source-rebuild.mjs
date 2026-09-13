#!/usr/bin/env node
// GPL-2.0-or-later. Rebuild the archived recipe using only local inputs.
import {spawn,execFile} from 'node:child_process';
import {createHash} from 'node:crypto';
import {createReadStream} from 'node:fs';
import {readFile,writeFile,mkdir,mkdtemp,open,stat,access,rm,rename} from 'node:fs/promises';
import {join,resolve,dirname,delimiter} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {promisify} from 'node:util';
import {isDeepStrictEqual} from 'node:util';
import {SOURCE_PINS,EPHEMERIS,EMSDK} from '../build/pins.mjs';
import {patches} from '../build/patches.mjs';

const ROOT=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const ARTIFACTS=['fo.wasm','fo.js','find-orb-worker.js','find-orb.data','manifest.json','source-lock.json'];
const RECIPES=['build/build.mjs','build/pins.mjs','build/patches.mjs','build/platform.cpp',
  'data/patches.mjs','src/runtime.js','src/worker.js','scripts/verify-source-rebuild.mjs'];
const capture=promisify(execFile);
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const require=(condition,message)=>{if(!condition)throw new Error(message);};

async function hashFile(path) {
  const hash=createHash('sha256');
  for await(const chunk of createReadStream(path)) hash.update(chunk);
  return hash.digest('hex');
}

async function hashes(base,names) {
  return Object.fromEntries(await Promise.all(names.map(async name=>[name,await hashFile(join(base,name))])));
}

async function equalFiles(left,right) {
  const a=await open(left,'r'),b=await open(right,'r');
  try {
    const length=(await a.stat()).size;
    if(length!==(await b.stat()).size)return false;
    const ba=Buffer.alloc(65536),bb=Buffer.alloc(65536);
    for(let position=0;position<length;position+=ba.length) {
      const count=Math.min(ba.length,length-position);
      const [ra,rb]=await Promise.all([a.read(ba,0,count,position),b.read(bb,0,count,position)]);
      require(ra.bytesRead===count&&rb.bytesRead===count,'Short read during artifact comparison');
      if(!ba.subarray(0,count).equals(bb.subarray(0,count)))return false;
    }
    return true;
  } finally {await a.close();await b.close();}
}

async function save(path,report) {
  const temporary=path+'.tmp-'+process.pid;
  await writeFile(temporary,JSON.stringify(report,null,2)+'\n');
  await rename(temporary,path);
}

async function execute(command,args,{cwd,env,log,timeout=1200000}) {
  const file=await open(log,'w');
  const start=performance.now();
  try {
    const outcome=await new Promise((yes,no)=>{
      const child=spawn(command,args,{cwd,env,stdio:['ignore',file.fd,file.fd],shell:false});
      const timer=setTimeout(()=>child.kill('SIGKILL'),timeout);
      child.once('error',error=>{clearTimeout(timer);no(error);});
      child.once('close',(code,signal)=>{clearTimeout(timer);yes({exitCode:code,signal});});
    });
    require(outcome.exitCode===0,`${command} failed (${outcome.signal??outcome.exitCode}); see ${log}`);
    return {...outcome,elapsedMs:performance.now()-start};
  } finally {await file.close();}
}

async function offlineEnvironment(base,directory) {
  const bin=join(directory,'bin');
  await mkdir(bin,{recursive:true});
  const attemptLog=join(directory,'network-attempts.jsonl');
  const nodeGuard=join(directory,'deny-network.mjs');
  await writeFile(nodeGuard,`import fs from 'node:fs';
import http from 'node:http'; import https from 'node:https'; import net from 'node:net';
import tls from 'node:tls'; import dns from 'node:dns'; import {syncBuiltinESMExports} from 'node:module';
const deny=(...args)=>{fs.appendFileSync(process.env.REBUILD_NETWORK_LOG,JSON.stringify({runtime:'node',args:args.map(String)})+'\\n');throw new Error('Network access is forbidden during source rebuild');};
globalThis.fetch=deny;
for(const module of [http,https]) {module.request=deny;module.get=deny;}
net.connect=deny;net.createConnection=deny;net.Socket.prototype.connect=deny;tls.connect=deny;
dns.lookup=deny;dns.resolve=deny;dns.promises.lookup=deny;dns.promises.resolve=deny;
syncBuiltinESMExports();\n`);
  await writeFile(join(directory,'sitecustomize.py'),`import json, os, socket
def deny(*args, **kwargs):
    with open(os.environ['REBUILD_NETWORK_LOG'], 'a') as stream:
        stream.write(json.dumps({'runtime':'python','args':repr(args)})+'\\n')
    raise RuntimeError('Network access is forbidden during source rebuild')
socket.socket.connect=deny
socket.socket.connect_ex=deny
socket.create_connection=deny
socket.getaddrinfo=deny
socket.gethostbyname=deny
`);
  for(const name of ['git','curl','wget']) await writeFile(join(bin,name),`#!${process.execPath}
import fs from 'node:fs';
fs.appendFileSync(process.env.REBUILD_NETWORK_LOG,JSON.stringify({tool:${JSON.stringify(name)},args:process.argv.slice(2)})+'\\n');
console.error('Git/download tools are forbidden during source rebuild');process.exit(78);
`,{mode:0o755});
  const env={...base};
  for(const key of Object.keys(env)) if(key.endsWith('FLAGS')||key.startsWith('EMCC_')||key.startsWith('EM_')||
    /^(CC|CXX|CPP|LD|AR|RANLIB|NM|MAKEFILES|MAKEOVERRIDES|MAKELEVEL|CPATH|C_INCLUDE_PATH|CPLUS_INCLUDE_PATH|LIBRARY_PATH|LD_PRELOAD|DYLD_INSERT_LIBRARIES|NODE_OPTIONS|PYTHONPATH|PYTHONHOME)$/.test(key))delete env[key];
  Object.assign(env,{PATH:bin+delimiter+base.PATH,PYTHONPATH:directory,
    NODE_OPTIONS:'--import='+pathToFileURL(nodeGuard).href,REBUILD_NETWORK_LOG:attemptLog,
    EM_FROZEN_CACHE:'1',PYTHONNOUSERSITE:'1',GIT_CONFIG_NOSYSTEM:'1'});
  return {env,attemptLog,nodeGuard};
}

async function checkOfflineGuards({env,attemptLog},python,cwd) {
  const controls=[
    ['node-network',process.execPath,['-e',"fetch('data:text/plain,offline-test')"]],
    ['python-network',python,['-c',"import socket; socket.getaddrinfo('localhost', 0)"]],
    ['git-executable','git',['--version']],
  ];
  const result=[];
  for(const [name,command,args] of controls) {
    let rejected=false;
    try {await capture(command,args,{cwd,env,timeout:20000,maxBuffer:1024*1024});}
    catch(error) {
      rejected=typeof error.code==='number'&&error.code!==0&&/forbidden during source rebuild/.test(error.stderr??'');
    }
    require(rejected,'Offline guard negative control failed: '+name);
    result.push({name,rejected:true});
  }
  const attempts=(await readFile(attemptLog,'utf8')).trim().split('\n').map(line=>JSON.parse(line));
  require(attempts.length===3,'Offline guards did not log exactly the three intentional tests');
  await writeFile(join(cwd,'offline-guard-tests.json'),JSON.stringify(attempts,null,2)+'\n');
  await rm(attemptLog);
  return result;
}

const EXTRACT_SCRIPT=`import json, pathlib, sys, tarfile
archive, destination = sys.argv[1:]
with tarfile.open(archive, 'r:gz') as handle:
    members = handle.getmembers()
    for member in members:
        path = pathlib.PurePosixPath(member.name)
        if path.is_absolute() or '..' in path.parts or '\\\\' in member.name:
            raise ValueError('Unsafe archive path: '+member.name)
        if not (member.isfile() or member.isdir()):
            raise ValueError('Archive links/devices are not permitted: '+member.name)
    handle.extractall(destination, members=members, filter='data')
print(json.dumps({'membersChecked':len(members),'linksAndDevicesAllowed':False}))
`;

export async function verifySourceRebuild({dist=join(ROOT,'dist'),sdk=join(ROOT,'.wasm-toolchain'),
  ephemeris=join(ROOT,'.cache',EPHEMERIS.filename),output=join(ROOT,'results/research-source-rebuild.json')}={}) {
  [dist,sdk,ephemeris,output]=[dist,sdk,ephemeris,output].map(path=>resolve(path));
  const archive=join(dist,'corresponding-source.tar.gz');
  require(![archive,ephemeris,...ARTIFACTS.map(name=>join(dist,name))].includes(output),'Report path must not overwrite a rebuild input');
  await mkdir(dirname(output),{recursive:true});
  // Remove a prior success before any input validation, extraction or build.
  await rm(output,{force:true});
  const report={schema:1,passed:false,status:'running',startedAt:new Date().toISOString(),
    scope:'Byte-for-byte reproduction of six distribution artifacts from the archived corresponding source and archived build recipe',
    archive,dist,sdk,ephemeris,artifacts:ARTIFACTS};
  await save(output,report);
  try {
    const manifest=JSON.parse(await readFile(join(dist,'manifest.json'),'utf8'));
    const sourceLock=JSON.parse(await readFile(join(dist,'source-lock.json'),'utf8'));
    require(isDeepStrictEqual(manifest.sources,SOURCE_PINS)&&isDeepStrictEqual(sourceLock.sources,SOURCE_PINS),'Current distribution source pins do not match this checkout');
    require(isDeepStrictEqual(manifest.emscripten,EMSDK),'Current distribution SDK pin mismatch');
    require(sourceLock.patchesSHA256===sha(JSON.stringify(patches)),'Current source-lock patch ID mismatch');
    report.archiveSHA256=await hashFile(archive);
    report.archiveBytes=(await stat(archive)).size;
    report.inputSHA256=await hashes(dist,ARTIFACTS);
    report.currentRecipeSHA256=await hashes(ROOT,RECIPES);
    report.ephemerisSHA256=await hashFile(ephemeris);
    require(report.ephemerisSHA256===EPHEMERIS.sha256,'Local ephemeris is not the pinned full DE440');
    require(report.inputSHA256['fo.wasm']===manifest.binarySHA256&&
      report.inputSHA256['fo.js']===manifest.glueSHA256&&
      report.inputSHA256['find-orb-worker.js']===manifest.workerSHA256&&
      report.inputSHA256['find-orb.data']===manifest.pack.sha256&&
      report.inputSHA256['source-lock.json']===manifest.sourceLockSHA256,'Distribution integrity check failed before rebuild');
    require(report.currentRecipeSHA256['build/patches.mjs']===manifest.patchesSHA256&&
      report.currentRecipeSHA256['data/patches.mjs']===manifest.strictEphemerisPatchesSHA256&&
      report.currentRecipeSHA256['build/platform.cpp']===manifest.platformSHA256,'Current recipe differs from recorded distribution patches/platform');
    report.sourceIDs={sources:SOURCE_PINS,sourceLockSHA256:manifest.sourceLockSHA256,
      patchesObjectSHA256:sourceLock.patchesSHA256,patchesFileSHA256:manifest.patchesSHA256,
      strictEphemerisPatchesSHA256:manifest.strictEphemerisPatchesSHA256,platformSHA256:manifest.platformSHA256};
    await mkdir(join(ROOT,'.cache'),{recursive:true});
    const work=await mkdtemp(join(ROOT,'.cache/src-rebuild-'));
    const extracted=join(work,'archive'),buildWork=join(work,'work'),rebuilt=join(work,'dist');
    await mkdir(extracted);
    report.work=work;
    report.node={executable:process.execPath,version:process.version};
    const sdkPython=join(sdk,'python/3.13.3_64bit/bin/python3');
    let python=sdkPython;
    try {await access(python);} catch {python='python3';}
    const {env,attemptLog}=await offlineEnvironment(process.env,join(work,'offline'));
    report.offlineGuardNegativeControls=await checkOfflineGuards({env,attemptLog},python,work);
    report.offlinePolicy={upstreamSources:'--sources supplies checked archive files; no Git checkout/fetch path',
      ephemeris:'Explicit pinned local --ephemeris; download path unused',sdkCache:'EM_FROZEN_CACHE=1; SDK must already contain required runtime libraries',
      guards:'Git/curl/wget blocked on PATH; standard Node and Python network entry points throw and log attempts',
      limitation:'Defense-in-depth instrumentation, not an operating-system network sandbox or proof against malicious archived code',attemptLog};
    report.extractionCommand=[python,'-c',EXTRACT_SCRIPT,archive,extracted];
    const extraction=await capture(python,['-c',EXTRACT_SCRIPT,archive,extracted],{cwd:work,env,maxBuffer:1024*1024,timeout:120000});
    report.extraction=JSON.parse(extraction.stdout);
    report.archivedRecipeSHA256=await hashes(extracted,RECIPES);
    require(isDeepStrictEqual(report.archivedRecipeSHA256,report.currentRecipeSHA256),'Archived recipe does not match the current checkout');
    require(await equalFiles(join(extracted,'source-lock.json'),join(dist,'source-lock.json')),'Archived source-lock differs from distribution');
    const command=[process.execPath,join(extracted,'build/build.mjs'),'--sdk',sdk,'--work',buildWork,
      '--dist',rebuilt,'--ephemeris',ephemeris,'--sources',join(extracted,'sources')];
    const log=join(work,'build.log');
    Object.assign(report,{command,buildLog:log,rebuiltDist:rebuilt,status:'building'});
    await save(output,report);
    console.log('Rebuilding archived corresponding source; log: '+log);
    report.build=await execute(command[0],command.slice(1),{cwd:extracted,env,log});
    report.buildLogSHA256=await hashFile(log);
    report.outputSHA256=await hashes(rebuilt,ARTIFACTS);
    report.comparisons=[];
    for(const name of ARTIFACTS) {
      const same=await equalFiles(join(dist,name),join(rebuilt,name));
      report.comparisons.push({file:name,bytes:(await stat(join(dist,name))).size,byteForByteEqual:same,
        inputSHA256:report.inputSHA256[name],outputSHA256:report.outputSHA256[name]});
    }
    const mismatches=report.comparisons.filter(item=>!item.byteForByteEqual||item.inputSHA256!==item.outputSHA256);
    require(mismatches.length===0,'Rebuilt artifacts differ: '+mismatches.map(item=>item.file).join(', '));
    require(await hashFile(archive)===report.archiveSHA256,'Archive changed during rebuild');
    require(isDeepStrictEqual(await hashes(dist,ARTIFACTS),report.inputSHA256),'Distribution inputs changed during rebuild');
    require(isDeepStrictEqual(await hashes(ROOT,RECIPES),report.currentRecipeSHA256),'Current recipes changed during rebuild');
    require(await hashFile(ephemeris)===report.ephemerisSHA256,'Ephemeris changed during rebuild');
    let attempts='';
    try {attempts=await readFile(attemptLog,'utf8');} catch(error) {if(error.code!=='ENOENT')throw error;}
    require(attempts.length===0,'A forbidden Git/download/network operation was attempted');
    report.forbiddenAttempts=0;
    report.status='complete';report.passed=true;
    console.log('All six archived-source rebuild artifacts match byte-for-byte.');
  } catch(error) {
    report.status='failed';report.passed=false;report.error=error.stack??String(error);
    throw error;
  } finally {
    report.completedAt=new Date().toISOString();
    await save(output,report);
  }
  return report;
}

if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  if(process.argv.includes('--help')) {
    console.log('Usage: node scripts/verify-source-rebuild.mjs [--dist PATH] [--sdk PATH] [--ephemeris PATH] [--output PATH]');
  } else {
    const options={};
    for(let i=2;i<process.argv.length;i+=2) {
      const key=process.argv[i].slice(2);
      require(process.argv[i].startsWith('--')&&['dist','sdk','ephemeris','output'].includes(key)&&process.argv[i+1],'Expected a supported option and path; use --help');
      options[key]=process.argv[i+1];
    }
    await verifySourceRebuild(options);
  }
}
