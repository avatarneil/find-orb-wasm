#!/usr/bin/env node
// Recreate the original package from the exact recorded webastrometrica commit.
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {mkdir,readFile,writeFile,mkdtemp,readdir,access} from 'node:fs/promises';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {EPHEMERIS} from '../build/pins.mjs';
import {digest,run,cleanBuildEnvironment} from '../build/build.mjs';
const capture=promisify(execFile),root=resolve(fileURLToPath(new URL('../',import.meta.url)));
const options={source:null,work:resolve(root,'.wasm-engine-baseline-rebuild'),dist:resolve(root,'dist-baseline'),extractOnly:false};
for(let i=2;i<process.argv.length;i++) {
  const key=process.argv[i].slice(2);
  if(key==='extract-only'){options.extractOnly=true;continue;}
  if(!['source','work','dist'].includes(key)||!process.argv[i+1])throw new Error('Options: --source LOCAL_WEBASTROMETRICA --work EMPTY_PATH --dist PATH --extract-only');
  options[key]=resolve(process.argv[++i]);
}
const provenance=JSON.parse(await readFile(join(root,'provenance.json'),'utf8'));
if(!options.source) {
  options.source=await mkdtemp(join(root,'.performance-baseline-source-'));
  await run('git',['init',options.source],root);
  await run('git',['fetch','--depth','1',provenance.sourceRepository+'.git',provenance.sourceCommit],options.source);
}
// git show reads immutable objects; never change the user's working checkout.
await capture('git',['cat-file','-e',provenance.sourceCommit+'^{commit}'],{cwd:options.source});
const recipe=await mkdtemp(join(root,'.performance-baseline-recipe-'));
for(const [filename,expected]of Object.entries(provenance.extractedFilesSHA256)) {
  if(!filename.startsWith(provenance.sourceDirectory))throw new Error('Unexpected extraction provenance path.');
  const relative=filename.slice(provenance.sourceDirectory.length);
  if(relative.split('/').some(part=>!part||part==='.'||part==='..'))throw new Error('Unsafe extraction path.');
  const {stdout:bytes}=await capture('git',['show',provenance.sourceCommit+':'+filename],{cwd:options.source,encoding:'buffer',maxBuffer:10000000});
  if(digest(bytes)!==expected)throw new Error('Extraction checksum mismatch: '+filename);
  await mkdir(dirname(join(recipe,relative)),{recursive:true});await writeFile(join(recipe,relative),bytes);
}
console.log('Verified original baseline recipe: '+recipe+' ('+provenance.sourceCommit+')');
if(!options.extractOnly) {
  await mkdir(options.work,{recursive:true});
  if((await readdir(options.work)).length)throw new Error('Use a fresh empty --work directory for the historical baseline builder.');
  const sdk=join(root,'.wasm-toolchain'),env={...cleanBuildEnvironment(process.env),EM_CONFIG:join(sdk,'.emscripten')};
  const sdkPython=join(sdk,'python/3.13.3_64bit/bin/python3');
  try{await access(sdkPython);env.EMSDK_PYTHON=sdkPython;}catch{/* Linux can use its host Python 3.10+. */}
  await run(process.execPath,[join(recipe,'build/build.mjs'),'--sdk',sdk,'--work',options.work,'--dist',options.dist,
    '--ephemeris',join(root,'.cache',EPHEMERIS.filename)],recipe,env);
}
