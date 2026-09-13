#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
// Isolated scientific experiment. Production recipes and distributions are untouched.
import {cp,mkdir,readFile,writeFile,readdir} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {SOURCE_PINS,EPHEMERIS} from '../../build/pins.mjs';
import {run} from '../../build/build.mjs';
import {patches} from './patches.mjs';

const root=fileURLToPath(new URL('../../',import.meta.url));
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
export async function buildExperiment(target) {
  if(!['native','wasm'].includes(target)) throw new Error('Target must be native or wasm.');
  const snapshot=join(root,'.performance-short-arcs-'+target),recipe=join(snapshot,'recipe');
  const work=join(root,target==='wasm'?'.wasm-engine-short-arcs':'.native-engine-short-arcs');
  if((await readdir(work).catch(e=>{if(e.code==='ENOENT')return [];throw e;})).length)
    throw new Error('Experimental build already exists; preserve it or explicitly move it before rebuilding: '+work);
  await mkdir(recipe,{recursive:true});
  for(const name of ['build','src','data','package.json','README.md','LICENSE','EMSCRIPTEN-LICENSE.txt','licenses','NOTICE','provenance.json'])
    await cp(join(root,name),join(recipe,name),{recursive:true});
  await cp(join(root,'experiments/short-arcs'),join(recipe,'experiments/short-arcs'),{recursive:true});
  const patchJson=JSON.stringify(patches);
  if(target==='wasm') {
    const path=join(recipe,'build/patches.mjs');
    await writeFile(path,(await readFile(path,'utf8'))+'\n// Opt-in short-arc research; intentionally outside the release recipe.\npatches.push(...'+patchJson+');\n');
  } else {
    const path=join(recipe,'build/native.mjs'),original=await readFile(path,'utf8');
    const from='await writeFile(filename,original.replace(from,to));';
    if(original.split(from).length!==2)throw new Error('Native experiment insertion context changed.');
    const to=`let experimental=original.replace(from,to);
        for(const patch of ${patchJson}) {
          if(patch.file!=='orb_func.cpp')throw new Error('Native experiment only supports orb_func.cpp patches.');
          if(experimental.split(patch.from).length!==2)throw new Error('Research patch context changed.');
          experimental=experimental.replace(patch.from,patch.to);
        }
        await writeFile(filename,experimental);`;
    await writeFile(path,original.replace(from,to).replace(
      'Only statistical-ranging loop changed to complete configured candidate count',
      'Count-limited upstream plus explicitly configured experimental short-arc selector and candidate export'));
  }
  // Local clones retain immutable upstream revisions; the checked build recipe
  // applies its recorded patches in separate trees and records all file hashes.
  for(const [name,commit]of Object.entries(SOURCE_PINS)) {
    const source=join(work,'sources',name);await mkdir(join(work,'sources'),{recursive:true});
    await run('git',['clone','--local','--no-hardlinks',join(root,'.native-engine/sources',name),source],root);
    await run('git',['checkout','--detach',commit],source);
    if(target==='wasm') {
      const path=join(source,'makefile');await writeFile(path,(await readFile(path,'utf8')).replace(/\tar /g,'\temar '));
    }
  }
  const args=target==='wasm'?
    [join(recipe,'build/build.mjs'),'--sdk',join(root,'.wasm-toolchain'),'--work',work,'--dist',join(root,'dist-short-arcs')]:
    [join(recipe,'build/native.mjs'),'--root',work];
  await run(process.execPath,[...args,'--ephemeris',join(root,'.cache',EPHEMERIS.filename)],root);
  const evidence={schemaVersion:1,target,sources:SOURCE_PINS,patchesSHA256:hash(patchJson),patches,
    experiment:'Uncalibrated candidate representatives; selection is opt-in; no changed force model or floating-point policy.',
    builtAt:new Date().toISOString()};
  await writeFile(join(work,'short-arc-experiment.json'),JSON.stringify(evidence,null,2)+'\n');
  if(target==='wasm')await writeFile(join(root,'dist-short-arcs/short-arc-experiment.json'),JSON.stringify(evidence,null,2)+'\n');
  return evidence;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  if(process.argv.length!==3)throw new Error('Usage: node experiments/short-arcs/build.mjs native|wasm');
  await buildExperiment(process.argv[2]);
}
