#!/usr/bin/env node
// GPL-2.0-or-later. Isolated, auditable compiler experiment; never replaces dist.
import {readFile,writeFile,mkdir,cp,readdir,copyFile,access} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {SOURCE_PINS,EPHEMERIS} from './pins.mjs';
import {run} from './build.mjs';
const root=resolve(fileURLToPath(new URL('../',import.meta.url)));
export async function experiment({variant='lto'}={}) {
  if(!['lto','quad'].includes(variant))throw new Error('Supported compiler experiments: lto, quad');
  const snapshot=join(root,'.performance-'+variant),recipe=join(snapshot,'recipe');
  const work=join(root,'.wasm-engine-'+variant),dist=join(root,'dist-'+variant),sdk=join(root,'.wasm-toolchain');
  await mkdir(recipe,{recursive:true});
  for(const name of ['build','src','data','package.json','README.md','LICENSE','EMSCRIPTEN-LICENSE.txt','licenses','NOTICE','provenance.json']) {
    await cp(join(root,name),join(recipe,name),{recursive:true});
  }
  const builder=join(recipe,'build/build.mjs'),original=await readFile(builder,'utf8');
  let changed=original,transformation;
  if(variant==='lto') {
    const from="const strictFP=' -fno-fast-math -ffp-contract=off';";
    const to="const strictFP=' -fno-fast-math -ffp-contract=off -flto';";
    if(original.split(from).length!==2)throw new Error('Compiler recipe changed; review LTO transformation.');
    changed=original.replace(from,to).replace("const flags=['-O3','-g2'","const flags=['-O3','-flto','-g2'");
    transformation={from,to,linkFlag:'-flto'};
  } else {
    const source=join(sdk,'upstream/emscripten/system/lib/compiler-rt/lib/builtins'),target=join(recipe,'build/quad');
    await mkdir(target,{recursive:true});
    for(const name of await readdir(source)) if(name.endsWith('.h')||['fp_mul_impl.inc','multf3.c'].includes(name))await copyFile(join(source,name),join(target,name));
    // The upstream Find_Orb makefile links through em++; force C linkage so our
    // helper really overrides the compiler-rt symbol instead of being discarded.
    const helper=join(target,'multf3.c'),helperText=await readFile(helper,'utf8');
    const abi='COMPILER_RT_ABI fp_t __multf3(fp_t a, fp_t b)';
    if(helperText.split(abi).length!==2)throw new Error('compiler-rt multf3 ABI context changed.');
    await writeFile(helper,helperText.replace(abi,'#ifdef __cplusplus\nextern "C"\n#endif\n'+abi));
    const header=join(target,'fp_lib.h'),text=await readFile(header,'utf8');
    const body=text.indexOf('  const uint64_t product11 = Word_1(a) * Word_1(b);');
    const start=text.lastIndexOf('static __inline void wideMultiply',body),end=text.indexOf('#undef Word_1',body);
    if(body<0||start<0||end<0)throw new Error('compiler-rt wideMultiply context changed.');
    await writeFile(header,text.slice(0,start)+await readFile(join(root,'benchmark/quad-wide-multiply.h'),'utf8')+text.slice(end));
    await copyFile(join(sdk,'upstream/emscripten/system/lib/compiler-rt/LICENSE.TXT'),join(target,'LICENSE.TXT'));
    const from="join(here,'platform.cpp')];",to="join(here,'platform.cpp'),join(here,'quad/multf3.c')];";
    if(original.split(from).length!==2)throw new Error('Compiler link recipe changed.');
    changed=original.replace(from,to);transformation={helper:'__multf3',kernel:'benchmark/quad-wide-multiply.h',from,to};
  }
  await writeFile(builder,changed);
  await writeFile(join(snapshot,'experiment.json'),JSON.stringify({variant,source:'build/build.mjs',...transformation,
    numericalPolicy:'All double and binary128 long double precision preserved; no-fast-math and fp-contract=off throughout',
    createdAt:new Date().toISOString()},null,2)+'\n');
  // Clone locally from the pristine native source pins; keep experiments apart.
  for(const [name,commit]of Object.entries(SOURCE_PINS)) {
    const source=join(work,'sources',name);await mkdir(source,{recursive:true});
    if(!(await readdir(source)).length) {
      await run('git',['clone','--local','--no-hardlinks',join(root,'.native-engine/sources',name),source],root);
      await run('git',['checkout','--detach',commit],source);
      const makefile=join(source,'makefile');await writeFile(makefile,(await readFile(makefile,'utf8')).replace(/\tar /g,'\temar '));
    }
  }
  const env={...process.env},sdkPython=join(sdk,'python/3.13.3_64bit/bin/python3');
  try{await access(sdkPython);env.EMSDK_PYTHON=sdkPython;}catch{/* Linux uses its host Python. */}
  await run(process.execPath,[builder,'--sdk',sdk,'--work',work,'--dist',dist,'--ephemeris',join(root,'.cache',EPHEMERIS.filename)],root,env);
  return {variant,dist,work,recipe};
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  if(process.argv.length>2&&!(process.argv.length===4&&process.argv[2]==='--variant'))throw new Error('Usage: node build/performance.mjs [--variant lto|quad]');
  await experiment({variant:process.argv[3]||'lto'});
}
