// SPDX-License-Identifier: GPL-2.0-or-later
// Package checked builds; never rebuild or change solver arithmetic here.
import {readFile,writeFile,mkdir,cp,copyFile,readdir} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {createHash} from 'node:crypto';
import {gunzipSync} from 'node:zlib';
import {execFileSync} from 'node:child_process';
const root=resolve(import.meta.dirname,'..');
const {version}=JSON.parse(await readFile(join(root,'package.json'),'utf8'));
const output=resolve(process.argv[2] || `.cache/release-v${version}`);
await mkdir(output); // Refuse to overwrite a prepared release.
const assets=join(output,'assets');await mkdir(assets);
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
for(const [flavor,directory] of [['compact','dist-compact'],['full','dist']]) {
  const dist=join(root,directory),manifest=JSON.parse(await readFile(join(dist,'manifest.json'),'utf8'));
  for(const [file,expected] of [['fo.wasm',manifest.binarySHA256],['fo.js',manifest.glueSHA256],
    ['find-orb-worker.js',manifest.workerSHA256],['find-orb.data',manifest.pack.sha256]]) {
    if(hash(await readFile(join(dist,file)))!==expected) throw new Error(`Checksum mismatch: ${directory}/${file}`);
  }
  const compressed=await readFile(join(dist,'find-orb.data.gz'));
  if(hash(gunzipSync(compressed))!==manifest.pack.sha256) throw new Error('Compressed pack mismatch.');
  const stage=join(output,flavor);await mkdir(join(stage,'dist'),{recursive:true});
  for(const file of ['fo.js','fo.cjs','fo.wasm','find-orb-worker.js','manifest.json','source-lock.json','licenses','corresponding-source.tar.gz'])
    await cp(join(dist,file),join(stage,'dist',file),{recursive:true});
  for(const file of ['src','build','data','licenses','package.json','README.md','NOTICE','LICENSE','EMSCRIPTEN-LICENSE.txt','provenance.json'])
    await cp(join(root,file),join(stage,file),{recursive:true});
  const stem=`find-orb-wasm-v${version}${flavor==='full'?'-full':''}`;
  execFileSync('tar',['-czf',join(assets,stem+'.tar.gz'),'-C',stage,'.']);
  await writeFile(join(assets,`find-orb-v${version}${flavor==='full'?'-full':''}.data.gz`),compressed);
}
await copyFile(join(root,'dist/corresponding-source.tar.gz'),join(assets,`find-orb-wasm-v${version}-corresponding-source.tar.gz`));
await copyFile(join(root,`results/parity-v${version}.json`),join(assets,`parity-v${version}.json`));
let sums='';
for(const name of (await readdir(assets)).sort()) sums+=hash(await readFile(join(assets,name)))+'  '+name+'\n';
await writeFile(join(assets,'SHA256SUMS'),sums);
console.log(assets);
