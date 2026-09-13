import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import '../../src/runtime.js';
const runtime=globalThis.FindOrbRuntime;
test('integrity checks reject wrong bytes, missing coverage and unsafe data paths',async () => {
  const pack=new Uint8Array([1,2,3]).buffer,wasm=new Uint8Array([4,5]);
  const manifest={schema:1,pack:{size:3,sha256:await runtime.sha256(pack)},binarySHA256:await runtime.sha256(wasm),entries:{'data/test':{offset:0,size:3}}};
  await runtime.verify(manifest,pack,wasm);
  await assert.rejects(runtime.verify(manifest,new Uint8Array([1,2,4]).buffer,wasm),/checksum mismatch/);
  await assert.rejects(runtime.verify(manifest,pack,new Uint8Array([5,4])),/checksum mismatch/);
  await assert.rejects(runtime.verify({...manifest,entries:{'../bad':{offset:0,size:3}}},pack,wasm),/Invalid data/);
  await assert.rejects(runtime.verify({...manifest,entries:{'data/test':{offset:0,size:2}}},pack,wasm),/Incomplete/);
});
test('unsafe job files and unbounded commands are rejected before instantiating native code',async () => {
  const factory=() => {throw new Error('Must not instantiate');};
  for (const files of [{'/engine/data/environ.def':'bad'},{'/job/../bad':'bad'},{'/job/a':'x'.repeat(5000001)}]) {
    await assert.rejects(runtime.execute(factory,{},null,null,[],files,[]),/bounded job files/);
  }
  await assert.rejects(runtime.execute(factory,{},null,null,['bad\0option'],{},[]),/Invalid command/);
  for(const path of ['/job/../','/job/a/b/','/engine/data/',null]) {
    await assert.rejects(runtime.execute(factory,{},null,null,[],{},[path]),/bounded job files/);
  }
});
test('output directories collect bounded regular files, reject links, recursion and oversized families',async () => {
  const execute=async (names,size=10,mode='file',directoryMode='directory')=>runtime.execute(async options=>({
    FS:{mkdir(){},writeFile(){},chdir(){},readdir:()=>['.','..',...names],
      lstat:path=>({size,mode:path==='/job/offsets'?directoryMode:mode}),isFile:mode=>mode==='file',isDir:mode=>mode==='directory',readFile:()=> '0.0 0.0\n'},
    callMain:()=>options.onExit(0),
  }),{entries:{}},new ArrayBuffer(0),new Uint8Array(),[],{},['/job/offsets/']);
  const result=await execute(['202604200000.txt']);
  assert.deepEqual(Object.keys(result.files),['/job/offsets/202604200000.txt']);
  assert.deepEqual((await execute([])).files,{});
  for(const args of [[Array(130).fill('x.txt')],[['../bad']],[['nested/x']],[['x'],24001],[['x'],10,'symlink'],[['x'],10,'directory'],[['x'],10,'file','symlink']]) {
    await assert.rejects(execute(...args),/output/);
  }
});
test('generated runtime has no Node host-shell implementation',async () => {
  const glue=await readFile(new URL('../../dist/fo.js',import.meta.url),'utf8');
  assert.doesNotMatch(glue,/require\(["']child_process["']\)/);
});
