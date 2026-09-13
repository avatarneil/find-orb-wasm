// SPDX-License-Identifier: GPL-2.0-or-later
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {readFile} from 'node:fs/promises';
import '../../src/runtime.js';
const require=createRequire(import.meta.url);
const factory=require('../../dist/fo.cjs');
const wasmBinary=await readFile(new URL('../../dist/fo.wasm',import.meta.url));
const runtime=globalThis.FindOrbRuntime;
const moduleOptions=()=>({noInitialRun:true,wasmBinary,print(){},printErr(){}});

test('retaining compiled code preserves independent instances and filesystems',async()=>{
  const prepared=await runtime.prepare(factory,wasmBinary);
  const first=await prepared(moduleOptions());
  first.FS.writeFile('/only-first','private');
  const second=await prepared(moduleOptions());
  assert.notEqual(first,second);
  assert.notEqual(first.FS,second.FS);
  assert.throws(()=>second.FS.readFile('/only-first'));
  second.FS.writeFile('/only-first','second');
  assert.equal(first.FS.readFile('/only-first',{encoding:'utf8'}),'private');
  assert.equal(second.FS.readFile('/only-first',{encoding:'utf8'}),'second');
});

test('real MEMFS shares reference bytes until write/truncate and preserves the next job',async()=>{
  const instance=await factory(moduleOptions()),fs=instance.FS;
  const pack=new Uint8Array([9,1,2,3,4,8]);
  for (const [name,mutate] of [
    ['write',()=>fs.writeFile('/ref-write',new Uint8Array([6,7]),{flags:'r+'})],
    ['truncate',()=>fs.truncate('/ref-truncate',2)],
    ['grow',()=>fs.truncate('/ref-grow',9)],
  ]) {
    const path='/ref-'+name;
    runtime.mountReference(fs,path,pack.subarray(1,5));
    assert.equal(fs.lookupPath(path).node.contents.buffer,pack.buffer);
    mutate();
    assert.notEqual(fs.lookupPath(path).node.contents.buffer,pack.buffer);
    assert.deepEqual([...pack],[9,1,2,3,4,8]);
  }
  const second=await factory(moduleOptions());
  runtime.mountReference(second.FS,'/ref',pack.subarray(1,5));
  assert.deepEqual([...second.FS.readFile('/ref')],[1,2,3,4]);
  assert.notEqual(second.FS,instance.FS);
});

test('real MEMFS mapped writeback cannot modify shared reference pack',async()=>{
  const fs=(await factory(moduleOptions())).FS;
  const pack=new Uint8Array([1,2,3,4]);
  runtime.mountReference(fs,'/mapped',pack);
  const stream=fs.open('/mapped','r+');
  try {
    stream.stream_ops.msync(stream,new Uint8Array([8,7,6,5]),0,4,0);
    assert.deepEqual([...fs.readFile('/mapped')],[8,7,6,5]);
    assert.deepEqual([...pack],[1,2,3,4]);
  } finally {fs.close(stream);}
});
