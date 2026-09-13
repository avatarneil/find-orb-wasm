// SPDX-License-Identifier: GPL-2.0-or-later
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {gzipSync} from 'node:zlib';
import {createHash} from 'node:crypto';
import {createSessionFromUrls} from '../../src/index.js';
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const source='/* trusted worker */',data=Buffer.from([1,2,3]);
const manifest={schema:1,pack:{size:3,sha256:hash(data)},workerSHA256:hash(source)};

test('URL loader verifies assets before worker execution and accepts raw/gzip data',async t=>{
  let created=0,terminated=0,initialized;
  t.mock.method(globalThis,'fetch',async url=>new Response(url==='worker'?source: url==='gzip'?gzipSync(data):data));
  const previousWorker=globalThis.Worker;
  t.after(()=>{if(previousWorker===undefined)delete globalThis.Worker;else globalThis.Worker=previousWorker;});
  globalThis.Worker=class {
    constructor(){created++;}
    postMessage(message){initialized=message.pack;queueMicrotask(()=>this.onmessage({data:{id:message.id,result:{ready:true}}}));}
    terminate(){terminated++;}
  };
  for (const compression of ['none','gzip']) {
    const session=await createSessionFromUrls({workerURL:'worker',dataURL:compression==='gzip'?'gzip':'data',manifest,compression});
    assert.deepEqual([...new Uint8Array(initialized)],[1,2,3]);session.close();
  }
  assert.equal(created,2);assert.equal(terminated,2);
  await assert.rejects(createSessionFromUrls({workerURL:'worker',dataURL:'data',manifest:{...manifest,workerSHA256:'0'.repeat(64)}}),/checksum/);
  assert.equal(created,2,'Never execute an unverified worker');
});

test('URL loader bounds decompression, rejects corrupt data, and honors cancellation',async t=>{
  t.mock.method(globalThis,'fetch',async url=>new Response(url==='worker'?source:gzipSync(Buffer.alloc(100))));
  await assert.rejects(createSessionFromUrls({workerURL:'worker',dataURL:'bomb',manifest,compression:'gzip'}),/size limit/);
  t.mock.method(globalThis,'fetch',async url=>new Response(url==='worker'?source:Buffer.from([4,5,6])));
  await assert.rejects(createSessionFromUrls({workerURL:'worker',dataURL:'bad',manifest}),/checksum/);
  await assert.rejects(createSessionFromUrls({workerURL:'worker',dataURL:'bad',manifest,signal:AbortSignal.abort()}),{name:'AbortError'});
});
