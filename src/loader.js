// SPDX-License-Identifier: GPL-2.0-or-later
import './client.js';
const {createSession}=globalThis.FindOrbClient;

async function boundedBytes(stream,limit,signal) {
  const reader=stream.getReader(),parts=[];
  let size=0;
  const abort=() => {void reader.cancel(signal.reason).catch(()=>{});};
  signal?.addEventListener('abort',abort,{once:true});
  try {
    while (true) {
      signal?.throwIfAborted();
      const {value,done}=await reader.read();
      signal?.throwIfAborted();
      if (done) break;
      size+=value.byteLength;
      if (size>limit) throw new Error('Download exceeded its declared size limit.');
      parts.push(value);
    }
    const result=new Uint8Array(size);let offset=0;
    for (const part of parts) {result.set(part,offset);offset+=part.byteLength;}
    return result;
  } finally {
    signal?.removeEventListener('abort',abort);
    await reader.cancel().catch(()=>{});
    reader.releaseLock();
  }
}

async function checkedDownload(url,limit,expectedHash,compression,signal) {
  const response=await fetch(url,{signal,credentials:'omit'});
  if (!response.ok || !response.body) throw new Error('Unable to load solver asset: HTTP '+response.status);
  let body=response.body;
  if (compression==='gzip') {
    body=await decodeGzipIfNeeded(body);
  }
  const bytes=await boundedBytes(body,limit,signal);
  const hash=Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',bytes)),x=>x.toString(16).padStart(2,'0')).join('');
  if (hash!==expectedHash) throw new Error('Solver asset checksum mismatch.');
  return bytes;
}

async function decodeGzipIfNeeded(body) {
  // Browsers decode Content-Encoding even when CORS hides that header. Inspect
  // the delivered bytes, retaining the prefix without buffering the full asset.
  const reader=body.getReader(),prefix=[];
  let size=0,done=false;
  try {
    while (size<3 && !done) {
      const next=await reader.read();done=next.done;
      if (!done) {prefix.push(next.value);size+=next.value.byteLength;}
    }
  } catch(error) {reader.releaseLock();throw error;}
  const signature=new Uint8Array(Math.min(size,3));let offset=0;
  for (const chunk of prefix) {
    const part=chunk.subarray(0,signature.length-offset);signature.set(part,offset);offset+=part.length;
    if (offset===signature.length) break;
  }
  const replay=new ReadableStream({
    start(controller) {
      for (const chunk of prefix) controller.enqueue(chunk);
      if (done) {controller.close();reader.releaseLock();}
    },
    async pull(controller) {
      try {
        const next=await reader.read();
        if (next.done) {controller.close();reader.releaseLock();} else controller.enqueue(next.value);
      } catch(error) {controller.error(error);reader.releaseLock();}
    },
    async cancel(reason) {try {await reader.cancel(reason);} finally {reader.releaseLock();}},
  });
  return signature[0]===0x1f && signature[1]===0x8b && signature[2]===8 ? replay.pipeThrough(new DecompressionStream('gzip')) : replay;
}

/** Fetch assets using an application-trusted build manifest, then initialize.
 * Calling this API explicitly starts downloads; it does not run on import.
 * Bundle/pin the manifest with your application, not an untrusted remote input.
 */
export async function createSessionFromUrls({workerURL,dataURL,manifest,compression='none',signal,timeoutMs=90000}) {
  if (!manifest || manifest.schema!==1 || !Number.isSafeInteger(manifest.pack?.size) ||
      manifest.pack.size<1 || manifest.pack.size>128*1024*1024 ||
      !/^[a-f0-9]{64}$/.test(manifest.pack.sha256) || !/^[a-f0-9]{64}$/.test(manifest.workerSHA256) ||
      !['none','gzip'].includes(compression) || !Number.isFinite(timeoutMs) || timeoutMs<1 || timeoutMs>120000) {
    throw new Error('Invalid trusted solver manifest or loading options.');
  }
  const controller=new AbortController();
  const combined=signal ? AbortSignal.any([signal,controller.signal]) : controller.signal;
  const timer=setTimeout(()=>controller.abort(new Error('Solver asset loading timed out.')),timeoutMs);
  let session;
  try {
    const [worker,pack]=await Promise.all([
      checkedDownload(workerURL,5000000,manifest.workerSHA256,'none',combined),
      checkedDownload(dataURL,manifest.pack.size,manifest.pack.sha256,compression,combined),
    ]);
    combined.throwIfAborted();
    session=createSession(new TextDecoder('utf-8',{fatal:true}).decode(worker),{timeoutMs});
    await session.initialize(pack.buffer,combined);
    return session;
  } catch (error) {
    controller.abort(error);
    session?.close();
    throw error;
  } finally {clearTimeout(timer);}
}
