/* GPL-2.0-or-later. Browser worker lifecycle. No application dependencies. */
(function(root,factory) {
  if (typeof module==='object' && module.exports) module.exports=factory();
  else root.FindOrbClient=factory();
})(typeof globalThis==='object' ? globalThis : this,function() {
  'use strict';
  function createSession(workerSource,{timeoutMs=90000}={}) {
    if (!Number.isFinite(timeoutMs) || timeoutMs<1 || timeoutMs>120000 || typeof workerSource!=='string' || workerSource.length>5000000) throw new Error('Invalid worker or timeout.');
    if (typeof Worker!=='function' || typeof WebAssembly!=='object' || !globalThis.crypto?.subtle) throw new Error('Use a browser with WebAssembly, workers and Web Crypto (HTTPS or a local file).');
    const url=URL.createObjectURL(new Blob([workerSource],{type:'text/javascript'}));
    let worker;
    try {worker=new Worker(url);} finally {URL.revokeObjectURL(url);}
    let pending=null,sequence=0,closed=false;
    function close(message='Calculation cancelled.') {
      if (closed) return; closed=true; worker.terminate();
      if (pending) {const p=pending;pending=null;p.cleanup();p.reject(new Error(message));}
    }
    worker.onerror=event => {event.preventDefault();close('WebAssembly worker failed: '+event.message);};
    worker.onmessageerror=() => close('Unable to read the solver response.');
    worker.onmessage=event => {
      const p=pending;
      if (!p || event.data?.id!==p.id) return;
      pending=null;p.cleanup();
      if (event.data.error) {p.reject(new Error(event.data.error));close('Solver failed.');}
      else p.resolve(event.data.result);
    };
    function command(payload,signal,transfer=[]) {
      if (closed || signal?.aborted) return Promise.reject(new Error('Calculation cancelled.'));
      if (pending) return Promise.reject(new Error('A calculation is already running.'));
      return new Promise((resolve,reject) => {
        const id=++sequence;
        const abort=() => close();
        const timer=setTimeout(() => close('Calculation exceeded its time limit; no partial solution was accepted.'),timeoutMs);
        const cleanup=() => {clearTimeout(timer);signal?.removeEventListener('abort',abort);};
        pending={id,resolve,reject,cleanup};signal?.addEventListener('abort',abort,{once:true});
        try {worker.postMessage({id,...payload},transfer);}
        catch(error) {close('Unable to start the solver: '+error.message);}
      });
    }
    return {initialize:(pack,signal) => command({type:'init',pack},signal,[pack]),
      execute:(args,files,outputs,signal) => command({type:'run',args,files,outputs},signal),close};
  }
  return {createSession};
});
