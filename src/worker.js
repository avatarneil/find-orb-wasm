/* Appended to pinned compiler glue by the build, never loaded from user input. */
let engineData=null,engineWasm=null,engineFactory=null,busy=false;
self.onmessage=async event => {
  const {id,type,pack,args,files,outputs}=event.data;
  if (busy) {self.postMessage({id,error:'A solver command is already running.'}); return;}
  busy=true;
  try {
    if (type==='init') {
      engineWasm=Uint8Array.from(atob(FIND_ORB_WASM_BASE64),c => c.charCodeAt(0));
      await FindOrbRuntime.verify(FIND_ORB_MANIFEST,pack,engineWasm);
      engineFactory=await FindOrbRuntime.prepare(createFindOrb,engineWasm);
      engineData=pack; self.postMessage({id,result:{ready:true}});
    } else if (type==='run' && engineData) {
      const result=await FindOrbRuntime.execute(engineFactory,FIND_ORB_MANIFEST,engineData,engineWasm,args,files,outputs);
      self.postMessage({id,result});
    } else throw new Error('The solver data have not been verified.');
  } catch(error) {self.postMessage({id,error:error.message || 'WebAssembly calculation failed.'});}
  finally {busy=false;}
};
