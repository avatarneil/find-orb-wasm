/* GPL-2.0-or-later. Portable low-level runtime; no application imports.
 * Each command gets a fresh C runtime, heap and virtual filesystem. */
(function(root,factory) {
  if (typeof module==='object' && module.exports) module.exports=factory();
  else root.FindOrbRuntime=factory();
})(typeof globalThis==='object' ? globalThis : this,function() {
  'use strict';
  const MAX_OUTPUT=5000000;
  async function sha256(bytes) {
    const result=await crypto.subtle.digest('SHA-256',bytes);
    return Array.from(new Uint8Array(result),x => x.toString(16).padStart(2,'0')).join('');
  }
  async function verify(manifest,pack,wasm) {
    if (manifest.schema!==1 || pack.byteLength!==manifest.pack.size ||
      await sha256(pack)!==manifest.pack.sha256 || await sha256(wasm)!==manifest.binarySHA256) {
      throw new Error('Find_Orb engine/data checksum mismatch. Nothing was calculated.');
    }
    let end=0;
    for (const [name,entry] of Object.entries(manifest.entries)) {
      if (!/^(data\/)?[A-Za-z0-9_.-]+$/.test(name) || name.includes('..') ||
        !Number.isSafeInteger(entry.offset) || !Number.isSafeInteger(entry.size) ||
        entry.offset!==end || entry.size<1 || entry.offset+entry.size>pack.byteLength) throw new Error('Invalid data directory.');
      end+=entry.size;
    }
    if (end!==pack.byteLength) throw new Error('Incomplete data directory.');
  }
  async function execute(factory,manifest,pack,wasm,args,files,outputs) {
    if (!Array.isArray(args) || args.length>64 || args.some(s => typeof s!=='string' || s.length>4096 || s.includes('\0')) ||
      !Array.isArray(outputs) || outputs.length>32) throw new Error('Invalid command.');
    const validPath=name => typeof name==='string' && /^\/job\/[A-Za-z0-9_.-]+$/.test(name) && !name.includes('..');
    const validDirectory=name => typeof name==='string' && name.endsWith('/') && validPath(name.slice(0,-1));
    if (!files || Object.keys(files).length>16 || Object.entries(files).some(([name,text]) => !validPath(name) || typeof text!=='string' || text.length>MAX_OUTPUT) ||
      outputs.some(name => !validPath(name) && !validDirectory(name))) throw new Error('Only bounded job files are accepted.');
    let log='',exitCode=null;
    const print=text => {if (log.length+text.length>262144) throw new Error('Solver output exceeded its limit.'); log+=text+'\n';};
    const instance=await factory({noInitialRun:true,wasmBinary:wasm,print,printErr:print,
      onExit:code => {exitCode=code;},
      quit:(_status,error) => {throw error;},
      // Never let this library resolve external files over the network.
      locateFile:() => 'unavailable:verified-wasm-is-supplied-in-memory'});
    const fs=instance.FS;
    fs.mkdir('/engine'); fs.mkdir('/engine/data'); fs.mkdir('/job');
    for(const name of new Set(outputs.filter(validDirectory))) fs.mkdir(name.slice(0,-1));
    for (const [name,entry] of Object.entries(manifest.entries)) {
      fs.writeFile('/engine/'+name,new Uint8Array(pack,entry.offset,entry.size));
    }
    for (const [name,text] of Object.entries(files)) fs.writeFile(name,text);
    fs.chdir('/job');
    try {instance.callMain([...args]);}
    catch(error) {if (error.name!=='ExitStatus' || error.status!==0) throw new Error(error.message+' '+log.slice(-2000),{cause:error});}
    if (exitCode!==0) throw new Error('Find_Orb failed ('+exitCode+'). '+log.slice(-2000));
    const result={files:{},stdout:log,exitCode}; let total=0;
    const requested=[];
    for(const name of new Set(outputs)) {
      if(validDirectory(name)) {
        if(!fs.isDir(fs.lstat(name.slice(0,-1)).mode)) throw new Error('Solver output directory is not a regular directory.');
        const names=fs.readdir(name).filter(n=>n!=='.' && n!=='..').sort();
        // Only one level of small text outputs; never recursive or unbounded.
        if(names.length>129 || names.some(n=>!validPath('/job/'+n))) throw new Error('Solver output directory exceeded its limit.');
        requested.push(...names.map(n=>({name:name+n,limit:24000})));
      } else requested.push({name,limit:MAX_OUTPUT});
    }
    for (const {name,limit} of requested) {
      const info=fs.lstat(name); total+=info.size;
      if (!fs.isFile(info.mode) || info.size>limit || total>16000000) throw new Error('Solver output exceeded its limit.');
      result.files[name]=fs.readFile(name,{encoding:'utf8'});
    }
    return result;
  }
  return {verify,execute,sha256};
});
