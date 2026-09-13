#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir,rename,open} from 'node:fs/promises';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {gzipSync} from 'node:zlib';
import os from 'node:os';
import {loadNative,loadWasm} from '../../benchmark/engines.mjs';
import {SOURCE_PINS} from '../../build/pins.mjs';
import {sha} from '../short-arcs/methods.mjs';
import {protocol,validateCorpus,makePlan,commandFor,evaluateOutput,comparePair,summarize,validateCoverage,objectId} from './core.mjs';
const root=fileURLToPath(new URL('../../',import.meta.url));
export const usage=`Usage: node experiments/regression-suite/run.mjs [options]
  --mode sentinel|full             Sentinel executes; full only plans unless --execute.
  --checks forward|fit|all          Default all; selected checks and omissions are explicit.
  --corpus PATH                    Default experiments/regression-corpus/corpus.json.
  --validate-corpus                Offline whole-corpus structural/numerical validation only.
  --dry-run                       Offline planning only; no engine loads or API calls.
  --execute                       Execute the full plan (potentially thousands of jobs).
  --baseline-dir DIR              Default .native-engine; verified reference build.
  --baseline-kind native-count|wasm
  --baseline-sha256 HEX            Require this exact baseline manifest SHA256 for replay.
  --candidate-dir DIR             Default dist-compact; verified candidate build.
  --candidate-kind wasm|native-count
  --fit-gate parity|report         Report permits intentional fit changes, not forward regressions.
  --arcs all|CSV --cases CSV        Explicit subset overrides frozen sentinel assignment.
  --noise exact,gaussian --seeds 0  Full defaults exact+Gaussian; sentinel defaults exact.
  --budget 100                     Initial SR batch capacity, not total attempted candidates.
  --original-native-dir DIR        Optional time-capped fo diagnostic; not parity authority.
  --output DIR                    New evidence directory; existing directories are rejected.
  --estimate-fit-seconds 5         Unmeasured scheduling assumption for dry-run estimates.
  --estimate-forward-seconds 1     Unmeasured scheduling assumption for dry-run estimates.
  --help
`;
const values=new Set(['mode','checks','corpus','baseline-dir','baseline-kind','baseline-sha256','candidate-dir','candidate-kind','fit-gate','arcs','cases','noise','seeds','budget','original-native-dir','output','estimate-fit-seconds','estimate-forward-seconds']);
const flags=new Set(['dry-run','execute','validate-corpus','help']);
export function parseOptions(args) {
  const options={};
  for(let i=0;i<args.length;i++) {
    assert.ok(args[i].startsWith('--'),'Expected --option');const key=args[i].slice(2);
    assert.ok(!Object.hasOwn(options,key),'Duplicate option: '+key);
    if(flags.has(key))options[key]=true;
    else {assert.ok(values.has(key),'Unknown option: '+key);assert.ok(args[i+1]&&!args[i+1].startsWith('--'),'Missing value for '+key);options[key]=args[++i];}
  }
  return options;
}
export function configuration(options) {
  for(const key of Object.keys(options))assert.ok(values.has(key)||flags.has(key),'Unknown option: '+key);
  const config={mode:'sentinel',checks:'all',corpus:join(root,'experiments/regression-corpus/corpus.json'),
    'baseline-dir':join(root,'.native-engine'),'baseline-kind':'native-count','candidate-dir':join(root,'dist-compact'),'candidate-kind':'wasm',
    'fit-gate':'parity',budget:100,'estimate-fit-seconds':5,'estimate-forward-seconds':1,...options};
  assert.ok(['sentinel','full'].includes(config.mode),'Known suite mode');
  assert.ok(['forward','fit','all'].includes(config.checks),'Known selected checks');
  for(const role of ['baseline','candidate'])assert.ok(['wasm','native-count'].includes(config[role+'-kind']),'Known '+role+' kind; original fo is diagnostic only');
  assert.ok(['parity','report'].includes(config['fit-gate']),'Known fit gate');
  for(const key of ['budget','estimate-fit-seconds','estimate-forward-seconds']){assert.ok(String(config[key]).trim()!=='','Nonempty '+key);config[key]=Number(config[key]);assert.ok(Number.isFinite(config[key])&&config[key]>0,'Positive '+key);}
  assert.ok(Number.isInteger(config.budget)&&config.budget>=11&&config.budget<=10000,'Valid SR batch capacity');
  if(config['baseline-sha256'])assert.match(config['baseline-sha256'],/^[a-f0-9]{64}$/,'Baseline manifest SHA256');
  assert.ok(!(config.execute&&config['dry-run']),'Choose execution or dry run');
  config['dry-run']=Boolean(config['dry-run']||(config.mode==='full'&&!config.execute));
  return config;
}
export function planSummary(units,config) {
  const fits=config.checks==='forward'?0:units.reduce((n,u)=>n+u.settings.length,0),original=Boolean(config['original-native-dir']);
  const forwardPairs=config.checks==='fit'?0:units.length,forwardCommands=forwardPairs*2,fitCommands=fits*(original?3:2);
  return {mode:config.mode,checks:config.checks,caseCount:new Set(units.map(u=>u.c.id)).size,objectCount:new Set(units.map(u=>objectId(u.c))).size,
    arcAssignments:units.map(u=>({caseId:u.c.id,arc:u.arc.id,settings:u.settings})),forwardPairs,fitPairs:fits,forwardCommands,fitCommands,
    totalCommands:forwardCommands+fitCommands,originalTimeCappedDiagnostics:original?fits:0,
    estimatedSerialSeconds:forwardCommands*config['estimate-forward-seconds']+fitCommands*config['estimate-fit-seconds'],
    estimateBasis:{measured:false,fitSeconds:config['estimate-fit-seconds'],forwardSeconds:config['estimate-forward-seconds'],warning:'Scheduling assumption only; difficult fits may take much longer.'}};
}
async function loadEngine(directory,kind) {return kind==='wasm'?loadWasm(directory):loadNative(directory);}
async function provenance(engine,kind) {
  const filename=kind==='wasm'?'manifest.json':'engine.json',bytes=await readFile(join(engine.root,filename));
  assert.deepEqual(engine.manifest.sources,SOURCE_PINS,'Pinned source revisions');
  let header;
  if(kind==='wasm') {
    const entry=engine.manifest.entries[engine.manifest.ephemeris.filename];assert.ok(entry,'Packed ephemeris entry');
    header=Buffer.from(engine.pack,entry.offset+2652,16);
  } else {
    const file=await open(join(engine.root,engine.manifest.ephemeris.filename));header=Buffer.alloc(16);
    try {assert.equal((await file.read(header,0,16,2652)).bytesRead,16,'Complete ephemeris date header');}finally{await file.close();}
  }
  const coverage={startExclusiveJd:header.readDoubleLE(0),endInclusiveJd:header.readDoubleLE(8),basis:'Verified DE440 file date header; conservative exclusive lower endpoint'};
  assert.ok(Number.isFinite(coverage.startExclusiveJd)&&coverage.startExclusiveJd<coverage.endInclusiveJd,'Valid ephemeris coverage');
  return {kind,manifestFile:filename,manifestSHA256:sha(bytes),manifest:engine.manifest,coverage,
    executionPolicy:kind==='native-original'?'Original native fo, upstream half-CPU-second SR cap; diagnostic only.':'Fixed SR batch capacity; upstream outer refinement time limits remain.',
    setup:engine.setup??null};
}
async function writeJson(path,object) {
  await writeFile(path+'.tmp',JSON.stringify(object,null,2)+'\n');await rename(path+'.tmp',path);
}
export async function runSuite(options={},dependencies={}) {
  const config=configuration(options),corpusBytes=await readFile(config.corpus),corpus=validateCorpus(JSON.parse(corpusBytes));
  if(config['validate-corpus'])return {validation:{valid:true,cases:corpus.cases.length,objects:new Set(corpus.cases.map(objectId)).size,
    corpusSHA256:sha(corpusBytes),scope:'Entire corpus structure, finite values, index ordering, physical applicability and TT/UTC target grids; source response hash integrity is the corpus generator validator responsibility.'}};
  const units=makePlan(corpus,config),plan=planSummary(units,config);
  if(config['dry-run'])return {dryRun:true,plan,corpusSHA256:sha(corpusBytes),protocol};
  assert.ok(config.output,'Execution requires --output pointing to a new evidence directory');
  const output=resolve(config.output);
  // Reserve the whole directory exclusively; interrupted runs are never silently
  // resumed or overwritten. Re-run into a new directory and compare evidence.
  await mkdir(dirname(output),{recursive:true});await mkdir(output);await mkdir(join(output,'raw'));
  const manifest={schemaVersion:1,config,plan,corpusSHA256:sha(corpusBytes),corpusProvenance:corpus.provenance??null,protocol,
    sources:SOURCE_PINS,startedAt:new Date().toISOString(),status:'loading-engines',
    host:{platform:os.platform(),arch:os.arch(),node:process.version,cpu:os.cpus()[0]?.model},files:{}};
  for(const path of ['experiments/regression-suite/run.mjs','experiments/regression-suite/core.mjs','experiments/regression-suite/protocol.json',
    'experiments/short-arcs/methods.mjs','benchmark/engines.mjs','benchmark/cases.mjs','benchmark/accuracy.mjs','build/pins.mjs'])manifest.files[path]=sha(await readFile(join(root,path)));
  await writeJson(join(output,'manifest.json'),manifest);
  const loader=dependencies.loadEngine??loadEngine,describe=dependencies.provenance??provenance;
  let baseline,candidate,original;
  try {
    baseline=await loader(config['baseline-dir'],config['baseline-kind']);candidate=await loader(config['candidate-dir'],config['candidate-kind']);
    manifest.engines={baseline:await describe(baseline,config['baseline-kind']),candidate:await describe(candidate,config['candidate-kind'])};
    if(config['baseline-sha256'])assert.equal(manifest.engines.baseline.manifestSHA256,config['baseline-sha256'],'Requested immutable baseline manifest');
    if(config['original-native-dir']&&config.checks!=='forward') {
      original=dependencies.loadOriginal?await dependencies.loadOriginal(config['original-native-dir']):await loadNative(config['original-native-dir'],'fo');
      manifest.engines.original=await describe(original,'native-original');
    }
    manifest.status='running';await writeJson(join(output,'manifest.json'),manifest);
  } catch(error) {
    manifest.status='failed-before-execution';manifest.error=String(error.stack||error);await writeJson(join(output,'manifest.json'),manifest);throw error;
  }
  let rawIndex=0;const results=[];
  async function execute(engine,role,command,identity) {
    let result=null,summary,stage='execution';
    try {result=await engine.execute(command);stage='validation';summary=evaluateOutput(command,result);}
    catch(error){summary={valid:false,stage,error:String(error.stack||error)};}
    const raw={identity,role,command,result,summary},bytes=Buffer.from(JSON.stringify(raw)),compressed=gzipSync(bytes,{level:9});
    const rawFile='raw/'+String(++rawIndex).padStart(6,'0')+'-'+role+'.json.gz';
    await writeFile(join(output,rawFile),compressed);
    return {...summary,evidence:{rawFile,rawSHA256:sha(bytes),gzipSHA256:sha(compressed),commandSHA256:sha(JSON.stringify(command))}};
  }
  async function pair(unit,kind,settings) {
    const {c,arc}=unit,identity={caseId:c.id,objectId:objectId(c),object:c.object.name,class:c.object.class,split:c.split,arc:arc.id,kind,settings,applicability:c.applicability};
    let command;try {
      command=commandFor(c,arc,kind,settings,config.budget);
      identity.coverage={baseline:validateCoverage(command,manifest.engines.baseline.coverage),candidate:validateCoverage(command,manifest.engines.candidate.coverage)};
      if(original)identity.coverage.original=validateCoverage(command,manifest.engines.original.coverage);
      identity.geometry={observer:c.observer,source:c.geometry??null,model:c.model??null,
        observedElongationDeg:arc.observationIndices.map(i=>c.astrometry[i].elongationDeg??null),
        interpretation:'Geocentric numerical geometry; solar elongation is recorded, not a daylight/horizon observability filter.'};
    }
    catch(error) {
      const row={...identity,comparison:{pass:false,comparable:false,failures:['Command construction: '+String(error.stack||error)]}};
      results.push(row);await writeJson(join(output,'results.json'),results);return;
    }
    // Sequential fresh jobs avoid shared loader state and record the exact same
    // command hash for the paired engines. Timings are not performance claims.
    const b=await execute(baseline,'baseline',command,identity),cnd=await execute(candidate,'candidate',command,identity);
    let comparison;try {comparison=comparePair(b,cnd,{kind,applicability:c.applicability,fitGate:config['fit-gate']});}
    catch(error){comparison={pass:false,comparable:false,failures:['Comparison validation: '+String(error.stack||error)]};}
    const row={...identity,baseline:b,candidate:cnd,comparison};
    if(original&&kind==='fit') {
      row.originalDiagnostic=await execute(original,'original-time-capped',command,identity);
      row.originalDiagnostic.comparisonScope='Diagnostic only; different ranging CPU cap. Excluded from parity and overall pass.';
      if(row.originalDiagnostic.valid&&b.valid)row.originalDiagnostic.pairedWithCount=comparePair(b,row.originalDiagnostic,{kind,applicability:c.applicability,fitGate:'report'});
    }
    results.push(row);await writeJson(join(output,'results.json'),results);
    (dependencies.log??console.log)(JSON.stringify({pair:results.length,plannedPairs:plan.forwardPairs+plan.fitPairs,
      caseId:c.id,arc:arc.id,kind,settings,pass:comparison.pass,failures:comparison.failures}));
  }
  for(const unit of units) {
    if(config.checks!=='fit')await pair(unit,'forward',{noise:'exact',seed:0});
    if(config.checks!=='forward')for(const settings of unit.settings)await pair(unit,'fit',settings);
  }
  const summary=summarize(results);summary.complete=results.length===plan.forwardPairs+plan.fitPairs;
  summary.pass&&=summary.complete;
  summary.validationScope={checks:config.checks,forwardControlsRun:config.checks!=='fit',inverseFitsRun:config.checks!=='forward',
    fullSelectedProtocolPassed:summary.pass&&config.checks==='all'&&config['fit-gate']==='parity',
    fitGate:config['fit-gate'],interpretation:'Pass applies only to explicitly selected checks and cases; fit-only runs do not validate the independent forward-state reference floor.'};
  await writeJson(join(output,'summary.json'),summary);
  manifest.completedAt=new Date().toISOString();manifest.status=summary.pass?'passed':'failed';manifest.completedPairs=results.length;manifest.rawFiles=rawIndex;
  manifest.resultsSHA256=sha(await readFile(join(output,'results.json')));manifest.summarySHA256=sha(await readFile(join(output,'summary.json')));
  await writeJson(join(output,'manifest.json'),manifest);
  return {manifest,summary,results};
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  try {
    const options=parseOptions(process.argv.slice(2));
    if(options.help)console.log(usage);
    else {const result=await runSuite(options);console.log(JSON.stringify(result.summary??result,null,2));if(result.summary&&!result.summary.pass)process.exitCode=1;}
  } catch(error) {console.error(String(error.stack||error));process.exitCode=1;}
}
