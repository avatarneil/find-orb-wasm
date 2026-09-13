#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
// Offline evidence replay: never imports or invokes an engine factory directly.
// Source hashes are strict; reproduce historical code before replaying old runs.
import assert from 'node:assert/strict';
import {readFile,readdir} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {gunzipSync} from 'node:zlib';
import {sha} from '../short-arcs/methods.mjs';
import {SOURCE_PINS} from '../../build/pins.mjs';
import {configuration,planSummary} from './run.mjs';
import {protocol,validateCorpus,makePlan,commandFor,validateCoverage,evaluateOutput,comparePair,summarize,objectId} from './core.mjs';
const root=fileURLToPath(new URL('../../',import.meta.url));
const recordedSources=['experiments/regression-suite/run.mjs','experiments/regression-suite/core.mjs','experiments/regression-suite/protocol.json',
  'experiments/short-arcs/methods.mjs','benchmark/engines.mjs','benchmark/cases.mjs','benchmark/accuracy.mjs','build/pins.mjs'];
const firstLine=error=>String(error.stack??error).split(/\r?\n/)[0];
const jsonValue=value=>JSON.parse(JSON.stringify(value));
function normalized(value) {
  if(Array.isArray(value))return value.map(normalized);
  if(value&&typeof value==='object')return Object.fromEntries(Object.entries(value).map(([key,item])=>[key,
    key==='error'&&typeof item==='string'?firstLine(item):key==='failures'&&Array.isArray(item)?item.map(firstLine):normalized(item)]));
  return value;
}
function equivalent(actual,expected,label) {assert.deepEqual(normalized(jsonValue(actual)),normalized(jsonValue(expected)),label);}
function checksum(bytes,expected,label) {assert.match(expected??'',/^[a-f0-9]{64}$/,'Recorded '+label+' SHA256');assert.equal(sha(bytes),expected,label+' checksum');}
function identityFor(c,arc,kind,settings) {
  return {caseId:c.id,objectId:objectId(c),object:c.object.name,class:c.object.class,split:c.split,arc:arc.id,kind,settings,applicability:c.applicability};
}
function prepare(c,arc,kind,settings,config,engines) {
  const identity=identityFor(c,arc,kind,settings);let command;
  try {
    command=commandFor(c,arc,kind,settings,config.budget);
    identity.coverage={baseline:validateCoverage(command,engines.baseline.coverage),candidate:validateCoverage(command,engines.candidate.coverage)};
    if(engines.original)identity.coverage.original=validateCoverage(command,engines.original.coverage);
    identity.geometry={observer:c.observer,source:c.geometry??null,model:c.model??null,
      observedElongationDeg:arc.observationIndices.map(i=>c.astrometry[i].elongationDeg??null),
      interpretation:'Geocentric numerical geometry; solar elongation is recorded, not a daylight/horizon observability filter.'};
    return {identity,command};
  } catch(error) {return {identity,failure:{pass:false,comparable:false,failures:['Command construction: '+firstLine(error)]}};}
}
function scientificComparison(baseline,candidate,kind,applicability,fitGate) {
  try {return comparePair(baseline,candidate,{kind,applicability,fitGate});}
  catch(error) {return {pass:false,comparable:false,failures:['Comparison validation: '+firstLine(error)]};}
}
export async function replaySuite({directory,corpus:corpusPath=join(root,'experiments/regression-corpus/corpus.json'),manifestSHA256}={}) {
  assert.ok(directory,'Archive directory required');const archive=resolve(directory);
  const manifestBytes=await readFile(join(archive,'manifest.json')),manifest=JSON.parse(manifestBytes);
  if(manifestSHA256)checksum(manifestBytes,manifestSHA256,'Externally anchored manifest');
  assert.equal(manifest.schemaVersion,1,'Known suite archive schema');
  assert.ok(['passed','failed'].includes(manifest.status),'Completed suite archive required');
  assert.ok(Number.isFinite(Date.parse(manifest.completedAt)),'Completion timestamp');
  assert.deepEqual(Object.keys(manifest.files??{}).sort(),recordedSources.slice().sort(),'Complete source-hash inventory');
  for(const path of recordedSources)checksum(await readFile(join(root,path)),manifest.files[path],'Historical/current source '+path+' (restore recorded code to replay)');
  equivalent(manifest.protocol,protocol,'Recorded numerical protocol matches current pinned source');
  equivalent(manifest.sources,SOURCE_PINS,'Pinned upstream source revisions');
  const corpusBytes=await readFile(corpusPath);checksum(corpusBytes,manifest.corpusSHA256,'Normalized corpus');
  const corpus=validateCorpus(JSON.parse(corpusBytes)),config=configuration(manifest.config),units=makePlan(corpus,config),plan=planSummary(units,config);
  equivalent(manifest.config,config,'Declared configuration is complete and valid');
  assert.equal(config['dry-run'],false,'Archive records actual execution, not a dry run');
  equivalent(manifest.corpusProvenance,corpus.provenance??null,'Recorded independent-source provenance');
  equivalent(manifest.plan,plan,'Declared plan independently reconstructed from corpus and configuration');
  const roles=['baseline','candidate',...(config['original-native-dir']&&config.checks!=='forward'?['original']:[])];
  assert.deepEqual(Object.keys(manifest.engines??{}).sort(),roles.slice().sort(),'Complete declared engine roles');
  for(const role of roles) {
    const engine=manifest.engines[role];assert.match(engine.manifestSHA256??'',/^[a-f0-9]{64}$/,'Recorded '+role+' manifest hash');
    if(engine.manifest)equivalent(engine.manifest.sources,SOURCE_PINS,'Recorded '+role+' upstream revisions');
  }
  if(config['baseline-sha256'])assert.equal(manifest.engines.baseline.manifestSHA256,config['baseline-sha256'],'Declared baseline replay lock');
  const resultBytes=await readFile(join(archive,'results.json')),summaryBytes=await readFile(join(archive,'summary.json'));
  checksum(resultBytes,manifest.resultsSHA256,'Results index');checksum(summaryBytes,manifest.summarySHA256,'Summary');
  const recorded=JSON.parse(resultBytes),recordedSummary=JSON.parse(summaryBytes);
  assert.ok(Array.isArray(recorded),'Results index array');
  const expectedPairs=plan.forwardPairs+plan.fitPairs;
  assert.equal(recorded.length,expectedPairs,'Every planned pair retained, including failures');
  assert.equal(manifest.completedPairs,expectedPairs,'Declared completed-pair count');
  const recomputed=[],expectedRaw=[];let pairIndex=0,executionFailuresRetained=0,validationFailuresRecomputed=0,constructionFailuresRecomputed=0;
  async function replayRaw(indexed,role,identity,command) {
    assert.ok(indexed?.evidence,'Raw evidence reference required for '+role);
    const {evidence,...saved}=indexed;
    if(role==='original-time-capped'){delete saved.comparisonScope;delete saved.pairedWithCount;}
    const filename=String(expectedRaw.length+1).padStart(6,'0')+'-'+role+'.json.gz';
    assert.equal(evidence.rawFile,'raw/'+filename,'Ordered unique raw filename; no path traversal');expectedRaw.push(filename);
    const gzip=await readFile(join(archive,'raw',filename));checksum(gzip,evidence.gzipSHA256,'Compressed raw '+filename);
    const bytes=gunzipSync(gzip);checksum(bytes,evidence.rawSHA256,'Decoded raw '+filename);
    const raw=JSON.parse(bytes);assert.equal(raw.role,role,'Raw engine role');equivalent(raw.identity,identity,'Raw planned identity');
    checksum(JSON.stringify(raw.command),evidence.commandSHA256,'Saved command '+filename);
    checksum(JSON.stringify(command),evidence.commandSHA256,'Independently regenerated command '+filename);
    equivalent(raw.command,command,'Saved command matches independent truth/measurement plan');
    assert.ok(Object.hasOwn(raw,'result'),'Raw execution result or explicit null required');
    let summary;
    if(raw.result===null) {
      // A failed external process has no recoverable solver output. Its recorded
      // failure is retained and hash-checked, never converted into a success or
      // advertised as a reproduced failure cause.
      assert.equal(raw.summary?.valid,false,'Missing result retains failure');assert.equal(raw.summary.stage,'execution','Missing result was execution failure');
      assert.ok(typeof raw.summary.error==='string'&&raw.summary.error.trim(),'Execution error retained');
      summary={valid:false,stage:'execution',error:raw.summary.error};executionFailuresRetained++;
    } else {
      try {summary=evaluateOutput(command,raw.result);}
      catch(error){summary={valid:false,stage:'validation',error:firstLine(error)};validationFailuresRecomputed++;}
    }
    equivalent(raw.summary,summary,'Raw scientific validation independently recomputed');
    equivalent(saved,summary,'Indexed engine summary agrees with raw evidence');
    return {...summary,evidence};
  }
  async function replayPair(unit,kind,settings) {
    const {c,arc}=unit,row=recorded[pairIndex++],{identity,command,failure}=prepare(c,arc,kind,settings,config,manifest.engines);
    const {baseline,candidate,comparison,originalDiagnostic,...recordedIdentity}=row;
    equivalent(recordedIdentity,identity,'Ordered case/arc/settings identity matches declared plan');
    if(failure) {
      assert.equal(baseline,undefined,'Construction failure has no baseline output');assert.equal(candidate,undefined,'Construction failure has no candidate output');
      assert.equal(originalDiagnostic,undefined,'Construction failure has no diagnostic output');equivalent(comparison,failure,'Construction/coverage failure retained');
      recomputed.push({...identity,comparison:failure});constructionFailuresRecomputed++;return;
    }
    const b=await replayRaw(baseline,'baseline',identity,command),cnd=await replayRaw(candidate,'candidate',identity,command);
    const result={...identity,baseline:b,candidate:cnd,comparison:scientificComparison(b,cnd,kind,c.applicability,config['fit-gate'])};
    equivalent(comparison,result.comparison,'Paired scientific comparison independently recomputed');
    if(manifest.engines.original&&kind==='fit') {
      const diagnostic=await replayRaw(originalDiagnostic,'original-time-capped',identity,command);
      assert.equal(originalDiagnostic.comparisonScope,'Diagnostic only; different ranging CPU cap. Excluded from parity and overall pass.','Original time-cap diagnostic scope');
      diagnostic.comparisonScope=originalDiagnostic.comparisonScope;
      if(diagnostic.valid&&b.valid)diagnostic.pairedWithCount=comparePair(b,diagnostic,{kind,applicability:c.applicability,fitGate:'report'});
      equivalent(originalDiagnostic.pairedWithCount??null,diagnostic.pairedWithCount??null,'Original/count diagnostic comparison');result.originalDiagnostic=diagnostic;
    } else assert.equal(originalDiagnostic,undefined,'No undeclared original-native diagnostic');
    recomputed.push(result);
  }
  for(const unit of units) {
    if(config.checks!=='fit')await replayPair(unit,'forward',{noise:'exact',seed:0});
    if(config.checks!=='forward')for(const settings of unit.settings)await replayPair(unit,'fit',settings);
  }
  assert.equal(manifest.rawFiles,expectedRaw.length,'Declared raw-file count');
  const entries=await readdir(join(archive,'raw'),{withFileTypes:true});
  assert.ok(entries.every(entry=>entry.isFile()),'Raw inventory contains only regular files');
  assert.deepEqual(entries.map(entry=>entry.name).sort(),expectedRaw.slice().sort(),'Complete exact raw inventory; no missing, duplicated or orphaned output');
  const summary=summarize(recomputed);summary.complete=recomputed.length===expectedPairs;summary.pass&&=summary.complete;
  summary.validationScope={checks:config.checks,forwardControlsRun:config.checks!=='fit',inverseFitsRun:config.checks!=='forward',
    fullSelectedProtocolPassed:summary.pass&&config.checks==='all'&&config['fit-gate']==='parity',fitGate:config['fit-gate'],
    interpretation:'Pass applies only to explicitly selected checks and cases; fit-only runs do not validate the independent forward-state reference floor.'};
  equivalent(recordedSummary,summary,'Scientific summary independently recomputed');
  assert.equal(manifest.status,summary.pass?'passed':'failed','Recorded pass/fail status agrees with retained evidence');
  return {verified:true,scientificPass:summary.pass,manifestSHA256:sha(manifestBytes),replayerSHA256:sha(await readFile(fileURLToPath(import.meta.url))),
    sourcePolicy:'Strict recorded current-source hashes; no historical-source migration or changed-policy recomputation.',
    archiveAuthenticity:manifestSHA256?'Externally supplied manifest hash checked.':'Internal hash-chain consistency only; no external signature/manifest anchor supplied.',
    pairs:recomputed.length,rawFiles:expectedRaw.length,executionFailuresRetained,validationFailuresRecomputed,constructionFailuresRecomputed,
    limitation:'No solver/API calls. Process failures without raw result are retained rather than reproduced; only error first lines are compared across stack locations. Source acquisition/normalization is validated separately by regression-corpus/verify.mjs.',summary:jsonValue(summary)};
}
export const usage='Usage: node experiments/regression-suite/replay.mjs --directory DIR [--corpus PATH] [--manifest-sha256 HEX]\nVerify/recompute a completed suite archive offline. A verified archive may correctly retain failed scientific gates.\n';
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  try {
    const args=process.argv.slice(2),options={};
    if(args.length===1&&args[0]==='--help')console.log(usage);
    else {
      for(let i=0;i<args.length;i+=2) {
        assert.ok(['--directory','--corpus','--manifest-sha256'].includes(args[i])&&args[i+1]&&!args[i+1].startsWith('--'),usage);
        const key=args[i]==='--manifest-sha256'?'manifestSHA256':args[i].slice(2);assert.ok(!Object.hasOwn(options,key),'Duplicate option '+args[i]);options[key]=args[i+1];
      }
      console.log(JSON.stringify(await replaySuite(options),null,2));
    }
  } catch(error) {console.error(String(error.stack||error));process.exitCode=1;}
}
