#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
// Replay the archived study's postprocessing. No engine is loaded or executed.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {resolve,join,dirname,relative,basename} from 'node:path';
import {fileURLToPath} from 'node:url';
import {gunzipSync} from 'node:zlib';
import {evaluate,candidateRows,offsetEnsemble} from './run.mjs';
import {selectPredictive,familyRows} from './predictive.mjs';
import {fitCommand,finiteFields,sha} from './methods.mjs';
import {skyRows} from '../../benchmark/accuracy.mjs';

const repository=resolve(dirname(fileURLToPath(import.meta.url)),'../..');
const groups=['development-v2','heldout-v2','followup-v2','tracklets-v3','heldout-wasm-v2'];
const expectedCounts=[240,320,140,84,12];
const scientificFields=['valid','observations','uncertaintyMethod','excluded','elements','invalidReason',
  'elementErrors','predictions','candidates','selectorApplied','eligibleSelectorComparison','search',
  'predictive','errorStage','solverCompleted','error'];
const sourceFields={methodsSHA256:'methods.mjs',runnerSHA256:'run.mjs',
  protocolSHA256:'protocol.json',predictiveSHA256:'predictive.mjs'};
const currentSourceFiles=['experiments/short-arcs/replay.mjs','experiments/short-arcs/run.mjs',
  'experiments/short-arcs/methods.mjs','experiments/short-arcs/predictive.mjs',
  'benchmark/accuracy.mjs','benchmark/cases.mjs','build/pins.mjs'];
const firstLine=value=>String(value).split('\n')[0];

// The scientific comparison is exact in JSON's number representation; only
// stack locations, wall times, and descriptive metadata are omitted. In
// particular there is no tolerance for different elements, forecasts or scores.
function scientificSummary(summary,compactObservations=false) {
  const result=Object.fromEntries(scientificFields.filter(k=>Object.hasOwn(summary,k)).map(k=>[k,summary[k]]));
  if(result.error)result.error=firstLine(result.error);
  if(result.predictive) {
    const {description,...values}=result.predictive;
    result.predictive=values;
  }
  if(compactObservations&&result.observations)
    result.observations={count:result.observations.count,used:result.observations.used};
  return JSON.parse(JSON.stringify(result));
}

function finiteNumbers(value,path) {
  if(typeof value==='number')assert.ok(Number.isFinite(value),path+' must be finite');
  else if(value&&typeof value==='object')for(const [key,child]of Object.entries(value))finiteNumbers(child,path+'.'+key);
}

// Report the first differing path without dumping complete raw observations.
function exact(actual,expected,path='value') {
  if(actual===expected)return;
  if(actual&&expected&&typeof actual==='object'&&typeof expected==='object') {
    assert.equal(Array.isArray(actual),Array.isArray(expected),path+' container type');
    assert.deepEqual(Object.keys(actual).sort(),Object.keys(expected).sort(),path+' keys');
    for(const key of Object.keys(expected))exact(actual[key],expected[key],path+'.'+key);
  } else assert.fail(path+': expected '+JSON.stringify(expected)+', got '+JSON.stringify(actual));
}

function executableCommand(command) {
  assert.ok(command&&Array.isArray(command.args)&&command.files&&Array.isArray(command.outputs),'complete stored command');
  return {args:command.args,files:command.files,outputs:command.outputs};
}

// This engine has no solver, process, network, or engine-loader fallback. A
// changed selected state, vector epoch, input byte or requested output fails.
export function storedEngine(raw) {
  const steps=raw.predictionRaw?[
    {command:raw.predictionRaw.transferCommand,result:raw.predictionRaw.transferRaw},
    {command:raw.predictionCommand,result:raw.predictionRaw},
  ]:[];
  let calls=0;
  return {
    async execute(command) {
      assert.ok(calls<steps.length,'unexpected propagation request during offline replay');
      const step=steps[calls];
      exact(executableCommand(command),executableCommand(step.command),'propagation['+calls+']');
      // Epoch/count metadata is independently checked as well as executable inputs.
      exact(command,step.command,'propagationMetadata['+calls+']');
      assert.ok(step.result,'stored propagation output exists');
      assert.equal(step.result.exitCode,0,'stored propagation exit code');
      calls++;
      return structuredClone(step.result);
    },
    finish() {assert.equal(calls,steps.length,'all stored propagation steps consumed');return calls;},
  };
}

function validateStoredNumbers(command,result) {
  assert.equal(result.exitCode,0,'stored solver exit code');
  const elements=JSON.parse(result.files['/job/elements.json']);
  finiteNumbers(elements,'elements');
  const sky=skyRows(result);
  assert.equal(sky.length,command.count,'stored sky row count');
  for(const [index,row]of sky.entries()) {
    finiteNumbers(row,'sky['+index+']');
    assert.ok([row.JD,row.RA,row.Dec,row.delta].every(Number.isFinite),'finite stored sky coordinates');
    assert.ok(Math.abs(row.JD-command.start-index*command.stepDays)<1e-7,'stored sky time grid');
  }
  // evaluate returns early for a scientifically invalid fit. Its diagnostics
  // still have to parse under the hardened, nonempty numeric-token grammar.
  const candidates=candidateRows(result.files['/job/candidates.csv']||'');
  const familyText=result.files['/job/family.csv']||'';
  const family=familyText.trim()?familyRows(familyText):[];
  const batchText=result.files['/job/batches.csv']||'';
  let batches=0,attempts=0;
  if(batchText.trim()) {
    const lines=batchText.trim().split('\n');
    assert.equal(lines.shift(),'starting_orbit,n_observations,max_orbits,attempted,successful,epoch_tt_jd');
    for(const line of lines) {
      const row=finiteFields(line,6);batches++;attempts+=row[3];
      assert.ok(row.slice(0,5).every(Number.isInteger),'integer ranging loop counters');
      assert.ok(row[3]>=0&&row[4]>=0&&row[4]<=row[3],'successful attempts bounded by actual attempts');
    }
  }
  let offsetFiles=0;
  for(const [name,text]of Object.entries(result.files))if(name.startsWith('/job/offsets/')) {
    const jd=Number(/^# JD ([0-9.]+)/.exec(text)?.[1]);
    const nominal=sky.find(row=>Math.abs(row.JD-jd)<.00000051);assert.ok(nominal,'stored offset sky epoch');
    offsetEnsemble(text,nominal);offsetFiles++;
  }
  return {candidates:candidates.length,family:family.length,batches,actualAttempts:attempts,offsetFiles};
}

function declaredPlans(corpus,config) {
  const result=[];
  for(const c of corpus.cases.filter(c=>config.split==='all'||c.split===config.split))
    for(const scenario of config.scenarios.split(','))
      for(const replicate of config.replicates.split(',').map(Number)) {
        if(scenario==='exact'&&replicate!==0)continue;
        for(const budget of config.budgets.split(',').map(Number))
          for(const selection of config.selections.split(','))for(const arc of config.arcs.split(',')) {
            const settings={scenario,replicate,budget,selection,arc};
            result.push({c,settings,id:[c.id,scenario,replicate,budget,selection,arc].join('_')});
          }
      }
  return result;
}

async function historicalSources(root,restoredRepository,manifest) {
  const matches={};
  for(const [field,name]of Object.entries(sourceFields))if(manifest[field]) {
    // Old selection sources and the source captured when the archive was built
    // are both retained; current checkout hashes need not equal historical ones.
    const candidates=[join(root,'selection-v2-sources',name),join(restoredRepository,'experiments/short-arcs',name)];
    const matching=[];
    for(const path of candidates)try {
      if(sha(await readFile(path))===manifest[field])matching.push(relative(restoredRepository,path));
    } catch(error) {if(error.code!=='ENOENT')throw error;}
    assert.ok(matching.length,'exact archived source snapshot for '+field);
    matches[field]={sha256:manifest[field],paths:matching};
  }
  return matches;
}

export async function replay(root=resolve(repository,'results/local/short-arcs-restored/results/local/short-arcs'),
  output=resolve(repository,'results/local/short-arcs/replay-report.json')) {
  root=resolve(root);output=resolve(output);
  const restoredRepository=resolve(root,'../../..');
  const startedAt=new Date().toISOString();
  const currentSources=Object.fromEntries(await Promise.all(currentSourceFiles.map(async path=>[path,sha(await readFile(join(repository,path)))])));
  const corpusPath=join(repository,'experiments/short-arcs/fixtures/observable-corpus.json');
  const trackletsPath=join(repository,'experiments/short-arcs/fixtures/followup-tracklets.json');
  const corpusText=await readFile(corpusPath,'utf8'),corpus=JSON.parse(corpusText);
  const trackletsText=await readFile(trackletsPath,'utf8'),tracklets=JSON.parse(trackletsText);
  for(const c of corpus.cases)c.followupTracklets=tracklets.cases.find(t=>t.id===c.id||t.caseId===c.id);
  const report={schemaVersion:1,startedAt,archiveRoot:root,output,currentSourceSHA256:currentSources,
    corpusSHA256:sha(corpusText),trackletsSHA256:sha(trackletsText),
    policy:{engineExecution:'None. Only stored propagation outputs from exactly matched commands are returned.',
      comparison:'Exact equality after JSON serialization; no numerical tolerance. JSON treats negative zero as zero.',
      omitted:['wall times','error-stack file locations','predictive description','incidental source/host metadata'],
      scope:'All 796 declared fit records, including unavailable commands and scientifically invalid completed fits. Controls and Jacobian records are outside this replay.'},
    groups:[],planned:0,checked:0,passed:0,failed:0,valid:0,unavailableCommands:0,invalidCompletedFits:0,
    rawHashesVerified:0,mpcInputsIdentical:0,predictivePropagationCalls:0,failures:[]};
  for(const [groupIndex,group]of groups.entries()) {
    const directory=join(root,group),manifestBytes=await readFile(join(directory,'manifest.json')),
      manifest=JSON.parse(manifestBytes);
    const indexBytes=await readFile(join(directory,'results.json')),rows=JSON.parse(indexBytes);
    const plans=declaredPlans(corpus,manifest.config);
    assert.equal(manifest.corpusSHA256,sha(corpusText),'historical corpus bytes');
    if(manifest.trackletsSHA256)assert.equal(manifest.trackletsSHA256,sha(trackletsText),'historical follow-up bytes');
    assert.equal(plans.length,expectedCounts[groupIndex],'declared group count');
    assert.equal(manifest.plannedRuns,plans.length);assert.equal(manifest.completedRuns,plans.length);
    assert.equal(rows.length,plans.length,'all planned records retained');
    assert.equal(new Set(rows.map(row=>row.id)).size,rows.length,'distinct planned records');
    const status={group,planned:plans.length,indexSHA256:sha(indexBytes),manifestSHA256:sha(manifestBytes),
      historicalSources:await historicalSources(root,restoredRepository,manifest),
      passed:0,failed:0,valid:0,unavailableCommands:0,invalidCompletedFits:0,records:[]};
    report.groups.push(status);report.planned+=plans.length;
    for(const [index,row]of rows.entries()) {
      const plan=plans[index],record={id:row.id,passed:false};
      report.checked++;
      try {
        exact({id:row.id,caseId:row.caseId,settings:row.settings,object:row.object,split:row.split},
          {id:plan.id,caseId:plan.c.id,settings:plan.settings,object:plan.c.object.name,split:plan.c.split},'declared plan');
        assert.equal(row.rawFile,basename(row.rawFile),'raw filename is local to its group');
        const bytes=gunzipSync(await readFile(join(directory,row.rawFile)));
        assert.equal(sha(bytes),row.rawSHA256,'decoded raw SHA256');report.rawHashesVerified++;
        record.rawSHA256=row.rawSHA256;
        const raw=JSON.parse(bytes);
        exact({id:raw.id,caseId:raw.caseId,settings:raw.settings},{id:row.id,caseId:row.caseId,settings:row.settings},'raw identity');
        exact(scientificSummary(raw.summary,true),scientificSummary(row,true),'raw/index scientific summary');
        let command,commandError;
        try {command=fitCommand(plan.c,{...plan.settings,experimental:manifest.config.engine.endsWith('-experiment')});}
        catch(error) {commandError=error;}
        if(commandError) {
          assert.match(commandError.message,/^Fixed night [23] tracklet is not observable under the protocol\.$/,'known unavailable-command reason');
          exact({command:raw.command,result:raw.result,predictionCommand:raw.predictionCommand,predictionRaw:raw.predictionRaw},
            {command:null,result:null,predictionCommand:null,predictionRaw:null},'unavailable command has no solver output');
          const summary={valid:false,errorStage:'command',solverCompleted:false,error:String(commandError)};
          exact(scientificSummary(summary),scientificSummary(raw.summary),'unavailable-command replay');
          record.kind='unavailable-command';record.reason=commandError.message;
          report.unavailableCommands++;status.unavailableCommands++;
        } else {
          exact(command,raw.command,'rebuilt command');report.mpcInputsIdentical++;
          record.mpcSHA256=sha(command.files['/job/observations.mpc']);
          record.numericOutputs=validateStoredNumbers(command,raw.result);
          let summary=evaluate(plan.c,command,raw.result);
          const engine=storedEngine(raw);
          if(plan.settings.selection==='predictive1d') {
            const prediction=await selectPredictive(plan.c,command,raw.result,summary,engine,{offsetEnsemble,candidateRows});
            summary=prediction.summary;
            exact(prediction.predictionCommand,raw.predictionCommand,'selected prediction command');
          }
          record.predictivePropagationCalls=engine.finish();report.predictivePropagationCalls+=record.predictivePropagationCalls;
          finiteNumbers(summary,'recomputed summary');
          exact(scientificSummary(summary),scientificSummary(raw.summary),'recomputed scientific summary');
          exact(scientificSummary(summary,true),scientificSummary(row,true),'recomputed scientific index');
          if(summary.valid) {
            assert.equal(summary.search.attemptedTotal,record.numericOutputs.batches?record.numericOutputs.actualAttempts:null,'actual attempt totals');
            for(const p of summary.predictions)assert.ok(p.jdUtc>command.lastObservationJdUtc+1e-7,'scored epoch strictly follows fitted data');
            record.kind='valid-fit';report.valid++;status.valid++;
          } else {
            record.kind='invalid-completed-fit';record.reason=summary.invalidReason;
            report.invalidCompletedFits++;status.invalidCompletedFits++;
          }
        }
        record.passed=true;status.passed++;report.passed++;
      } catch(error) {
        record.error=String(error.message||error);status.failed++;report.failed++;
        report.failures.push({group,id:row.id,error:record.error});
      }
      status.records.push(record);
    }
    console.log(JSON.stringify({group,planned:status.planned,passed:status.passed,failed:status.failed}));
  }
  assert.equal(report.planned,796);assert.equal(report.checked,796);
  for(const [path,expected]of Object.entries(currentSources))assert.equal(sha(await readFile(join(repository,path))),expected,'source changed during replay: '+path);
  report.completedAt=new Date().toISOString();report.allPassed=report.failed===0;
  await mkdir(dirname(output),{recursive:true});await writeFile(output,JSON.stringify(report,null,2)+'\n');
  console.log(JSON.stringify({planned:report.planned,passed:report.passed,failed:report.failed,
    valid:report.valid,unavailableCommands:report.unavailableCommands,invalidCompletedFits:report.invalidCompletedFits,
    predictivePropagationCalls:report.predictivePropagationCalls,output}));
  return report;
}

if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  assert.ok(process.argv.length<=4,'Usage: node experiments/short-arcs/replay.mjs [RESTORED_SHORT_ARCS_ROOT] [OUTPUT_JSON]');
  const report=await replay(process.argv[2],process.argv[3]);
  if(!report.allPassed)process.exitCode=1;
}
