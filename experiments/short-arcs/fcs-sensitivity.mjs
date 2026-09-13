#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {loadWasm} from '../../benchmark/engines.mjs';
import {loadCases} from '../../benchmark/cases.mjs';
import {sha} from './methods.mjs';
const engine=await loadWasm('dist-compact'),baseline=(await loadCases())[0];
const evidence={schemaVersion:1,createdAt:new Date().toISOString(),engine:engine.manifest,
  scriptSHA256:sha(await readFile(new URL(import.meta.url))),
  fixtureSHA256:sha(await readFile(new URL('../../benchmark/fixtures/fcs5000.mpc',import.meta.url))),
  interpretation:'Sensitivity only: independent true orbit is unknown. Runtime observations are not a controlled performance claim.',runs:[]};
for(const budget of [25,50,100,250,500,1000,2000]) {
  const command={...baseline,files:{...baseline.files,'/job/job.env':baseline.files['/job/job.env'].replace('MAX_SR_ORBITS=100','MAX_SR_ORBITS='+budget)}};
  const result=await engine.execute(command),elements=JSON.parse(result.files['/job/elements.json']).objects.FCS5000.elements;
  evidence.runs.push({configuredInitialBatchCapacity:budget,command,result,aAu:elements.a,rmsArcsec:elements.rms_residual});
  console.log(JSON.stringify({budget,a:elements.a,rms:elements.rms_residual}));
}
await mkdir('results/short-arcs',{recursive:true});
await writeFile('results/short-arcs/fcs-sensitivity.json',JSON.stringify(evidence,null,2)+'\n');
