// SPDX-License-Identifier: GPL-2.0-or-later
import {test,expect} from '@playwright/test';
import {createServer} from 'node:http';
import {readFile} from 'node:fs/promises';
import {resolve,join,extname} from 'node:path';
import {loadCases} from '../../benchmark/cases.mjs';
import {validate} from '../../benchmark/accuracy.mjs';
const root=resolve('.'),dist=resolve(process.env.FIND_ORB_BROWSER_DIST||'dist-compact');
const manifest=JSON.parse(await readFile(join(dist,'manifest.json'),'utf8'));
const cases=await loadCases();
let server,base;
test.beforeAll(async()=>{
  server=createServer(async(req,res)=>{
    try {
      const path=new URL(req.url,'http://localhost').pathname;
      if(path==='/') {res.setHeader('Content-Type','text/html');res.end('<!doctype html><title>Find_Orb browser verification</title>');return;}
      let file;
      if(/^\/src\/[a-z.-]+\.js$/.test(path))file=join(root,path);
      else if(['/assets/find-orb-worker.js','/assets/find-orb.data.gz'].includes(path))file=join(dist,path.slice('/assets/'.length));
      else {res.writeHead(404).end();return;}
      res.setHeader('Content-Type',extname(file)==='.js'?'text/javascript':'application/gzip');
      res.end(await readFile(file));
    } catch {res.writeHead(500).end();}
  });
  await new Promise(r=>server.listen(0,'127.0.0.1',r));base='http://127.0.0.1:'+server.address().port;
});
test.afterAll(async()=>{await new Promise(r=>server.close(r));});

test('automatic compressed data loading runs real worker with accurate repeatable output',async({page})=>{
  await page.goto(base);
  const command=cases.find(c=>c.id==='ceres-30d');
  const {first,second}=await page.evaluate(async({manifest,command})=>{
    const {createSessionFromUrls}=await import('/src/index.js');
    const session=await createSessionFromUrls({workerURL:'/assets/find-orb-worker.js',dataURL:'/assets/find-orb.data.gz',compression:'gzip',manifest});
    try {
      const first=await session.execute(command.args,command.files,command.outputs);
      const second=await session.execute(command.args,command.files,command.outputs);
      return {first,second};
    } finally {session.close();}
  },{manifest,command});
  validate(command,first);validate(command,second);
  expect(first.files['/job/vectors.txt']).toEqual(second.files['/job/vectors.txt']);
});

test('actual worker cancellation rejects work and closes the session',async({page})=>{
  await page.goto(base);
  const errors=await page.evaluate(async({manifest,command})=>{
    const {createSessionFromUrls}=await import('/src/index.js');
    const session=await createSessionFromUrls({workerURL:'/assets/find-orb-worker.js',dataURL:'/assets/find-orb.data.gz',compression:'gzip',manifest});
    const controller=new AbortController();
    try {
      const active=session.execute(command.args,command.files,command.outputs,controller.signal).then(()=> 'unexpected success',e=>e.message);
      setTimeout(()=>controller.abort(),20);
      const first=await active;
      const second=await session.execute(command.args,command.files,command.outputs).then(()=> 'unexpected success',e=>e.message);
      return [first,second];
    } finally {session.close();}
  },{manifest,command:cases.find(c=>c.id==='ceres-heldout-fit')});
  expect(errors).toEqual(['Calculation cancelled.','Calculation cancelled.']);
});
