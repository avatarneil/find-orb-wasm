// SPDX-License-Identifier: GPL-2.0-or-later
import assert from 'node:assert/strict';
import test from 'node:test';
import {readFile} from 'node:fs/promises';
import {angularOffset,direction,fitCommand,mpcRecord,noisyObservations,normalGenerator,separationArcsec,skyEnsembleMetrics,stateElements} from './methods.mjs';
import {candidateRows,offsetEnsemble} from './run.mjs';
import {predictiveIndex,familyRows} from './predictive.mjs';
import {compareForecasts} from './analyze.mjs';

test('astrometric noise has correct spherical length at wrap and poles',()=>{
  for(const point of [{RA:359.99999,Dec:0},{RA:0,Dec:89.99999},{RA:180,Dec:-90}]) {
    const moved=angularOffset(point,.3,.4);
    assert.ok(Math.abs(separationArcsec(point,moved)-.5)<1e-7);
    assert.ok(Math.abs(Math.hypot(...direction(moved))-1)<1e-14);
  }
});
test('MPC formatting carries midnight, RA wrap, and signed declination',()=>{
  const jd=Date.parse('2026-12-31T23:59:59.999Z')/86400000+2440587.5;
  const line=mpcRecord({jdUtc:jd,RA:359.99999999,Dec:-.5});
  assert.equal(line.length,80);assert.equal(line.slice(15,32),'2027 01 01.000000');
  assert.equal(line.slice(32,44),'00 00 00.000');assert.equal(line.slice(44,56),'-00 30 00.00');
});
test('deterministic independent normal generator has plausible moments',()=>{
  const a=normalGenerator('fixed'),b=normalGenerator('fixed'),values=Array.from({length:30000},()=>a());
  assert.deepEqual(values.slice(0,20),Array.from({length:20},()=>b()));
  const mean=values.reduce((a,b)=>a+b,0)/values.length,variance=values.reduce((s,x)=>s+(x-mean)**2,0)/values.length;
  assert.ok(Math.abs(mean)<.025);assert.ok(Math.abs(variance-1)<.03);
});
test('osculating invariants recover circular, eccentric, parabolic and hyperbolic states',()=>{
  for(const e of [0,.5,1,1.5])for(const i of [0,30,170]) {
    const q=.8,speed=.01720209895*Math.sqrt((1+e)/q),r=i*Math.PI/180;
    const result=stateElements([q,0,0,0,speed*Math.cos(r),speed*Math.sin(r)]);
    assert.ok(Math.abs(result.e-e)<1e-14);assert.ok(Math.abs(result.q-q)<1e-14);
    assert.ok(Math.abs(result.i-i)<1e-12);assert.ok(Math.abs(result.inverseA-(1-e)/q)<1e-14);
  }
});
test('energy score uses exact empirical pair measure and wrap-safe directions',()=>{
  const truth={RA:0,Dec:0},same=skyEnsembleMetrics([truth],truth);assert.equal(same.energyScoreChordArcsec,0);
  const a={RA:359,Dec:0},b={RA:1,Dec:0};
  const score=skyEnsembleMetrics([a,b],truth),r=180/Math.PI*3600;
  const expected=(2*Math.sin(Math.PI/360)-Math.sin(Math.PI/180)/2)*r;
  assert.ok(Math.abs(score.energyScoreChordArcsec-expected)<1e-8);
  assert.ok(score.meanErrorArcsec<1e-8);assert.equal(score.probabilityCalibrated,false);
});
test('offset inversion preserves upstream RA*cos(dec) convention',()=>{
  const nominal={JD:2461000.5,RA:359.99,Dec:60};
  const points=offsetEnsemble('# JD 2461000.500000 = test\n# SYN0001\n# 2 points; test\n0.0 0.0\n72.0 3.6',nominal);
  assert.ok(Math.abs(points[1].RA-.03)<1e-10);assert.ok(Math.abs(points[1].Dec-60.001)<1e-10);
  assert.throws(()=>offsetEnsemble('# JD 1 = test\n# SYN0001\n# 2 points; test\n0 0\n1 1',nominal));
});
test('truth corpus controls noise reuse, follow-up visibility, and no held-out astrometry leakage',async()=>{
  const corpus=JSON.parse(await readFile(new URL('./fixtures/observable-corpus.json',import.meta.url)));
  for(const c of corpus.cases) {
    const noise=noisyObservations(c,'gaussian'),changed=structuredClone(c);
    changed.holdout=changed.holdout.map(p=>({...p,RA:p.RA+1}));
    const command=fitCommand(c),other=fitCommand(changed);
    assert.equal(command.files['/job/observations.mpc'],other.files['/job/observations.mpc']);
    assert.deepEqual(noise.observations,noisyObservations(c,'gaussian').observations);
    const follow=fitCommand(c,{arc:'plus-one-day'});assert.equal(follow.observationCount,5);
    assert.equal(follow.lastObservationJdUtc,c.holdout[1].jdUtc);
    assert.throws(()=>fitCommand(c,{arc:'plus-six-hours'}),/not observable/);
  }
});
test('candidate parser rejects nonfinite/missing records',()=>{
  assert.deepEqual(candidateRows(''),[]);
  assert.throws(()=>candidateRows('bad\n1,2,3'));
});
test('predictive nearest mean minimizes the stated empirical squared-distance loss',()=>{
  const points=[{RA:359.9,Dec:20},{RA:0,Dec:20},{RA:.3,Dec:20.1},{RA:5,Dec:21}];
  const vectors=points.map(direction),losses=vectors.map(a=>vectors.reduce((s,b)=>s+a.reduce((t,x,i)=>t+(x-b[i])**2,0),0));
  const expected=losses.indexOf(Math.min(...losses));assert.equal(predictiveIndex(points).index,expected);
  assert.equal(predictiveIndex(points.slice().reverse()).index,points.length-1-expected);
  assert.throws(()=>predictiveIndex([]),/Empty/);
});
test('additional tracklets preserve existing measurements and enforce visibility',async()=>{
  const corpus=JSON.parse(await readFile(new URL('./fixtures/observable-corpus.json',import.meta.url)));
  const extra=JSON.parse(await readFile(new URL('./fixtures/followup-tracklets.json',import.meta.url)));
  for(const original of corpus.cases) {
    const c={...original,followupTracklets:extra.cases.find(c=>c.id===original.id)};
    if(!c.followupTracklets.night2Available) {
      assert.throws(()=>fitCommand(c,{arc:'two-tracklets'}),/not observable/);continue;
    }
    for(const scenario of ['exact','gaussian','biased','contaminated']) {
      const single=fitCommand(c,{arc:'plus-one-day',scenario}),two=fitCommand(c,{arc:'two-tracklets',scenario}),three=fitCommand(c,{arc:'three-tracklets',scenario});
      const lines=cmd=>cmd.files['/job/observations.mpc'].trim().split('\n');
      assert.deepEqual(lines(two).slice(0,6),lines(single));assert.deepEqual(lines(three).slice(0,9),lines(two));
      assert.equal(two.observationCount,8);assert.equal(three.observationCount,12);
      assert.ok(three.lastObservationJdUtc<c.holdout[2].jdUtc,'all +3d/+7d prediction targets remain withheld');
    }
  }
});
test('cross-engine parity detects opposite predictions with equal truth error',()=>{
  const a=[{jdUtc:2461000.5,nominal:{RA:1,Dec:0},errorArcsec:3600}];
  const b=[{jdUtc:2461000.5,nominal:{RA:359,Dec:0},errorArcsec:3600}];
  assert.ok(Math.abs(compareForecasts(a,b)-7200)<1e-8);
  assert.throws(()=>compareForecasts(a,[{...b[0],jdUtc:2461001.5}]),/epoch/);
});
test('diagnostic parsers reject missing values and handle whitespace deliberately',()=>{
  const candidateHeader='source_index,epoch_tt_jd,x_au,y_au,z_au,vx_au_day,vy_au_day,vz_au_day,heuristic_score,weighted_rms,n_residuals,rparam,vparam';
  assert.throws(()=>candidateRows(candidateHeader+'\n0,2461000.5,1,0,0,0,.01,0,.5,,8,.2,.3'),/Malformed/);
  const familyHeader='family_index,epoch_tt_jd,x_au,y_au,z_au,vx_au_day,vy_au_day,vz_au_day';
  assert.throws(()=>familyRows(familyHeader+'\n0,2461000.5,1,,0,0,.01,0'),/Malformed/);
  const nominal={JD:2461000.5,RA:0,Dec:0},header='# JD 2461000.500000 = test\n# SYN0001\n# 2 points; test\n0.0 0.0\n';
  const points=offsetEnsemble(header+'72.0  3.6',nominal);assert.ok(Math.abs(points[1].Dec-.001)<1e-12);
  assert.throws(()=>offsetEnsemble(header+'72.0 3.6 4.0',nominal),/Malformed/);
});
