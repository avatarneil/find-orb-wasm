// SPDX-License-Identifier: GPL-2.0-or-later
import {createHash} from 'node:crypto';
import {EPHEMERIS} from '../../build/pins.mjs';
import {separationArcsec} from '../../benchmark/accuracy.mjs';
export {separationArcsec};
const rad=Math.PI/180,arcsecondsPerRadian=180/Math.PI*3600;
const norm=v=>Math.hypot(...v);
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
export const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
export function finiteFields(text,count,separator=',') {
  const tokens=text.trim().split(separator).map(s=>s.trim());
  if(tokens.length!==count||tokens.some(s=>!/^[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?$/.test(s)))
    throw new Error('Malformed numeric diagnostic fields.');
  const values=tokens.map(Number);if(values.some(v=>!Number.isFinite(v)))throw new Error('Nonfinite numeric diagnostic.');
  return values;
}
export const median=values=>quantile(values,.5);
export function quantile(values,p) {
  if(!values.length||values.some(v=>!Number.isFinite(v))||p<0||p>1)throw new Error('Invalid quantile input.');
  const sorted=values.slice().sort((a,b)=>a-b),at=p*(sorted.length-1),i=Math.floor(at);
  return sorted[i]+(sorted[Math.min(i+1,sorted.length-1)]-sorted[i])*(at-i);
}
export function direction({RA,Dec}) {return [Math.cos(Dec*rad)*Math.cos(RA*rad),Math.cos(Dec*rad)*Math.sin(RA*rad),Math.sin(Dec*rad)];}
// Exponential map on the sphere; injected noise is in east/north arcseconds,
// with no RA-wrap or cos(dec) singularity in the resulting direction.
export function angularOffset(point,eastArcsec,northArcsec) {
  const [ra,dec]=[point.RA*rad,point.Dec*rad],x=direction(point);
  const east=[-Math.sin(ra),Math.cos(ra),0],north=[-Math.sin(dec)*Math.cos(ra),-Math.sin(dec)*Math.sin(ra),Math.cos(dec)];
  const a=eastArcsec/arcsecondsPerRadian,b=northArcsec/arcsecondsPerRadian,theta=Math.hypot(a,b),s=theta?Math.sin(theta)/theta:1;
  const v=x.map((c,i)=>c*Math.cos(theta)+s*(a*east[i]+b*north[i]));
  return {...point,RA:((Math.atan2(v[1],v[0])/rad)%360+360)%360,Dec:Math.atan2(v[2],Math.hypot(v[0],v[1]))/rad};
}
export function normalGenerator(seed) {
  let state=parseInt(sha(String(seed)).slice(0,8),16)>>>0;
  function uniform() {state=(Math.imul(state,1664525)+1013904223)>>>0;return (state+.5)/4294967296;}
  return ()=>Math.sqrt(-2*Math.log(uniform()))*Math.cos(2*Math.PI*uniform());
}
export const noiseScenarios=Object.freeze({
  exact:{independentSigma:0,commonSigma:0,outlierArcsec:0},
  gaussian:{independentSigma:.2,commonSigma:0,outlierArcsec:0},
  biased:{independentSigma:.2,commonSigma:.3,outlierArcsec:0},
  contaminated:{independentSigma:.2,commonSigma:0,outlierArcsec:3},
});
export function noisyObservations(c,scenario,replicate=0) {
  const spec=noiseScenarios[scenario];if(!spec)throw new Error('Unknown noise scenario.');
  const gaussian=normalGenerator(c.id+':astrometry:'+replicate);
  // Shared draws across scenarios/budgets/selectors improve paired comparisons.
  const bias=[gaussian(),gaussian()];
  const followupCommonArcsec=[];
  const all=[...c.observations,...c.holdout].map((point,index)=>{
    // One common error per original tracklet. Follow-up points get independent
    // common errors because they are from distinct synthetic observing visits.
    const common=index<c.observations.length?bias:[gaussian(),gaussian()];
    if(index>=c.observations.length)followupCommonArcsec.push(common.map(x=>x*spec.commonSigma));
    const east=spec.independentSigma*gaussian()+spec.commonSigma*common[0]+(index===4?spec.outlierArcsec:0);
    const north=spec.independentSigma*gaussian()+spec.commonSigma*common[1];
    return angularOffset(point,east,north);
  });
  return {observations:all.slice(0,c.observations.length),followup:all.slice(c.observations.length),followupCommonArcsec};
}
function sex(degrees,ra) {
  const factor=ra?1000:100,ticks=Math.round(Math.abs(degrees)/(ra?15:1)*3600*factor);
  return (ra?'':degrees<0?'-':'+')+String(Math.floor(ticks/(3600*factor))%(ra?24:100)).padStart(2,'0')+' '+
    String(Math.floor(ticks/(60*factor))%60).padStart(2,'0')+' '+((ticks%(60*factor))/factor).toFixed(ra?3:2).padStart(ra?6:5,'0');
}
export function mpcRecord(point,designation='SYN0001',observer='F52') {
  if(!/^[A-Z0-9]{7}$/.test(designation)||!/^\w{3}$/.test(observer)||![point.jdUtc,point.RA,point.Dec].every(Number.isFinite)||Math.abs(point.Dec)>90)
    throw new Error('Invalid synthetic MPC record.');
  // Quantize time to the MPC six-decimal-day grid before finding its calendar
  // date so rounding across midnight also carries into the next month/year.
  const ticks=Math.round((point.jdUtc-2440587.5)*1e6),days=Math.floor(ticks/1e6),fraction=ticks-days*1e6;
  const date=new Date(days*86400000).toISOString(),day=Number(date.slice(8,10))+fraction/1e6;
  const record=('     '+designation+'  C'+date.slice(0,4)+' '+date.slice(5,7)+' '+day.toFixed(6).padStart(9,'0')+
    sex(((point.RA%360)+360)%360,true)+sex(point.Dec,false)).padEnd(77)+observer;
  if(record.length!==80)throw new Error('MPC record must be 80 columns.');
  return record;
}
export function fitCommand(c,{budget=100,selection='position',scenario='gaussian',replicate=0,arc='one-hour',experimental=false}={}) {
  if(!Number.isInteger(budget)||budget<11||budget>10000)throw new Error('Invalid ranging budget.');
  if(!['position','phase6d','min-rms','predictive1d'].includes(selection))throw new Error('Invalid selection.');
  if(!['one-hour','plus-six-hours','plus-one-day','two-tracklets','three-tracklets'].includes(arc))throw new Error('Invalid arc.');
  if(selection!=='position'&&!experimental)throw new Error('Research selectors require the experimental engine.');
  const noise=noisyObservations(c,scenario,replicate),points=[0,2,4,6].map(i=>noise.observations[i]);
  if(arc==='plus-six-hours'||arc==='plus-one-day') {
    const index=arc==='plus-six-hours'?0:1,truth=c.holdout[index];
    if(!(truth.altitudeDeg>=20)||truth.solarPresence!=='')throw new Error('Requested follow-up is not observable under the fixed visibility rule.');
    points.push(noise.followup[index]);
  }
  if(arc==='two-tracklets'||arc==='three-tracklets') {
    const spec=noiseScenarios[scenario];
    for(const night of arc==='two-tracklets'?[2]:[2,3]) {
      const source=c.followupTracklets?.['night'+night];
      if(!source||!c.followupTracklets['night'+night+'Available']||source.some(p=>p.altitudeDeg<20||p.solarPresence!==''))
        throw new Error('Fixed night '+night+' tracklet is not observable under the protocol.');
      const gaussian=normalGenerator(c.id+':night-'+night+':'+replicate);
      const common=night===2?noise.followupCommonArcsec[1]:[gaussian()*spec.commonSigma,gaussian()*spec.commonSigma];
      for(let i=0;i<source.length;i++) {
        // Reuse the exact +24h noisy point and common bias from the single-point
        // intervention. Additional positions have independent exposure noise.
        points.push(night===2&&i===0?noise.followup[1]:angularOffset(source[i],
          spec.independentSigma*gaussian()+common[0],spec.independentSigma*gaussian()+common[1]));
      }
    }
  }
  const records=points.map(p=>mpcRecord(p,'SYN0001',c.observer));
  const start=c.epochJdUtc,count=29,stepDays=.25;
  const env=['JPL_FILENAME=/engine/'+EPHEMERIS.filename,'LINUX_JPL_FILENAME=/engine/'+EPHEMERIS.filename,
    'PERTURBERS=7fe','VECTOR_OPTS=1,1,1',"MOTION_UNITS='/hr",'JSON_ELEMENTS_NAME=/job/elements.json','JSON_EPHEM_NAME=/job/sky.json',
    'MAX_SR_ORBITS='+budget,'SETTINGS=N,4,12,0,2,1','SETTINGS2=1,99,0,0,0','IOD_TIMEOUT=0',
    'EPHEM_START=JD'+start,'EPHEM_STEPS='+count,'EPHEM_STEP_SIZE=6h','EPHEMERIS_TIMESCALE=UTC','SIGMA_MULTIPLIER=1',
    // Both engine loaders set cwd to the private job directory. A relative
    // template avoids upstream's 80-byte pathname limit on macOS temporary paths.
    'OFFSET_FILES=offsets/%t.txt',...(experimental?['SR_SELECTION='+(selection==='predictive1d'?'position':selection),
      'SR_CANDIDATES_FILE=/job/candidates.csv','SR_FAMILY_FILE=/job/family.csv','SR_BATCHES_FILE=/job/batches.csv']:[])];
  return {args:['/job/observations.mpc','-x/engine/data/','-D/engine/data/environ.def','-D/job/job.env','-O/job/','-i','-q','-V','-h0',
    '-tEJD'+c.epochJdTt,'-e/job/sky.txt','-E3,9,16,17,20,25','-C'+c.observer],
    files:{'/job/observations.mpc':'COM Posn sigma 0.2\n'+records.join('\n')+'\n','/job/job.env':env.join('\n')+'\n',
      ...(experimental?{'/job/candidates.csv':'','/job/family.csv':'','/job/batches.csv':''}:{})},
    outputs:['/job/elements.txt','/job/elements.json','/job/sky.json','/job/offsets/',...(experimental?['/job/candidates.csv','/job/family.csv','/job/batches.csv']:[])],
    designation:'SYN0001',start,count,stepDays,observationCount:points.length,lastObservationJdUtc:points.at(-1).jdUtc};
}
// Two-body osculating invariants of a heliocentric J2000 ecliptic state. Solar
// Gaussian gravitational constant matches the upstream convention. Inverse a
// remains finite at the parabolic boundary, unlike semimajor axis itself.
export function stateElements(state) {
  if(state.length!==6||!state.every(Number.isFinite))throw new Error('Invalid state.');
  const r=state.slice(0,3),v=state.slice(3),radius=norm(r),mu=.01720209895**2;
  if(!(radius>0))throw new Error('Zero position.');
  const h=cross(r,v),hn=norm(h),ev=cross(v,h).map((x,i)=>x/mu-r[i]/radius),e=norm(ev);
  const inverseA=2/radius-dot(v,v)/mu;
  return {inverseA,a:inverseA?1/inverseA:null,e,q:hn**2/mu/(1+e),i:Math.atan2(Math.hypot(h[0],h[1]),h[2])/rad};
}
export function elementErrors(estimate,truth) {
  return {inverseA:Math.abs(1/estimate.a-1/truth.a),e:Math.abs(estimate.e-truth.e),q:Math.abs(estimate.q-truth.q),i:Math.abs(estimate.i-truth.i)};
}
export function skyEnsembleMetrics(points,truth) {
  if(!points.length)throw new Error('Empty predictive ensemble.');
  const vectors=points.map(direction),y=direction(truth),center=vectors.reduce((a,v)=>a.map((x,i)=>x+v[i]),[0,0,0]),n=norm(center);
  if(n<1e-12)throw new Error('Undefined spherical mean.');
  const mean={RA:((Math.atan2(center[1],center[0])/rad)%360+360)%360,Dec:Math.atan2(center[2],Math.hypot(center[0],center[1]))/rad};
  const radius90=quantile(points.map(p=>separationArcsec(p,mean)),.9),error=separationArcsec(mean,truth);
  const distance=(a,b)=>norm(a.map((x,i)=>x-b[i]))*arcsecondsPerRadian;
  const first=vectors.reduce((s,x)=>s+distance(x,y),0)/vectors.length;
  let pair=0;for(let i=0;i<vectors.length;i++)for(let j=0;j<i;j++)pair+=distance(vectors[i],vectors[j]);
  return {candidateCount:points.length,meanErrorArcsec:error,radius90Arcsec:radius90,inside90Radius:error<=radius90,
    energyScoreChordArcsec:first-pair/vectors.length**2,probabilityCalibrated:false};
}
