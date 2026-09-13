// GPL-2.0-or-later. Standalone commands adapted from the provenance-pinned tests.
import {readFile} from 'node:fs/promises';
import {EPHEMERIS} from '../build/pins.mjs';
export const AU_METERS=149597870700;
export const rows=document=>document.result.split('$$SOE')[1].split('$$EOE')[0].trim().split('\n').map(line=>line.split(','));
const fixture=async name=>JSON.parse(await readFile(new URL('./fixtures/'+name,import.meta.url),'utf8'));
const base=['-x/engine/data/','-D/engine/data/environ.def','-D/job/job.env','-O/job/','-i','-q','-V','-h0'];
const common=['JPL_FILENAME=/engine/'+EPHEMERIS.filename,'LINUX_JPL_FILENAME=/engine/'+EPHEMERIS.filename,'PERTURBERS=7fe',
  'VECTOR_OPTS=1,1,1',"MOTION_UNITS='/hr",'JSON_ELEMENTS_NAME=/job/elements.json','JSON_EPHEM_NAME=/job/sky.json'];
export function stateCommand(state,{epoch=2461150.5,start=epoch,count=4,step='10d',scale='TT',sky=false}={}) {
  return {args:['-oCER0001','-vJD'+epoch+','+state.join(','),...base,sky?'-E3,9,16,17,20,25':'-E0',sky?'-CF52':'-CSun','-e/job/vectors.txt'],
    files:{'/job/job.env':[...common,'EPHEM_START=JD'+start,'EPHEM_STEPS='+count,'EPHEM_STEP_SIZE='+step,'EPHEMERIS_TIMESCALE='+scale].join('\n')+'\n'},
    outputs:['/job/elements.txt',sky?'/job/sky.json':'/job/vectors.txt'],epoch,start,count,stepDays:step.endsWith('h')?parseFloat(step)/24:parseFloat(step)};
}
function fitCommand(records,{start=2461150.5,count=29,stepHours=6,epoch=2461150.5,sigma=null}={}) {
  return {args:['/job/observations.mpc',...base,'-tEJD'+epoch,'-e/job/sky.txt','-E3,9,16,17,20,25','-CF52'],
    files:{'/job/observations.mpc':(sigma?'COM Posn sigma '+sigma+'\n':'')+records.join('\n')+'\n',
      '/job/job.env':[...common,'MAX_SR_ORBITS=100','SETTINGS=N,4,12,0,2,1','SETTINGS2=1,99,0,0,0','IOD_TIMEOUT=0',
        'EPHEM_START=JD'+start,'EPHEM_STEPS='+count,'EPHEM_STEP_SIZE='+stepHours+'h','EPHEMERIS_TIMESCALE=UTC','SIGMA_MULTIPLIER=1'].join('\n')+'\n'},
    outputs:['/job/elements.txt','/job/elements.json','/job/sky.json'],start,count,stepDays:stepHours/24};
}
function sex(degrees,ra) {
  const factor=ra?1000:100,ticks=Math.round(Math.abs(degrees)/(ra?15:1)*3600*factor);
  return (ra?'':degrees<0?'-':'+')+String(Math.floor(ticks/(3600*factor))).padStart(2,'0')+' '+
    String(Math.floor(ticks/(60*factor))%60).padStart(2,'0')+' '+((ticks%(60*factor))/factor).toFixed(ra?3:2).padStart(ra?6:5,'0');
}
export async function loadCases() {
  const truth=rows(await fixture('ceres-horizons.json')),epoch=Number(truth[0][0]),state=truth[0].slice(2,8).map(Number);
  const records=(await readFile(new URL('./fixtures/fcs5000.mpc',import.meta.url),'utf8')).trimEnd().split('\n');
  const cases=[{id:'short-arc-fit',kind:'fit',...fitCommand(records),designation:'FCS5000',observations:4},
    {id:'ceres-30d',kind:'vectors',...stateCommand(state,{epoch}),truth:truth.map(row=>row.slice(2,8).map(Number))},
    {id:'ceres-topocentric',kind:'sky',...stateCommand(state,{epoch,count:5,step:'6h',scale:'UTC',sky:true}),truth:rows(await fixture('ceres-horizons-f52.json'))}];
  for(const e of [.95,.999999,1.4]) {
    const q=.8,v=Math.sqrt(.01720209895**2*(1+e)/q),inclination=170*Math.PI/180;
    cases.push({id:'eccentricity-'+e,kind:'vectors',...stateCommand([q,0,0,0,v*Math.cos(inclination),v*Math.sin(inclination)],{count:7,step:'10d'}),eccentricity:e});
  }
  const recovery=rows(await fixture('ceres-horizons-recovery.json'));
  const synthetic=recovery.slice(0,7).map(row=>{
    const jd=Number(row[0]),date=new Date((jd-2440587.5)*86400000).toISOString(),day=Number(date.slice(8,10))+(jd+.5)%1;
    return ('     CER0001  C'+date.slice(0,4)+' '+date.slice(5,7)+' '+day.toFixed(6).padStart(9,'0')+sex(Number(row[3]),true)+sex(Number(row[4]),false)).padEnd(77)+'F52';
  });
  cases.push({id:'ceres-heldout-fit',kind:'fit',...fitCommand(synthetic,{start:Number(recovery[6][0]),count:11,stepHours:24,
    epoch:Math.floor((Number(recovery[0][0])+Number(recovery[6][0]))/2-.5)+.5,sigma:.05}),designation:'CER0001',observations:7,truth:recovery.slice(7)});
  return cases;
}
