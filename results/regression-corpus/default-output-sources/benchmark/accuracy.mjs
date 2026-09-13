import assert from 'node:assert/strict';
import {AU_METERS} from './cases.mjs';
export function separationArcsec(a,b) {
  const rad=Math.PI/180,da=(a.RA-b.RA)*rad,dd=(a.Dec-b.Dec)*rad;
  return 2*Math.asin(Math.min(1,Math.sqrt(Math.sin(dd/2)**2+Math.cos(a.Dec*rad)*Math.cos(b.Dec*rad)*Math.sin(da/2)**2)))/rad*3600;
}
export function parseVectors(text,command) {
  const lines=text.trim().split(/\r?\n/);
  assert.equal(lines.length,command.count+1,'vector row count');assert.match(lines[0],/ 1,1,1 /,'AU, day, ecliptic vector units');
  return lines.slice(1).map((line,i)=>{
    const row=line.trim().split(/\s+/).map(Number);
    assert.equal(row.length,7);assert.ok(row.every(Number.isFinite),'finite state');
    assert.ok(Math.abs(row[0]-command.start-i*command.stepDays)<.0000051,'requested time grid');return row.slice(1);
  });
}
export function skyRows(result) {
  const ephemeris=JSON.parse(result.files['/job/sky.json']).ephemeris;
  assert.equal(ephemeris.count,Object.keys(ephemeris.entries).length);
  return Object.values(ephemeris.entries).sort((a,b)=>a.JD-b.JD);
}
export function validate(command,result) {
  assert.equal(result.exitCode,0);
  const force=/^# Perturbers:\s+([0-9a-f]+).*JPL DE-440.*$/im.exec(result.files['/job/elements.txt']);
  assert.ok(force&&(parseInt(force[1],16)&0x7fe)===0x7fe,'full planetary force model, no ephemeris fallback');
  const metrics={};
  if(command.kind==='vectors') {
    const vectors=parseVectors(result.files['/job/vectors.txt'],command);
    if(command.truth) {
      metrics.horizonsPositionErrorMeters=vectors.map((state,i)=>Math.hypot(...state.slice(0,3).map((x,j)=>x-command.truth[i][j]))*AU_METERS);
      assert.ok(metrics.horizonsPositionErrorMeters[0]<10);assert.ok(Math.max(...metrics.horizonsPositionErrorMeters)<100,'30-day Horizons propagation <100m');
    }
  } else {
    const sky=skyRows(result);assert.equal(sky.length,command.count);
    sky.forEach((row,i)=>{assert.ok([row.JD,row.RA,row.Dec,row.delta].every(Number.isFinite));assert.ok(Math.abs(row.JD-command.start-i*command.stepDays)<1e-7);});
    if(command.truth) {
      metrics.horizonsSkyErrorArcsec=command.truth.map(row=>{
        const s=sky.find(value=>Math.abs(value.JD-Number(row[0]))<1e-7);assert.ok(s,'heldout epoch exists');
        return separationArcsec(s,{RA:Number(row[3]),Dec:Number(row[4])});
      });
      assert.ok(Math.max(...metrics.horizonsSkyErrorArcsec)<.1,'independent Horizons sky <0.1 arcsec');
      if(command.kind==='sky') sky.forEach((s,i)=>{
        const row=command.truth[i];assert.ok(Math.abs(s.delta-Number(row[9]))<1e-6,'range <1e-6 AU');
        assert.ok(Math.abs(s.RAvel*60-Number(row[5]))<.2,'RA rate <0.2 arcsec/h');
        assert.ok(Math.abs(s.decvel*60-Number(row[6]))<.2,'Dec rate <0.2 arcsec/h');
        assert.ok(Math.abs(s.alt-Number(row[8]))<.05,'altitude <0.05 deg');
      });
    }
    if(command.kind==='fit') {
      const fit=JSON.parse(result.files['/job/elements.json']).objects[command.designation];
      assert.ok(fit);assert.equal(fit.observations.count,command.observations);assert.equal(fit.observations.used,command.observations);
      metrics.rmsArcsec=fit.elements.rms_residual;assert.ok(metrics.rmsArcsec<.3);
      if(command.id==='short-arc-fit') {assert.ok(fit.elements['a sigma']>1);assert.ok(sky.at(-1).sigPos>10000,'honest broad short-arc uncertainty');}
    }
  }
  return metrics;
}
export function compare(command,result,reference) {
  const metrics={};
  if(command.kind==='vectors') {
    const a=parseVectors(result.files['/job/vectors.txt'],command),b=parseVectors(reference.files['/job/vectors.txt'],command);
    metrics.maxNativePositionErrorMeters=Math.max(...a.map((s,i)=>Math.hypot(...s.slice(0,3).map((x,j)=>x-b[i][j]))*AU_METERS));
    metrics.maxNativeVelocityErrorMetersPerSecond=Math.max(...a.map((s,i)=>Math.hypot(...s.slice(3).map((x,j)=>x-b[i][j+3]))*AU_METERS/86400));
    assert.ok(metrics.maxNativePositionErrorMeters<1,'native propagation parity <1m');
    assert.ok(metrics.maxNativeVelocityErrorMetersPerSecond<.00001,'native velocity parity <10um/s');
  } else {
    const a=skyRows(result),b=skyRows(reference);assert.equal(a.length,b.length);
    metrics.maxNativeSkyErrorArcsec=Math.max(...a.map((s,i)=>separationArcsec(s,b[i])));
    assert.ok(metrics.maxNativeSkyErrorArcsec<(command.id==='short-arc-fit'?.0001:.001),'native sky parity');
    if(command.kind==='fit') {
      const a=JSON.parse(result.files['/job/elements.json']).objects[command.designation].elements;
      const b=JSON.parse(reference.files['/job/elements.json']).objects[command.designation].elements;
      metrics.nativeElementDeltas={};for(const key of ['a','e','i','M','arg_per','asc_node']) {
        metrics.nativeElementDeltas[key]=Math.abs(a[key]-b[key]);assert.ok(metrics.nativeElementDeltas[key]<1e-6,'native fit element '+key);
      }
    }
  }
  return metrics;
}
