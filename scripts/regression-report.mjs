#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
import {readFile,writeFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
const corpusBytes=await readFile('experiments/regression-corpus/corpus.json');
const corpus=JSON.parse(corpusBytes), protocol=JSON.parse(await readFile('experiments/regression-corpus/protocol.json','utf8'));
if(!corpus.complete)throw new Error('Finish reference acquisition before publishing its report.');
let checks=null;
try{checks=JSON.parse(await readFile('results/regression-corpus/checks.json','utf8'));}catch(error){if(error.code!=='ENOENT')throw error;}
const esc=s=>String(s??'—').replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;');
const table=(headers,rows)=>'<div class="table-wrap"><table><thead><tr>'+headers.map(x=>'<th>'+esc(x)+'</th>').join('')+'</tr></thead><tbody>'+rows.map(row=>'<tr>'+row.map(x=>'<td>'+esc(x)+'</td>').join('')+'</tr>').join('')+'</tbody></table></div>';
const count=predicate=>corpus.cases.filter(predicate).length;
const objects=corpus.objects, cases=corpus.cases, raw=corpus.provenance.rawFiles;
const arcInstances=cases.reduce((n,c)=>n+c.arcs.length,0);
const stratumRows=protocol.catalog.strata.map(s=>[s.id,objects.filter(o=>o.stratum===s.id).length,
  objects.filter(o=>o.stratum===s.id&&o.split==='development').length,
  objects.filter(o=>o.stratum===s.id&&o.split!=='development').length,
  count(c=>c.object.stratum===s.id),count(c=>c.object.stratum===s.id&&c.applicability.forwardTruth==='model-limited')]);
const rows=cases.map(c=>({id:c.id,name:c.object.name,designation:c.object.designation,stratum:c.object.stratum,split:c.split,
  role:c.role,anchor:c.anchorUtc,applicability:c.applicability.forwardTruth,reason:c.applicability.reason,
  rangeAu:c.astrometry[0].rangeAu,rangeRateKmPerSecond:Math.max(...c.astrometry.map(p=>Math.abs(p.rangeRateKmPerSecond))),
  minElongationDeg:Math.min(...c.astrometry.map(p=>p.elongationDeg)),e:c.initialElements.e,i:c.initialElements.i,q:c.initialElements.q}));
const dynamic=JSON.stringify(rows).replaceAll('<','\\u003c');
const sha=createHash('sha256').update(corpusBytes).digest('hex');
const html=`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Find_Orb regression corpus</title>
<style>:root{color-scheme:light;--ink:#18313c;--muted:#526772;--line:#ccdadd;--accent:#126b65}*{box-sizing:border-box}body{margin:0;background:#f1f5f5;color:var(--ink);font:16px/1.6 system-ui,sans-serif}main{max-width:1220px;margin:auto;padding:36px 24px}h1{font-size:clamp(2rem,4vw,3rem);line-height:1.15;max-width:25ch}h2{font-size:1.45rem;margin-top:0}a{color:#075d84;text-underline-offset:3px}header{padding-bottom:25px;border-bottom:3px solid var(--accent)}.eyebrow{font-size:.82rem;text-transform:uppercase;letter-spacing:.08em;font-weight:750;color:var(--accent)}.cards{display:grid;grid-template-columns:repeat(3,1fr);gap:16px;margin-top:25px}.card,section{background:white;padding:24px;border:1px solid var(--line);border-radius:8px}section{margin:24px 0}.metric{font-size:2rem;font-weight:750;color:var(--accent);display:block}small,footer{color:var(--muted)}.note{border-left:4px solid var(--accent);padding:13px 18px;background:#edf5f3}.caution{border-left-color:#b56a2f;background:#fff6eb}.table-wrap{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:.86rem}th,td{text-align:left;padding:10px;border-bottom:1px solid var(--line);vertical-align:top}th{background:#edf2f3;white-space:nowrap}code{font-size:.85em;overflow-wrap:anywhere}pre{padding:18px;background:#eef2f3;overflow:auto;font-size:.86rem}.filters{display:flex;flex-wrap:wrap;gap:14px;margin:18px 0}label{display:grid;gap:5px;font-size:.9rem}input,select{font:inherit;padding:8px;border:1px solid #97adb4;border-radius:4px;background:white;color:var(--ink);max-width:100%}details{margin:12px 0}summary{cursor:pointer;font-weight:650}nav{display:flex;flex-wrap:wrap;gap:18px}p{max-width:96ch}@media(max-width:760px){main{padding:24px 12px}section{padding:18px}.cards{grid-template-columns:1fr}}@media print{body{background:white}section{border:0;border-top:1px solid var(--line)}.filters,nav{display:none}}</style></head><body><main>
<header><div class="eyebrow">Independent reference data · Frozen selection · Reproducible checks</div><h1>A broader test bed for orbital accuracy</h1>
<p>A versioned corpus for testing future <strong>find-orb-wasm</strong> changes across orbital classes, viewing geometries, arc lengths, and withheld predictions. NASA/JPL SBDB supplies the object catalog; Horizons supplies independent nominal trajectories.</p>
<nav><a href="#coverage">Coverage</a><a href="#gates">Regression gates</a><a href="#explore">Explore objects</a><a href="#reproduce">Run the checks</a></nav>
<div class="cards"><div class="card"><span class="metric">${corpus.counts.usableObjects}</span>Usable objects across ${protocol.catalog.strata.length} declared categories.</div><div class="card"><span class="metric">${cases.length}</span>Object/date cases: ${corpus.counts.coreCases} core and ${corpus.counts.temporalSupplementCases} temporal supplements.</div><div class="card"><span class="metric">${arcInstances.toLocaleString('en-US')}</span>Case/arc combinations before paired engines and noise realizations.</div></div>
<p class="note">This corpus supports regression testing. It does not establish that a one-hour optical arc uniquely identifies orbital elements, or that the current solver is accurate on every case.</p></header>
<section id="coverage"><h2>Coverage is declared before solver outcomes</h2><p>Two fixed UTC anchors (${protocol.anchorsUtc.map(x=>esc(x.slice(0,10))).join(' and ')}) provide different viewing geometries. The schedules contain one-hour tracklets on days 0, 1, 2, 7, 14, 21, and 30. Each arc has independent prediction targets at +1, +3, and +7 days after its last fitted exposure. A position used to test a short arc may become an input to a longer arc; no arc is scored on its own fitted observations.</p>
${table(['Arc','Tracklets','Observations'],protocol.arcs.map(a=>[a.id,a.trackletDays.join(', '),a.trackletDays.length*protocol.exposureMinutes.length]))}
<p>All epochs and realizations of an object share a split: ${objects.filter(o=>o.split==='development').length} development and ${objects.filter(o=>o.split!=='development').length} regression-holdout objects. The eight previously studied objects remain development/known-regression. A regression holdout becomes a reusable reference after inspection; future method selection needs fresh untouched objects. Cases and noise seeds from the same object are correlated.</p>
${table(['Declared category','Objects','Development','Regression holdout','Usable cases','Model-limited cases'],stratumRows)}
<p>The selection favors established catalog objects and named sentinels. It is not a random population sample. The Hilda-region category is selected by semimajor-axis band and does not certify resonance. Apophis near its 2029 encounter and Encke near its catalog perihelion add temporal stress cases; these do not increase the independent object count.</p>
<p class="note caution">The broad core uses geocentric observer <strong>MPC 500</strong>, including daylight and inaccessible ground-based geometries. It tests mechanics and software behavior. The <a href="short-arc-research.html">earlier F52 study</a> supplies seven visible station-specific cases. Horizons trajectories are numerical reference solutions, not exact physical truth or observed astrometry.</p>
${corpus.unavailable.length?'<details><summary>Unavailable acquisitions retained without substitution</summary>'+table(['Object','Category','Reason'],corpus.unavailable.map(u=>[u.name,u.stratum,u.reason]))+'</details>':''}</section>
<section id="gates"><h2>Separate numerical parity from scientific improvement</h2>
${table(['Layer','What is checked','Interpretation'],[
['Offline evidence','Frozen object identities, query/response and file hashes, frames, time scales, state/element identities, future-only forecast grids.','Detects corruption, changed fixtures, parsing mistakes and target/time mismatches.'],
['Forward controls','Supply independent Cartesian states to baseline and candidate; compare their predictions with each other and Horizons.','Separates propagation from inverse orbit recovery. Strict cases have a declared broad 0.1″ reference guard; model-limited cases retain numerical checks and report reference errors separately.'],
['Unchanged solver','Fit identical MPC80 observations with the native count comparator and WASM candidate. Enforce declared parity and structural gates.','Detects port/compiler/runtime regressions within covered cases. Upstream clock-dependent refinement can cause genuine differences that remain visible.'],
['Changed algorithm','Use explicit report mode for fit differences. Retain structural and forward gates; report paired sky and orbital-energy errors and worsening cases.','A lower residual, pooled median improvement, or native/WASM agreement alone does not establish better orbital accuracy.']])}
<p>${count(c=>c.applicability.forwardTruth==='strict')} cases have strict forward-reference applicability; ${count(c=>c.applicability.forwardTruth==='model-limited')} are model-limited. Explicit nongravitational forces, comets, special trajectory sources, and unknown force metadata require distinct treatment. Null catalog coefficients do not prove zero force. Every case retains its applicability reason and reference headers.</p>
<p>The full plan combines all five arcs with exact astrometry and a paired Gaussian 0.2″ realization. Exact input still has finite reference precision and MPC80 quantization. Gaussian noise is deterministic per case, bank position and seed, preserving common measurements across nested arcs. Biased/outlier cases remain in the earlier study; the broad suite does not yet claim timing-error or correlated-error coverage.</p>
<p><strong>Match the forecast coordinate convention.</strong> Find_Orb ordinarily includes differential solar light deflection relative to background stars; Horizons quantity 1 omits it. The initial default-output comparison reached 0.0919″ for Chicago as it approached within 1.02° of the Sun, while native and WASM agreed. The current harness sets <code>DISABLE_LIGHT_BENDING=1</code> for emitted ephemerides. Original results and exact source snapshots remain available as a separate convention control. This switch leaves the internal fitting model unchanged: raw Horizons angles are still an approximation to CCD-relative fitting inputs, and that remaining mismatch belongs in interpreting fit errors. <a href="https://github.com/Bill-Gray/find_orb/blob/9cc932997837c5ab994fbf015db59f5d0da852e5/orb_func.cpp#L702">Upstream explanation</a>.</p>
${checks?'<h3>Recorded baseline checks</h3>'+table(['Run','Compared pairs','Passed / failed','Maximum native/WASM sky difference ″'],['forward-v2','sentinel-v2'].map(name=>{const r=checks.runs[name];return [name,r.pairs,r.passedPairs+' / '+r.failedPairs,r.maxEngineDirectionDifferenceArcsec.toExponential(3)];}))+
table(['Independent forward reference','Cases','Maximum error ″','Absolute guard'],Object.entries(checks.runs['forward-v2'].independentForwardReference).map(([name,r])=>[name,r.cases,r.maxArcsec.toPrecision(4),r.absoluteGuardEnforced?'0.1″, predeclared':'Reported separately']))+
'<p>All '+checks.tests.pass+' corpus/harness tests pass. Offline replay verifies the archived commands and scientific summaries. The 194 broad propagation pairs and the 19 sentinel propagation / 19 fit pairs cover 464 fresh solver calls. The complete 5,820-call noisy fitting matrix has not been run. <a href="../results/regression-corpus/checks.json">Commands, outcomes, and evidence links</a>.</p>'+
'<p class="note caution"><strong>Passing parity is not accurate orbit recovery.</strong> The sentinel still contains large short-arc errors: the largest seven-day fit error is '+(checks.runs['sentinel-v2'].fitReferenceDiagnostic.sevenDayErrorArcsec/3600).toFixed(2)+'° in the geocentric Bennu case. Those truth errors are retained as diagnostics, including physical and input-convention limitations. They must remain visible when evaluating future solver changes.</p>':'<p>Solver validation results have not yet been attached to this generated report.</p>'}</section>
<section id="explore"><h2>Inspect the geometries and assumptions</h2><div class="filters"><label>Object or category<input id="query" type="search" placeholder="e.g. Apophis, trojan, comet"></label><label>Reference applicability<select id="applicability"><option value="">All</option><option>strict</option><option>model-limited</option></select></label><label>Split<select id="split"><option value="">All</option><option>development</option><option>regression-holdout</option></select></label></div><p id="row-count" aria-live="polite"></p><div id="case-table"></div><noscript>The category tables above remain readable without JavaScript. Full individual data is in the linked corpus JSON.</noscript></section>
<section id="reproduce"><h2>Run and extend the corpus</h2><pre># No Horizons/API access or compiled engines:
npm run regression:validate
npm run test:regression

# Print the sentinel or full plan without executing engines:
npm run regression:sentinel -- --dry-run
npm run regression:full

# Use the pinned native comparator and released compact WASM:
npm run regression:sentinel -- --output results/local/regression-sentinel

# Run broad known-state propagation controls without the orbit fits:
npm run regression:full -- --checks forward --arcs one-hour --execute \\
  --output results/local/regression-forward

# An intentionally changed solver must state that fit deltas are informational:
npm run regression:sentinel -- --candidate-dir dist-candidate --fit-gate report \\
  --output results/local/regression-candidate

# Full runs require an explicit execution flag and can be expensive:
npm run regression:full -- --execute --output results/local/regression-full
npm run regression:replay -- --directory results/local/regression-sentinel
node scripts/regression-evidence.mjs
npm run report:regression</pre>
<p>To replay the committed convention-matched baselines, use <code>results/regression-corpus/forward-v2</code> or <code>sentinel-v2</code>. The older v1 comparisons use their historical checker: <code>node results/regression-corpus/default-output-sources/experiments/regression-suite/replay.mjs --directory results/regression-corpus/forward-v1 --corpus experiments/regression-corpus/corpus.json</code>. Substitute <code>sentinel-v1</code> for its fitting run. The evidence-summary generator reads the four committed runs and verifies that the 388 paired propagation commands differ only by the emitted-coordinate switch.</p>
<p>The lightweight GitHub workflow replays frozen source data and tests the harness using Node 24. It does not compile or run the solver. Actual native/WASM comparisons require the pinned engine builds described in <a href="../README.md">README</a>. Each run uses a new output directory and saves commands, raw outputs, failures, engine hashes, protocol hashes, and the exact plan. Timings are diagnostic; use the separate benchmark suite for performance claims.</p>
<p>${raw.length} compressed raw references (${(raw.reduce((n,r)=>n+r.bytes,0)/1e6).toFixed(2)} MB) accompany the corpus. Refreshing upstream solutions changes the reference and requires a new corpus version. The saved responses permit offline replay even if an upstream orbit solution later changes.</p>
<p><a href="../experiments/regression-corpus/corpus.json">Normalized corpus</a> · <a href="../experiments/regression-corpus/selection.json">Frozen identities and splits</a> · <a href="../experiments/regression-corpus/protocol.json">Acquisition protocol</a> · <a href="../experiments/regression-suite/protocol.json">Regression thresholds and policy</a></p>
<details><summary>Reference conventions and source links</summary><p>${esc(corpus.provenance.observationCoordinates)}</p><p>${esc(corpus.provenance.stateCoordinates)}</p><p><a href="https://ssd-api.jpl.nasa.gov/doc/sbdb_query.html">JPL SBDB Query API</a> · <a href="https://ssd-api.jpl.nasa.gov/doc/horizons.html">Horizons API</a> · <a href="https://ssd.jpl.nasa.gov/horizons/manual.html">Horizons manual</a></p><p>Corpus SHA-256: <code>${sha}</code></p></details>
<p>Original solver: <a href="https://github.com/Bill-Gray/find_orb">Bill Gray / Project Pluto Find_Orb</a>. New code carries GPL-2.0-or-later notices; the existing <a href="../NOTICE">license notices</a> remain applicable. NASA/JPL source responses retain their provenance and are independent reference data.</p></section>
<footer>Read this corpus together with the <a href="short-arc-research.html">short-arc study</a>. It broadens coverage; it is not a full solver/compiler proof.</footer></main>
<script type="application/json" id="data">${dynamic}</script><script>
const rows=JSON.parse(document.getElementById('data').textContent),ids=['query','applicability','split'];
const safe=s=>String(s??'—').replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;');
const num=(v,d=3)=>Number.isFinite(v)?v.toLocaleString('en-US',{maximumFractionDigits:d}):'—';
function render(){const [q,a,s]=ids.map(id=>document.getElementById(id).value.toLowerCase());
const shown=rows.filter(r=>(!q||(r.name+' '+r.designation+' '+r.stratum+' '+r.id).toLowerCase().includes(q))&&(!a||r.applicability===a)&&(!s||r.split===s));
document.getElementById('row-count').textContent=shown.length+' of '+rows.length+' cases';
const headers=['Object / anchor','Category / split','Reference applicability','Initial range AU','Max |range rate| km/s','Min elongation °','e / i° / q AU'];
document.getElementById('case-table').innerHTML='<div class="table-wrap"><table><thead><tr>'+headers.map(x=>'<th>'+safe(x)+'</th>').join('')+'</tr></thead><tbody>'+shown.map(r=>'<tr>'+[r.name+' ('+r.designation+') / '+r.anchor.slice(0,10),r.stratum+' / '+r.split,r.applicability+' — '+r.reason,num(r.rangeAu),num(r.rangeRateKmPerSecond),num(r.minElongationDeg,1),num(r.e)+' / '+num(r.i,1)+' / '+num(r.q)].map(x=>'<td>'+safe(x)+'</td>').join('')+'</tr>').join('')+'</tbody></table></div>';}
for(const id of ids)document.getElementById(id).addEventListener('input',render);render();
</script></body></html>`;
await writeFile('docs/regression-corpus.html',html);
