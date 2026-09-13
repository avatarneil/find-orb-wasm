#!/usr/bin/env node
// SPDX-License-Identifier: GPL-2.0-or-later
// Local, scaled astrometric-Jacobian diagnostics at independently supplied truth.
// This is not a proof of global identifiability or a posterior approximation.
import {readFile, writeFile, mkdir, readdir} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {gzipSync} from 'node:zlib';
import {loadNative} from '../../benchmark/engines.mjs';
import {stateCommand} from '../../benchmark/cases.mjs';
import {skyRows, separationArcsec} from '../../benchmark/accuracy.mjs';

const root = fileURLToPath(new URL('../../', import.meta.url));
const sigmaArcsec = .2, gaussianK = .01720209895;
const coordinateScales = [1, 1, 1, gaussianK, gaussianK, gaussianK];
const perturbationSteps = [1e-4, 3e-5];
const arcIndices = {'one-hour': [0, 1, 2, 3], 'plus-one-day': [0, 1, 2, 3, 75]};
const sha256 = data => createHash('sha256').update(data).digest('hex');
const rad = Math.PI / 180;
const wrapDegrees = degrees => ((degrees + 180) % 360 + 360) % 360 - 180;

function assertFinite(values, message) {
  if (!values.every(Number.isFinite)) throw new Error(message);
}

function eclipticDirection(point) {
  const ra = point.RA * rad, dec = point.Dec * rad, eps = 84381.448 / 3600 * rad;
  const x = Math.cos(dec) * Math.cos(ra), y = Math.cos(dec) * Math.sin(ra), z = Math.sin(dec);
  return [x, y * Math.cos(eps) + z * Math.sin(eps), z * Math.cos(eps) - y * Math.sin(eps)];
}

export function whitenedJacobian(baseline, differences, indices) {
  return indices.flatMap(index => [0, 1].map(axis => differences.map(({plus, minus, scaledSeparation}) => {
    const difference = axis === 0
      ? wrapDegrees(plus[index].RA - minus[index].RA) * Math.cos(baseline[index].Dec * rad)
      : plus[index].Dec - minus[index].Dec;
    return difference * 3600 / sigmaArcsec / scaledSeparation;
  })));
}

// NumPy's float64 SVD acts directly on J. Forming J^T J would square its
// condition number and can erase the very modes this diagnostic investigates.
const analysisPython = String.raw`
import contextlib, io, json, platform, sys
import numpy as np

data=json.load(sys.stdin)
config=io.StringIO()
with contextlib.redirect_stdout(config):
    np.show_config()

def decompose(matrix, los):
    j=np.asarray(matrix,dtype=np.float64)
    u,s,vh=np.linalg.svd(j,full_matrices=False)
    r=np.r_[los,[0.,0.,0.]]
    v=np.r_[[0.,0.,0.],los]
    modes=[]
    for k in [-2,-1]:
        mode=vh[k]
        pn=float(np.linalg.norm(mode[:3])); vn=float(np.linalg.norm(mode[3:]))
        modes.append(dict(singularValue=float(s[k]),scaledStateDirection=mode.tolist(),
            positionNorm=pn,velocityNorm=vn,
            positionAlignmentWithAstrometricLos=float(abs(mode[:3]@los)/pn) if pn else None,
            velocityAlignmentWithAstrometricLos=float(abs(mode[3:]@los)/vn) if vn else None))
    inv=np.divide(1.,s,out=np.full_like(s,np.inf),where=s>0)
    cr=(vh@r)*inv; cv=(vh@v)*inv
    corr=float(cr@cv/(np.linalg.norm(cr)*np.linalg.norm(cv))) if np.all(np.isfinite(inv)) else None
    result=dict(singularValues=s.tolist(),conditionNumberRaw=float(s[0]/s[-1]) if s[-1]>0 else None,
        weakestModes=modes,
        weakTwoModeSubspace=dict(rangeDirectionSquaredProjection=float(np.sum((vh[-2:]@r)**2)),
            radialVelocityDirectionSquaredProjection=float(np.sum((vh[-2:]@v)**2))),
        localLinearizedRangeRangeRateCorrelationRaw=corr,
        svdRelativeReconstructionError=float(np.linalg.norm(j-(u*s)@vh)/np.linalg.norm(j)),
        rightVectorOrthogonalityError=float(np.linalg.norm(vh@vh.T-np.eye(6))))
    return result,s,vh

for case in data['cases']:
    los=np.asarray(case['astrometricLineOfSightEcliptic'],dtype=np.float64)
    for name,arc in case['arcs'].items():
        coarse=np.asarray(arc['jacobians'][0],dtype=np.float64)
        fine=np.asarray(arc['jacobians'][1],dtype=np.float64)
        c,cs,cv=decompose(coarse,los); f,fs,fv=decompose(fine,los)
        difference=float(np.linalg.norm(fine-coarse,ord=2))
        relative=np.abs(fs-cs)/np.maximum(fs,np.finfo(float).tiny)
        alignment=np.abs(np.sum(fv*cv,axis=1))
        # An observed step difference is an empirical sensitivity indicator,
        # NOT a proven discretization-error bound. The separate rounding bound
        # is conservative only for the documented decimal output quantization.
        rounding=arc['fineOutputRoundingFrobeniusBound']
        thresholds=np.maximum(difference,rounding)*10.
        stable=(relative<=.1)&(fs>thresholds)
        arc['decompositions']=[c,f]
        arc['stepSensitivity']=dict(relativeSingularValueChanges=relative.tolist(),
            absoluteCorrespondingRightVectorInnerProducts=alignment.tolist(),
            derivativeDifferenceSpectralNorm=difference,
            derivativeDifferenceRelativeSpectralNorm=difference/float(fs[0]),
            tenTimesEmpiricalOrRoundingFloor=thresholds,
            singularModesResolvedUnderTestedSteps=stable.tolist(),
            weakSubspacePrincipalCosines=np.linalg.svd(fv[-2:]@cv[-2:].T,compute_uv=False).tolist(),
            conditionNumberResolved=bool(np.all(stable)),
            conditionNumber=float(fs[0]/fs[-1]) if np.all(stable) else None,
            minimumResolvedSingularValue=float(np.min(fs[stable])) if np.any(stable) else None,
            label='Empirical two-step numerical resolution test; not a certified derivative-error bound.')
    short=case['arcs']['one-hour']; extended=case['arcs']['plus-one-day']
    a=np.asarray(short['decompositions'][1]['singularValues'])
    b=np.asarray(extended['decompositions'][1]['singularValues'])
    case['nextNightComparison']=dict(singularValueRatios=(b/a).tolist(),
        weakestSingularValueRatioRaw=float(b[-1]/a[-1]),
        weakestRatioNumericallyResolved=bool(short['stepSensitivity']['conditionNumberResolved'] and extended['stepSensitivity']['conditionNumberResolved']),
        interpretation='Same four measurements plus one independent 0.2 arcsec next-night position; local model information only.')

data['linearAlgebra']=dict(python=sys.version,numpy=np.__version__,platform=platform.platform(),
    dtype='float64',method='numpy.linalg.svd on whitened Jacobian directly; no normal-equation eigendecomposition',
    numpyConfiguration=config.getvalue())
json.dump(data,sys.stdout,allow_nan=False,indent=2)
`;

export async function runIdentifiability({
  corpus = join(root, 'experiments/short-arcs/fixtures/observable-corpus.json'),
  native = join(root, '.native-engine'),
  output = join(root, 'results/local/short-arcs/identifiability-v1'),
  python = 'python3',
} = {}) {
  const probe = spawnSync(python, ['-c', 'import numpy; print(numpy.__version__)'], {encoding: 'utf8', timeout: 30000});
  if (probe.status !== 0) throw new Error('Existing NumPy installation required; none installed automatically: ' + (probe.error?.message || probe.stderr));
  await mkdir(output, {recursive: true});
  if ((await readdir(output)).length) throw new Error('Preserve the previous diagnostic evidence; output directory must be empty: ' + output);
  const corpusText = await readFile(corpus, 'utf8'), fixtures = JSON.parse(corpusText);
  const engine = await loadNative(native, 'fo-count');
  const evidence = {
    schemaVersion: 1, startedAt: new Date().toISOString(),
    title: 'Local scaled astrometric identifiability at independent nominal truth',
    corpusSHA256: sha256(corpusText), corpus, engine: engine.manifest,
    sourceSHA256: sha256(await readFile(fileURLToPath(import.meta.url))),
    commandBuilderSHA256: sha256(await readFile(new URL('../../benchmark/cases.mjs', import.meta.url))),
    protocol: {
      truth: 'Horizons heliocentric J2000 ecliptic state at corpus epochJdTdb, representing the same instant as epochJdTt; Find_Orb takes that TT epoch.',
      velocityTimeUnit: 'AU per TDB day from Horizons treated as AU per TT day; their periodic fractional rate distinction is not modeled.',
      measuredCoordinates: 'RA*cos(baseline Dec) and Dec in a local equatorial astrometric tangent chart; reception epochs UTC, topocentric F52.',
      stateCoordinates: ['x', 'y', 'z', 'vx', 'vy', 'vz'],
      coordinateScales, coordinateScaleUnits: ['AU', 'AU', 'AU', 'AU/day', 'AU/day', 'AU/day'],
      whiteningSigmaArcsec: sigmaArcsec,
      noiseAssumption: 'Independent, isotropic 0.2 arcsec per angular coordinate. No catalog or visit correlation in this local diagnostic.',
      perturbationSteps, differencing: 'Central differences divided by actual represented plus-minus state separation in scaled coordinates.',
      observations: 'Four positions at minutes0,20,40,60; extended arc adds exactly one position24h after the fourth.',
      arcIndices, commandGrid: {count: 76, step: '20m', timeScale: 'UTC'},
      outputDecimalDegrees: 11,
      outputQuantization: 'Upstream ephem0.cpp emits RA/Dec with %15.11f. Per-value rounding is at most0.5e−11degree; bounds exclude propagation/compiler errors.',
      modeResolutionRule: 'Relative singular-value change <=10%, and singular value >10 times max(observed derivative-difference spectral norm, fine-grid decimal-rounding Frobenius bound).',
      lineOfSightInterpretation: 'Approximate range/radial-velocity direction from final astrometric RA/Dec rotated by IAU76 obliquity; it is a retarded astrometric direction, not an exact geometric attributable derivative.',
      limitations: [
        'The Jacobian describes a local linearization at supplied nominal truth. It neither establishes global uniqueness nor describes a multimodal posterior.',
        'Condition numbers depend on the explicit state scaling, epoch, frame, observing cadence, and whitening model.',
        'Two finite-difference scales and decimal rounding bounds can reveal numerical trouble but do not certify the full derivative error.',
        'Unresolved smallest modes retain raw SVD values for inspection, but no resolved condition number is asserted.',
        'Horizons/Find_Orb force-model and Earth-orientation differences bound independent-truth comparisons.',
        'A next-night position is hypothetical here; visibility metadata is retained and must be checked for actual observing plans.',
      ],
    }, cases: [],
  };
  await writeFile(join(output, 'manifest.json'), JSON.stringify(evidence, null, 2) + '\n');
  for (const c of fixtures.cases) {
    const state = [...c.state.positionAu, ...c.state.velocityAuPerDay];
    assertFinite([...state, c.epochJdTt, c.startJdUtc], 'Invalid truth state/epoch.');
    if (c.observer !== 'F52') throw new Error('stateCommand currently fixes the observer to F52.');
    const record = {
      id: c.id, split: c.split, object: c.object, stateEpochJdTt: c.epochJdTt,
      stateEpochJdTdb: c.epochJdTdb, truthState: state,
      startJdUtc: c.startJdUtc,
      followup: {jdUtc: c.holdout[1].jdUtc, altitudeDeg: c.holdout[1].altitudeDeg, solarPresence: c.holdout[1].solarPresence},
      astrometricLineOfSightEcliptic: eclipticDirection(c.observations[6]),
      rawRuns: [], arcs: {},
    };
    async function execute(trial, tag) {
      const command = stateCommand(trial, {epoch: c.epochJdTt, start: c.startJdUtc, count: 76, step: '20m', scale: 'UTC', sky: true});
      command.stepDays = 1 / 72; // stateCommand's generic metadata parser handles h/d, not m.
      const result = await engine.execute(command), sky = skyRows(result);
      if (sky.length !== 76) throw new Error('Wrong identifiability sky-grid length.');
      for (let i = 0; i < sky.length; i++) {
        assertFinite([sky[i].JD, sky[i].RA, sky[i].Dec], 'Nonfinite sky coordinate.');
        if (Math.abs(sky[i].JD - (c.startJdUtc + i / 72)) > 1e-8) throw new Error('Wrong UTC reception grid.');
      }
      if (Math.abs(sky[75].JD - c.holdout[1].jdUtc) > 1e-8) throw new Error('Next-night fixture does not match the grid.');
      const force = /^# Perturbers:\s+([0-9a-f]+).*JPL DE-440.*$/im.exec(result.files['/job/elements.txt']);
      if (!force || (parseInt(force[1], 16) & 0x7fe) !== 0x7fe) throw new Error('Missing full planetary force model.');
      const bytes = Buffer.from(JSON.stringify({command, result})), compressed = gzipSync(bytes);
      const filename = `${c.id}-${tag}.json.gz`;
      await writeFile(join(output, filename), compressed);
      record.rawRuns.push({tag, filename, commandSHA256: sha256(JSON.stringify(command)),
        resultSHA256: sha256(JSON.stringify(result)), rawSHA256: sha256(bytes), gzipSHA256: sha256(compressed),
        fileSHA256: Object.fromEntries(Object.entries(result.files).map(([name, text]) => [name, sha256(text)])),
        phases: result.phases});
      return sky;
    }
    const baseline = await execute(state, 'truth');
    record.truthSkyDifferencesArcsec = [0, 1, 2, 3].map((i) => separationArcsec(baseline[i], c.observations[i * 2]));
    record.truthNextNightDifferenceArcsec = separationArcsec(baseline[75], c.holdout[1]);
    const differencesByStep = [];
    for (const h of perturbationSteps) {
      const differences = [];
      for (let j = 0; j < 6; j++) {
        const plus = state.slice(), minus = state.slice();
        plus[j] += coordinateScales[j] * h; minus[j] -= coordinateScales[j] * h;
        const scaledSeparation = (plus[j] - minus[j]) / coordinateScales[j];
        if (!(scaledSeparation > 0)) throw new Error('Perturbation is not representable.');
        differences.push({
          plus: await execute(plus, `h${h}-axis${j}-plus`),
          minus: await execute(minus, `h${h}-axis${j}-minus`), scaledSeparation,
        });
      }
      differencesByStep.push(differences);
    }
    for (const [name, indices] of Object.entries(arcIndices)) {
      const fine = differencesByStep[1];
      // Bound the Frobenius norm of decimal-rounding error in J. Each central
      // difference combines two rounded coordinates, each with half-unit error.
      const roundingSquares = indices.flatMap(i => [0, 1].flatMap(axis => fine.map(({scaledSeparation}) => {
        const tangentScale = axis === 0 ? Math.abs(Math.cos(baseline[i].Dec * rad)) : 1;
        return (1e-11 * 3600 * tangentScale / sigmaArcsec / scaledSeparation) ** 2;
      })));
      record.arcs[name] = {observationJdUtc: indices.map(i => baseline[i].JD),
        jacobians: differencesByStep.map(differences => whitenedJacobian(baseline, differences, indices)),
        representedScaledSeparations: differencesByStep.map(differences => differences.map(d => d.scaledSeparation)),
        fineOutputRoundingFrobeniusBound: Math.sqrt(roundingSquares.reduce((sum, x) => sum + x, 0)),
      };
    }
    evidence.cases.push(record);
    await writeFile(join(output, 'jacobians.json'), JSON.stringify(evidence, null, 2) + '\n');
    console.log(JSON.stringify({id: c.id, nativeRuns: record.rawRuns.length,
      truthSkyDifferenceMaxArcsec: Math.max(...record.truthSkyDifferencesArcsec), truthNextNightDifferenceArcsec: record.truthNextNightDifferenceArcsec}));
  }
  const analysis = spawnSync(python, ['-c', analysisPython], {
    input: JSON.stringify(evidence), encoding: 'utf8', timeout: 30000, maxBuffer: 16 * 1024 * 1024,
  });
  if (analysis.status !== 0) throw new Error('Jacobian SVD analysis failed: ' + (analysis.error?.message || analysis.stderr));
  const result = JSON.parse(analysis.stdout);
  result.completedAt = new Date().toISOString();
  await writeFile(join(output, 'results.json'), JSON.stringify(result, null, 2) + '\n');
  for (const c of result.cases) console.log(JSON.stringify({id: c.id,
    oneHour: c.arcs['one-hour'].stepSensitivity,
    plusOneDay: c.arcs['plus-one-day'].stepSensitivity,
    nextNightComparison: c.nextNightComparison}));
  return result;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const options = {};
  for (let i = 2; i < process.argv.length; i += 2) {
    const key = process.argv[i].slice(2), value = process.argv[i + 1];
    if (!['corpus', 'native', 'output', 'python'].includes(key) || !value) throw new Error('Options: --corpus --native --output --python.');
    options[key] = key === 'python' ? value : resolve(value);
  }
  await runIdentifiability(options);
}
