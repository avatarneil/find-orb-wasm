#!/usr/bin/env python3
"""GPL-2.0-or-later. Reproduce the complete scoped correctness research suite."""
from __future__ import annotations

import hashlib
import importlib.metadata
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'verification/research-evidence.json'
GENERATED = {'NumericalCertificates.lean', 'RoundedDAG.lean', 'IntegratorCertificates.lean',
             'integrator-certificate-manifest.json', 'RKFLinear.lean', 'PDLinear.lean'}


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def inputs() -> dict[str, str]:
    files = [p for p in (ROOT / 'verification').rglob('*')
             if p.is_file() and 'evidence' not in p.parts and '__pycache__' not in p.parts
             and p.suffix in {'.py', '.lean', '.json', '.txt', '.mjs', '.js', '.c', '.cpp', '.h'}
             and p.name not in GENERATED and p != REPORT]
    files += [ROOT / name for name in ['build/patches.mjs', 'build/build.mjs', 'build/pins.mjs',
              'dist/fo.wasm', 'dist/fo.js', 'dist/find-orb-worker.js', 'dist/find-orb.data',
              'dist/manifest.json', 'dist/source-lock.json']]
    lock = json.loads((ROOT / 'dist/source-lock.json').read_text())
    for project, entries in lock['files'].items():
        for relative, expected in entries.items():
            path = ROOT / '.wasm-engine/sources' / project / relative
            if sha(path) != expected:
                raise RuntimeError('Source differs from distribution lock: ' + str(path))
            files.append(path)
    files += [ROOT / '.wasm-toolchain/upstream' / relative for relative in
              ['emscripten/emcc.py', 'emscripten/em++.py', 'emscripten/emscripten-version.txt',
               'bin/clang', 'bin/wasm-ld', 'bin/wasm-opt']]
    runtime_root = ROOT / '.wasm-toolchain/upstream/emscripten/system/lib/compiler-rt/lib/builtins'
    files += [runtime_root / name for name in ['extenddftf2.c', 'trunctfdf2.c',
              'fp_extend_impl.inc', 'fp_trunc_impl.inc', 'ashlti3.c', 'lshrti3.c', 'int_lib.h', 'int_types.h']]
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(files)}


def main() -> None:
    report = {'schema': 1, 'scope': 'complete scoped correctness research suite',
              'passed': False, 'status': 'running', 'startedAtUnix': time.time(), 'stages': []}
    REPORT.write_text(json.dumps(report, indent=2) + '\n')
    try:
        if sys.flags.optimize or sys.version_info < (3, 12):
            raise RuntimeError('Use unoptimized Python 3.12+ and the pinned research requirements')
        versions = {name: importlib.metadata.version(name)
                    for name in ['z3-solver', 'cvc5', 'zstandard']}
        if versions != {'z3-solver': '4.15.4.0', 'cvc5': '1.3.4', 'zstandard': '0.25.0'}:
            raise RuntimeError('Unpinned research dependencies: ' + str(versions))
        before = inputs()
        report['python'] = sys.version
        report['dependencies'] = versions
        env = dict(os.environ)
        env.pop('PYTHONOPTIMIZE', None)
        env['PYTHONUNBUFFERED'] = '1'
        logs = ROOT / '.cache/research-logs'
        logs.mkdir(parents=True, exist_ok=True)
        stages = [
            ('integrator-analysis', ['verification/integrator/analyze.py']),
            ('integrator-compiled', ['verification/integrator/compiled.py']),
            ('translation-proof', ['verification/translation/verify.py']),
            ('translation-checker-tests', ['verification/translation/test_checker.py']),
            ('translation-independent-replay', ['verification/translation/replay.py']),
            ('ephemeris-certificates', ['verification/ephemeris/run.py', '--certificates-only']),
            ('ephemeris-runner-tests', ['verification/ephemeris/test_runner.py']),
            ('integrator-kernel-export', ['verification/kernel/generate_integrator.py']),
            ('integrator-connected-export', ['verification/integrator_certified/generate.py']),
            ('production-interpolation', ['verification/production/run.py']),
            ('production-checker-tests', ['verification/production/test_checker.py']),
            ('production-runtime', ['verification/runtime/verify.py']),
            ('runtime-checker-tests', ['verification/runtime/test_machine.py']),
            ('runtime-mutation-witnesses', ['verification/runtime/witnesses.py']),
            ('kernel-compile-and-replay', ['verification/kernel/check.py']),
            ('ephemeris-kernel-mutations', ['verification/ephemeris/kernel_negatives.py']),
            ('rounding-controls', ['verification/rounding/run.py', '--negatives-only', '--modules', '.cache/kernel-modules']),
            ('integrator-connected-mutations', ['verification/integrator_certified/negative.py']),
        ]
        expected_outputs = {
            'integrator-analysis': ['verification/integrator/evidence/analysis.json'],
            'integrator-compiled': ['verification/integrator/evidence/compiled.json'],
            'translation-proof': ['verification/translation/evidence/report.json'],
            'ephemeris-certificates': ['verification/ephemeris/evidence/report.json'],
            'integrator-kernel-export': ['verification/kernel/integrator-certificate-manifest.json'],
            'integrator-connected-export': ['verification/integrator_certified/evidence/certificate.json'],
            'production-interpolation': ['verification/production/evidence/report.json'],
            'production-runtime': ['verification/runtime/evidence/report.json'],
            'runtime-mutation-witnesses': ['verification/runtime/evidence/witnesses.json'],
            'kernel-compile-and-replay': ['verification/kernel/evidence/report.json'],
            'ephemeris-kernel-mutations': ['verification/ephemeris/evidence/kernel-negatives.json'],
            'rounding-controls': ['verification/rounding/evidence/central-controls.json'],
            'integrator-connected-mutations': ['verification/integrator_certified/evidence/negative.json'],
        }
        for name, arguments in stages:
            print('Research stage: ' + name, flush=True)
            started = time.monotonic()
            log = logs / (name + '.txt')
            for relative in expected_outputs.get(name, []):
                (ROOT / relative).unlink(missing_ok=True)
            with log.open('w') as stream:
                result = subprocess.run([sys.executable, *arguments], cwd=ROOT, env=env,
                                        stdout=stream, stderr=subprocess.STDOUT, timeout=2400)
            item = {'name': name, 'command': ['python', *arguments],
                    'exitCode': result.returncode, 'elapsedSeconds': time.monotonic() - started,
                    'logSHA256': sha(log)}
            report['stages'].append(item)
            if result.returncode:
                raise RuntimeError(name + ' failed:\n' + log.read_text()[-4000:])
            for relative in expected_outputs.get(name, []):
                artifact = json.loads((ROOT / relative).read_text())
                if not isinstance(artifact, dict) or not artifact or artifact.get('passed') is False:
                    raise RuntimeError(name + ' did not produce valid fresh evidence: ' + relative)
            REPORT.write_text(json.dumps(report, indent=2) + '\n')
        if inputs() != before:
            raise RuntimeError('Verification inputs changed during the run; rerun on stable sources')
        kernel = json.loads((ROOT / 'verification/kernel/evidence/report.json').read_text())
        if not kernel.get('passed') or kernel.get('scope') != 'complete research kernel suite':
            raise RuntimeError('Full kernel suite did not pass')
        report['inputSHA256'] = before
        artifacts = [ROOT / p for p in [
            'verification/integrator/evidence/analysis.json',
            'verification/integrator/evidence/compiled.json',
            'verification/translation/evidence/report.json',
            'verification/ephemeris/evidence/report.json',
            'verification/kernel/evidence/report.json',
            'verification/kernel/integrator-certificate-manifest.json',
            'verification/ephemeris/evidence/kernel-negatives.json',
            'verification/production/evidence/report.json',
            'verification/runtime/evidence/report.json',
            'verification/runtime/evidence/witnesses.json',
            'verification/rounding/evidence/central-controls.json',
            'verification/integrator_certified/evidence/certificate.json',
            'verification/integrator_certified/evidence/negative.json',
        ]]
        artifacts += [p for p in (ROOT / 'verification').rglob('*.lean')]
        artifacts += [p for directory in ['production', 'runtime']
                      for p in (ROOT / 'verification' / directory / 'evidence').rglob('*')
                      if p.is_file() and p.suffix in {'.smt2', '.bin', '.wasm', '.json'}]
        report['artifactSHA256'] = {str(p.relative_to(ROOT)): sha(p) for p in sorted(artifacts)}
        report['kernelTheoremCount'] = kernel['theoremCount']
        report['status'], report['passed'] = 'complete', True
    except BaseException as error:
        report['status'], report['error'] = 'failed', str(error)
        raise
    finally:
        report['completedAtUnix'] = time.time()
        REPORT.write_text(json.dumps(report, indent=2) + '\n')
    print('Complete research suite passed; see verification/research-evidence.json', flush=True)


if __name__ == '__main__':
    main()
