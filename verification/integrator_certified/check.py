#!/usr/bin/env python3
"""GPL-2.0-or-later. Compile and replay the connected linear-ODE theorems."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def tools():
    spec = importlib.util.spec_from_file_location('kernel_bootstrap', ROOT / 'verification/kernel/bootstrap.py')
    bootstrap = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bootstrap)
    lean_root, mathlib, _ = bootstrap.paths()
    bootstrap.check_pins(lean_root, mathlib)
    env = bootstrap.proof_environment(lean_root)
    search = subprocess.check_output([str(lean_root / 'bin/lake'), '-d', str(mathlib),
                                     'env', 'printenv', 'LEAN_PATH'], env=env, text=True).strip()
    modules = ROOT / '.cache/integrator-certified-modules'
    modules.mkdir(parents=True, exist_ok=True)
    env['LEAN_PATH'] = os.pathsep.join([str(modules), str(ROOT / '.cache/rounding-modules'),
                                       str(ROOT / '.cache/kernel-modules'), search])
    return str(lean_root / 'bin/lean'), env, modules


def execute(command, env, logfile):
    process = subprocess.run(command, cwd=ROOT, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1200)
    logfile.write_text(process.stdout)
    if process.returncode or re.search(r'PANIC|sorryAx|\berror(?:\(|:)', process.stdout, re.I):
        raise RuntimeError('Lean check failed: ' + str(logfile) + '\n' + process.stdout[-4000:])
    return process.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--support-only', action='store_true')
    parser.add_argument('--no-replay', action='store_true')
    args = parser.parse_args()
    reportfile = HERE / 'evidence' / ('development.json' if args.support_only or args.no_replay else 'report.json')
    report = {'passed': False, 'status': 'running', 'startedAtUnix': time.time(), 'files': [],
              'scope': 'Development compilation only' if args.no_replay else 'Connected linear-ODE proof compile and empty-kernel replay'}
    reportfile.write_text(json.dumps(report) + '\n')
    try:
        if sys.flags.optimize:
            raise RuntimeError('Unoptimized Python is required')
        def snapshot():
            paths = list(HERE.glob('*.py')) + list(HERE.glob('*.lean')) + [HERE / 'evidence/certificate.json']
            paths += list((ROOT / 'verification/rounding').glob('*.lean'))
            return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)}
        before = snapshot()
        lean, env, modules = tools()
        logs = ROOT / '.cache/integrator-certified-logs'
        logs.mkdir(parents=True, exist_ok=True)
        files = ['LinearSupport'] if args.support_only else ['LinearSupport', 'RKFLinear', 'PDLinear', 'CanonicalLinear']
        for name in files:
            source = HERE / (name + '.lean')
            print('Checking ' + name, flush=True)
            output = execute([lean, '--trust=0', '--root', str(HERE), '-o',
                              str(modules / (name + '.olean')), str(source)], env, logs / (name + '.compile.txt'))
            expected = re.findall(r'^#print axioms\s+(\S+)', source.read_text(), re.M)
            audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output)
            if len(audits) != len(expected) or {name.rsplit('.', 1)[-1] for name, _ in audits} != set(expected):
                raise RuntimeError('Missing axiom audits: ' + name)
            if any(set(a.strip() for a in values.split(',') if a.strip()) - {'propext', 'Classical.choice', 'Quot.sound'} for _, values in audits):
                raise RuntimeError('Unapproved axiom')
            item = {'module': name, 'theoremCount': len(audits)}
            if not args.no_replay:
                output = execute([lean, '--run', str(ROOT / 'verification/kernel/Replay.lean'),
                                  name, *[key for key, _ in audits]], env, logs / (name + '.replay.txt'))
                replay = json.loads(output)
                if not replay.get('passed') or not replay.get('emptyInitialEnvironment') or not replay.get('canonicalSignaturesValidated'):
                    raise RuntimeError('Kernel replay failed')
                if set(replay.get('theorems', [])) != {name for name, _ in audits}:
                    raise RuntimeError('Missing replay roots')
                item['replay'] = replay
            report['files'].append(item)
        if snapshot() != before:
            raise RuntimeError('Proof inputs changed during checking')
        report['inputSHA256'] = before
        report['passed'] = True
        report['status'] = 'complete'
    except BaseException as error:
        report['error'] = str(error)
        report['status'] = 'failed'
        raise
    finally:
        report['completedAtUnix'] = time.time()
        reportfile.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
