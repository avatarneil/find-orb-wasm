#!/usr/bin/env python3
"""GPL-2.0-or-later. Compile/audit finite-rounding proofs and reject mutations."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import importlib.util

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'verification/ephemeris'))
from kernel_tools import proof_tools, require_success, require_rejection
from conformance import run as conformance

FILES = ['FiniteFormat', 'SpacingBound', 'IEEEBounds', 'Binary64Bits']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(output, source):
    expected = re.findall(r'^#print axioms (\w+)$', source, re.M)
    parsed = []
    for match in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output):
        axioms = {v.strip() for v in (match[2] or '').split(',') if v.strip()}
        if not axioms <= ALLOWED:
            raise RuntimeError('Unexpected axiom in ' + match[1])
        parsed.append({'name': match[1], 'axioms': sorted(axioms)})
    if not expected or [r['name'].split('.')[-1] for r in parsed] != expected:
        raise RuntimeError('Missing or unexpected theorem audits')
    return parsed


def mutations(tools):
    original = {name: (HERE / (name + '.lean')).read_text() for name in FILES}
    # Mutations retain the original claimed theorem, so failure is mathematical.
    cases = [
      ('odd-half-tie', original['FiniteFormat'].replace('⌊x⌋₊ % 2 = 0', '⌊x⌋₊ % 2 = 1', 1), ('error:', 'omega')),
      ('lost-binade-carry', original['SpacingBound'].replace('⟨n+2, by omega⟩', '⟨n+1, by omega⟩', 1), ('error:', 'unsolved goals')),
      ('wrong-exponent-bit-shift', original['Binary64Bits'].replace('v.2.1.val * 2^52', 'v.2.1.val * 2^51', 1), ('error:', 'omega')),
    ]
    prefix = original['IEEEBounds'][:original['IEEEBounds'].index('theorem binary128_error')]
    start = prefix.index('theorem binary64_error')
    for name, before, after in [
      ('halved-relative-error', '(2 : ℝ)^53 * |x|', '(2 : ℝ)^54 * |x|'),
      ('deleted-subnormal-allowance', '+ 1/(2 : ℝ)^1075', '+ 0'),
    ]:
        tail = prefix[start:]
        if before not in tail:
            raise RuntimeError('Missing mathematical mutation target')
        changed = prefix[:start] + tail.replace(before, after, 1) + '\nend\nend FindOrbRounding\n'
        cases.append((name, changed, ('error:', 'Type mismatch')))
    results = []
    with tempfile.TemporaryDirectory(prefix='rounding-negative-', dir=ROOT / '.cache') as folder:
        for name, contents, expected in cases:
            if contents in original.values():
                raise RuntimeError('Mutation did not change source: ' + name)
            path = Path(folder) / (name.replace('-', '_') + '.lean')
            path.write_text(contents)
            process = subprocess.run([tools['lean'], '--trust=0', '-DmaxRecDepth=8192',
              '-DmaxHeartbeats=1600000', str(path)], cwd=ROOT, env=tools['env'],
              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
            (HERE / 'evidence' / ('negative-' + name + '.log')).write_text(process.stdout)
            require_rejection(process.returncode, process.stdout, expected)
            results.append({'name': name, 'rejected': True, 'exitCode': process.returncode,
              'mutationSHA256': digest(path), 'expectedMessages': list(expected)})
    for code, output in [(0, 'PANIC: recovered'), (0, 'error: failed'), (0, 'sorryAx')]:
        try:
            require_success(code, output)
        except RuntimeError:
            results.append({'name': 'fail-closed-' + output.split(':')[0], 'rejected': True})
        else:
            raise RuntimeError('Accepted proof-tool failure')
    print('Rejected', len(results), 'rounding proof/control mutations', flush=True)
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-root', type=Path)
    parser.add_argument('--mathlib', type=Path, default=ROOT / '.cache/mathlib')
    parser.add_argument('--modules', type=Path, default=ROOT / '.cache/rounding-modules')
    parser.add_argument('--negatives-only', action='store_true', help='Reuse modules after the central raw-kernel replay')
    args = parser.parse_args()
    evidence = HERE / 'evidence'
    evidence.mkdir(parents=True, exist_ok=True)
    destination = evidence / ('central-controls.json' if args.negatives_only else 'report.json')
    destination.write_text('{"passed":false,"status":"incomplete"}\n')
    if sys.flags.optimize:
        raise RuntimeError('Optimized Python is forbidden for rounding verification')
    if args.lean_root is None:
        spec = importlib.util.spec_from_file_location('_rounding_bootstrap', ROOT / 'verification/kernel/bootstrap.py')
        bootstrap = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bootstrap)
        args.lean_root = bootstrap.paths()[0]
    args.modules = args.modules.resolve()
    args.modules.mkdir(parents=True, exist_ok=True)
    evidence = HERE / 'evidence'
    evidence.mkdir(parents=True, exist_ok=True)
    dependency = ROOT / '.cache/kernel-modules'
    for name in ['Foundations', 'Roundoff', 'BridgeSupport']:
        if not (dependency / (name + '.olean')).exists():
            raise RuntimeError('Run the central kernel checker first; missing ' + name)
    tools = proof_tools(args.lean_root.resolve(), args.mathlib.resolve(), args.modules)
    tools['env']['LEAN_PATH'] = str(dependency) + os.pathsep + tools['env']['LEAN_PATH']
    # Prefer this invocation's modules if an older central build also contains them.
    tools['env']['LEAN_PATH'] = str(args.modules) + os.pathsep + tools['env']['LEAN_PATH']
    sources = {name: digest(HERE / (name + '.lean')) for name in FILES}
    proofs = []
    if not args.negatives_only:
        for name in FILES:
            source = HERE / (name + '.lean')
            text = source.read_text()
            if re.search(r'\b(sorry|admit|axiom|native_decide)\b', text):
                raise RuntimeError('Unchecked proof construct: ' + name)
            command = [tools['lean'], '--trust=0', '--root=' + str(HERE),
              '-o', str(args.modules / (name + '.olean')), str(source)]
            process = subprocess.run(command, cwd=ROOT, env=tools['env'], text=True,
              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            (evidence / (name + '.log')).write_text(process.stdout)
            require_success(process.returncode, process.stdout)
            theorems = audit(process.stdout, text)
            proofs.append({'source': source.name, 'sourceSHA256': digest(source),
              'moduleSHA256': digest(args.modules / (name + '.olean')), 'theorems': theorems})
            print('Checked', name, ':', len(theorems), 'theorems', flush=True)
    else:
        for name in FILES:
            if not (args.modules / (name + '.olean')).exists():
                raise RuntimeError('Missing central checked rounding module: ' + name)
    negative = mutations(tools)
    backend = conformance()
    if sources != {name: digest(HERE / (name + '.lean')) for name in FILES}:
        raise RuntimeError('Mathematical sources changed during verification')
    report = {'schema': 1, 'passed': True, 'toolchain': tools['versions'], 'sourceSHA256': sources,
      'kernel': {'performed': not args.negatives_only, 'trustLevel': 0, 'checks': proofs,
        'theoremCount': sum(len(p['theorems']) for p in proofs),
        'centralRawReplayReport': 'verification/kernel/evidence/report.json'},
      'negativeControls': negative, 'backendConformance': backend,
      'integrationPremiseSHA256': digest(ROOT / 'verification/ephemeris/BridgeSupport.lean'),
      'scope': 'Universal finite nearest-representable rounding error, explicit even-significand tie preference, subnormal spacing and binade carry, binary64 field/word bijection, and concrete binary64/binary128 error predicates. Actual runtime/compiler implementation of IEEE semantics remains an external boundary; finite backend probes are conformance evidence only.',
      'sources': ['https://www.w3.org/TR/wasm-core/#floating-point-operations',
        'https://www.w3.org/TR/wasm-core/#floating-point',
        'https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Algebra/Order/Floor/Ring.lean',
        'https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Data/Finset/Max.lean']}
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print('Rounding verification complete:', destination)


if __name__ == '__main__':
    main()
