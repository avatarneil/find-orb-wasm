#!/usr/bin/env python3
"""GPL-2.0-or-later. Reject arithmetic mutations using previously checked modules."""
from __future__ import annotations
import argparse
import json
import subprocess
import tempfile
from pathlib import Path
from source import HERE, ROOT, digest
from kernel_tools import proof_tools, require_rejection


def run(lean_root: Path, mathlib: Path, modules: Path, tools=None):
    modules = modules.resolve()
    for name in ['Foundations', 'Roundoff', 'BridgeSupport']:
        if not (modules / (name + '.olean')).is_file():
            raise RuntimeError('Missing checked module; run verification/kernel/check.py first: ' + name)
    tools = tools or proof_tools(lean_root, mathlib, modules)
    evidence = HERE / 'evidence'
    evidence.mkdir(parents=True, exist_ok=True)
    original = (HERE / 'Recurrences.lean').read_text()
    mutation = original.replace('+ position (n + 1) + position (n + 1)', '+ position (n + 1)', 1)
    if mutation == original:
        raise ValueError('Kernel mutation target missing')
    bridge = (HERE / 'RoundedDAG.lean').read_text()
    before = 'rnd (r4 rnd x c * r3 rnd x c)'
    if before not in bridge or 'def e6 ' not in bridge:
        raise ValueError('Bridge mutation target missing')
    changed = bridge[:bridge.index('def e6 ')].replace(before, 'rnd (r4 rnd x c + r3 rnd x c)', 1)
    cases = [
      ('WrongRecurrences', mutation, 'kernel-negative.log', ('unsolved goals',)),
      ('WrongRoundedDAG', changed + '\nend\nend FindOrbEphemerisBridge\n',
        'kernel-bridge-negative.log', ('Type mismatch', 'r4 rnd x c + r3 rnd x c')),
    ]
    results = []
    with tempfile.TemporaryDirectory(prefix='ephemeris-kernel-negative-', dir=ROOT / '.cache') as folder:
        for name, contents, log, expected in cases:
            target = Path(folder) / (name + '.lean')
            target.write_text(contents)
            command = [tools['lean'], '--trust=0', str(target)]
            process = subprocess.run(command, cwd=ROOT, env=tools['env'], text=True,
              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
            (evidence / log).write_text(process.stdout)
            require_rejection(process.returncode, process.stdout, expected)
            results.append({'name': name, 'rejected': True, 'returnCode': process.returncode,
              'mutationSHA256': digest(contents.encode()), 'expectedMessages': list(expected), 'log': log})
    report = {'schema': 1, 'performed': True, 'passed': True, 'toolchain': tools['versions'],
      'modules': str(modules), 'trustLevel': 0, 'controls': results,
      'sourceSHA256': {name: digest((HERE / name).read_bytes()) for name in
        ['Recurrences.lean', 'RoundedDAG.lean']},
      'moduleSHA256': {name: digest((modules / (name + '.olean')).read_bytes()) for name in
        ['Foundations', 'Roundoff', 'BridgeSupport']},
      'deletedDerivativeTermRejected': True, 'returnCode': results[0]['returnCode'],
      'wrongRoundedOperationRejected': True, 'bridgeReturnCode': results[1]['returnCode']}
    (evidence / 'kernel-negatives.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Rejected both ephemeris Lean arithmetic mutations', flush=True)
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-root', type=Path, default=ROOT / '.cache/proof-tools/lean-4.24.0-darwin_aarch64')
    parser.add_argument('--mathlib', type=Path, default=ROOT / '.cache/mathlib')
    parser.add_argument('--modules', type=Path, default=ROOT / '.cache/kernel-modules')
    args = parser.parse_args()
    run(args.lean_root.resolve(), args.mathlib.resolve(), args.modules.resolve())


if __name__ == '__main__':
    main()
