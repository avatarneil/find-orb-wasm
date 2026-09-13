#!/usr/bin/env python3
"""GPL-2.0-or-later. Fail-closed mutations of retained generated proof inputs."""
from __future__ import annotations
import hashlib
import json
import re
import subprocess
import sys
import os
from pathlib import Path
from check import HERE, ROOT, tools


def main():
    output = HERE / 'evidence/negative.json'
    report = {'passed': False, 'status': 'running', 'controls': []}
    output.write_text(json.dumps(report) + '\n')
    try:
        if sys.flags.optimize:
            raise RuntimeError('Unoptimized Python required')
        lean, env, _ = tools()
        # The central runner has freshly compiled and replayed these modules;
        # prefer them over any older standalone development cache.
        env['LEAN_PATH'] = str(ROOT / '.cache/kernel-modules') + os.pathsep + env['LEAN_PATH']
        text = (HERE / 'RKFLinear.lean').read_text()
        work = ROOT / '.cache/integrator-certified-negatives'
        work.mkdir(parents=True, exist_ok=True)
        # Keep generated positive statements. Change a genuine first-stage
        # source coefficient and retain its extracted polynomial certificate.
        first = re.search(r'^def exact5 .*$', text, re.M)
        assert first and ':=' in first[0]
        weight = text[:text.index('theorem bound5')]
        weight = weight.replace(first[0], first[0].split(':=')[0] + ':= (1 : ℝ)')
        # Keep the complete node-3 rounding proof, reduce its claimed error to
        # zero, and require its positive rounding-budget inequality to fail.
        budget = text[:text.index('def exact4')]
        pattern = r'(\|rounded3 rnd h y - exact3 h y\| ≤ )[^\n]+'
        budget, count = re.subn(pattern, r'\g<1>(0 : ℝ) := by', budget)
        assert count == 1
        for name, mutated in [('wrong-first-stage-weight', weight), ('zero-rounding-budget', budget)]:
            path = work / (name + '.lean')
            path.write_text(mutated + '\nend RKFLinear\nend\nend FindOrbLinear\n')
            result = subprocess.run([lean, '--trust=0', str(path)], cwd=ROOT, env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
            (work / (name + '.log')).write_text(result.stdout)
            if result.returncode == 0 or 'unsolved goals' not in result.stdout or re.search(r'PANIC', result.stdout, re.I):
                raise RuntimeError('Mutation did not fail by a mathematical Lean goal: ' + name + '\n' + result.stdout[-3000:])
            report['controls'].append({'name': name, 'rejected': True, 'stage': 'Lean proof checking',
                                       'sourceSHA256': hashlib.sha256(path.read_bytes()).hexdigest(),
                                       'logSHA256': hashlib.sha256(result.stdout.encode()).hexdigest()})
        sys.path.insert(0, str(ROOT / 'verification/integrator'))
        from core import sources, definition, sha
        from generate import require_source_contract
        _, corrected, provenance = sources(ROOT / '.wasm-engine/sources')
        function = definition(corrected, 'take_rk_stepl')
        changed = function.replace('RKF_A1, RKF_A2, RKF_A3', 'RKF_A1, RKF_A3, RKF_A3')
        assert function != changed
        try:
            require_source_contract(changed, sha(function))
        except ValueError:
            pass
        else:
            raise RuntimeError('Source contract accepted shifted stage times')
        report['controls'].append({'name': 'shifted-stage-time', 'rejected': True,
            'stage': 'strict source-function hash contract', 'expectedSHA256': sha(function),
            'mutatedSHA256': sha(changed),
            'limitation': "The autonomous y'=y mathematical graph is invariant under stage-time changes. This control checks source identity, not sensitivity of the autonomous numerical theorem."})
        report['passed'], report['status'] = True, 'complete'
    except BaseException as error:
        report['status'], report['error'] = 'failed', str(error)
        raise
    finally:
        output.write_text(json.dumps(report, indent=2) + '\n')
    print('Three integrator certificate mutation controls passed')


if __name__ == '__main__':
    main()
