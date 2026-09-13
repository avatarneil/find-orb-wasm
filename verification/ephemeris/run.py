#!/usr/bin/env python3
"""GPL-2.0-or-later. Reproduce all ephemeris certificates and checks."""
from __future__ import annotations
import argparse
import json
import re
import subprocess
from pathlib import Path
from source import HERE, ROOT, digest
from generate import generate
from check import check
from export_lean import export
from export_bridge import export as export_bridge
from negative import run as negatives
from control import run as control
from kernel_tools import proof_tools, require_success
from kernel_negatives import run as kernel_negatives

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def kernel(args):
    output = ROOT / '.cache/ephemeris-kernel'
    output.mkdir(parents=True, exist_ok=True)
    tools = proof_tools(args.lean_root, args.mathlib, output)
    lean, env = tools['lean'], tools['env']
    results = []
    sources = [ROOT / 'verification/kernel/Foundations.lean'] + [HERE / filename for filename in
      ['Recurrences.lean', 'Roundoff.lean', 'NumericalCertificates.lean', 'BridgeSupport.lean', 'RoundedDAG.lean']]
    for source in sources:
        filename = source.name
        text = source.read_text()
        if source.parent == HERE and re.search(r'\b(sorry|admit|axiom|native_decide)\b', text):
            raise ValueError('Forbidden unchecked proof construct in ' + filename)
        expected = re.findall(r'^#print axioms ([\w.]+)$', text, re.M)
        if not expected:
            raise ValueError('Missing explicit theorem audit')
        command = [lean, '--trust=0', '--root=' + str(source.parent), '-o', str(output / filename.replace('.lean', '.olean')), str(source)]
        run = subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
        (HERE / 'evidence' / (filename.replace('.lean', '') + '-kernel.log')).write_text(run.stdout)
        require_success(run.returncode, run.stdout)
        audited = []
        pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
        for match in re.finditer(pattern, run.stdout):
            name = match.group(1)
            axioms = {item.strip() for item in (match.group(2) or '').split(',') if item.strip()}
            if not axioms <= ALLOWED_AXIOMS:
                raise ValueError('Unexpected theorem axiom: ' + name + ' ' + str(axioms))
            audited.append({'name': name, 'axioms': sorted(axioms)})
        if [row['name'].split('.')[-1] for row in audited] != [name.split('.')[-1] for name in expected]:
            raise ValueError('Incomplete theorem dependency audit: ' + filename)
        results.append({'source': str(source.relative_to(ROOT)), 'sha256': digest(source.read_bytes()), 'theorems': audited,
          'theoremCount': len(audited), 'command': command, 'returnCode': run.returncode})
        print('Lean kernel checked', filename, ':', len(audited), 'theorems', flush=True)
    negative = kernel_negatives(args.lean_root, args.mathlib, output, tools)
    return {'performed': True, 'lean': tools['versions']['leanVersion'],
      'mathlib': tools['versions']['mathlibCommit'], 'toolchain': tools['versions'], 'trustLevel': 0, 'checks': results,
      'negative': negative,
      'scope': 'Universal exact-polynomial derivative and L1 theorems, every concrete rational node inequality, and all 13 profiles/39 final output bounds instantiated through the exact/rounded DAG under an explicit bounded real rounding-function premise. The C++/IEEE/JPL-to-DAG connection is independently checked in Python and explicitly remains part of the trusted boundary, not an end-to-end C/compiler theorem.'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-root', type=Path, default=ROOT / '.cache/proof-tools/lean-4.24.0-darwin_aarch64')
    parser.add_argument('--mathlib', type=Path, default=ROOT / '.cache/mathlib')
    parser.add_argument('--certificates-only', action='store_true',
      help='Regenerate and check certificates; central kernel/check.py performs the Lean checks')
    args = parser.parse_args()
    args.lean_root, args.mathlib = args.lean_root.resolve(), args.mathlib.resolve()
    evidence = HERE / 'evidence'
    evidence.mkdir(parents=True, exist_ok=True)
    data = (ROOT / '.cache/linux_p1550p2650.440').read_bytes()
    certificate = generate(data)
    (evidence / 'certificate.json').write_text(json.dumps(certificate, indent=2) + '\n')
    checked = check(certificate, data)
    (evidence / 'checked.json').write_text(json.dumps(checked, indent=2) + '\n')
    print('Independently checked', checked['coefficientsChecked'], 'coefficients and', checked['nodesChecked'], 'arithmetic nodes', flush=True)
    controls = control()
    mutations = negatives()
    export(certificate)
    export_bridge(certificate)
    kernels = ({'performed': False, 'reason': '--certificates-only: delegated to the central kernel runner',
      'report': 'verification/kernel/evidence/report.json',
      'negativeControlsReport': 'verification/ephemeris/evidence/kernel-negatives.json',
      'requiredNextCommands': ['python verification/kernel/check.py',
        'python verification/ephemeris/kernel_negatives.py']} if args.certificates_only else kernel(args))
    report = {'schema': 1, 'certificateSHA256': digest((evidence / 'certificate.json').read_bytes()),
      'checked': checked, 'control': controls, 'mutations': mutations, 'kernel': kernels,
      'primarySources': [
        'https://github.com/Bill-Gray/jpl_eph/blob/a73f25e54d02b99b1c0d9a9d6c61acfbb2fa3a26/jpleph.cpp',
        'https://ssd.jpl.nasa.gov/planets/eph_export.html',
        'https://dlmf.nist.gov/18.9.E21',
        'https://dlmf.nist.gov/18.9.T1',
        'https://gappa.gitlabpages.inria.fr/gappa/arithmetic.html',
        'https://gappa.gitlabpages.inria.fr/gappa/invoking.html',
        'https://flocq.gitlabpages.inria.fr/theos.html',
      ]}
    (evidence / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Ephemeris ' + ('certificate verification complete; kernel checks delegated:' if args.certificates_only else 'verification complete:'), evidence / 'report.json')


if __name__ == '__main__':
    main()
