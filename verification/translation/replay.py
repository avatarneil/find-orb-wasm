#!/usr/bin/env python3
"""Replay the recorded proof and counterexample obligations in both solvers."""
from pathlib import Path
import argparse
import json
import z3
from verify import sha, replay_cvc

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('report',nargs='?',type=Path,default=Path(__file__).parent/'evidence/report.json')
args=parser.parse_args()
report=json.loads(args.report.read_text())
for record in report['obligations']:
    path=args.report.parent/'obligations'/(record['name']+'.smt2')
    smt=path.read_text()
    if sha(smt.encode())!=record['smt2SHA256']:raise ValueError('Modified SMT artifact '+str(path))
    solver=z3.Solver();solver.set(timeout=30000);solver.from_string(smt)
    result=str(solver.check());independent=replay_cvc(smt)
    if result!=record['z3'] or independent!=record['cvc5']:
        raise AssertionError(f'{record["name"]}: replay disagreement {result}/{independent}')
    print(f'{record["name"]}: {result}/{independent}',flush=True)
print('All recorded SMT artifacts replayed; this does not recompile or revalidate current source/binary hashes.')
