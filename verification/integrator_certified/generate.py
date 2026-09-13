#!/usr/bin/env python3
"""GPL-2.0-or-later. Source-pinned, source-ordered linear RK proof certificates.

Python chooses the propositions; Lean checks their connected proofs. This is
not a verified C++ parser, and the finite compiled correspondence remains a
separate empirical boundary. No assumption identifies decimal coefficients
with the actual evaluated binary64 constants.
"""
from __future__ import annotations
import hashlib
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
if sys.flags.optimize:
    (HERE / 'evidence/certificate.json').write_text(json.dumps({
        'passed': False, 'status': 'failed', 'error': 'Unoptimized Python required'}) + '\n')
    raise RuntimeError('Unoptimized Python required')
sys.path.insert(0, str(ROOT / 'verification/integrator'))
from core import definition, qjson, round_binary, sha, sources, tableau
from compiled import decode, exact_scalar

H, Y, U, ETA = Q(1, 16), Q(1, 2), Q(1, 2**113), Q(1, 2**200)
FUNCTION_SHA256 = {
    'rkf': '133a850a5393a2c6240590e42b65223eced81ae3eb7ed5e3d8acaecb003a33de',
    'pd': '2c5aca8cf131313a9f6a49e46bb47fc0a3112abf27e8647e73b1e662f55d61ad',
}


def require_source_contract(text, expected_sha256):
    if sha(text) != expected_sha256:
        raise ValueError('Integrator source-function contract changed')


def q(value):
    value = Q(value)
    return f'({value.numerator}/{value.denominator} : ℝ)'


def ceiling(value, bits):
    scaled = value * 2**bits
    return Q(-(-scaled.numerator // scaled.denominator), 2**bits)


def plus(a, b):
    result = dict(a)
    for power, value in b.items():
        result[power] = result.get(power, Q(0)) + value
    return {p: v for p, v in result.items() if v}


def times(a, b):
    result = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            power = (i+k, j+l)
            result[power] = result.get(power, Q(0)) + x*y
    return {p: v for p, v in result.items() if v}


def terms(poly):
    return '[' + ', '.join(f'({q(value)}, {i}, {j})' for (i, j), value in sorted(poly.items())) + ']'


class Graph:
    def __init__(self):
        self.nodes = []

    def add(self, op, args=(), value=None):
        if op == 'h':
            poly = {(1, 0): Q(1)}
        elif op == 'y':
            poly = {(0, 1): Q(1)}
        elif op == 'literal':
            poly = {(0, 0): Q(value)} if value else {}
        else:
            a, b = [self.nodes[k] for k in args]
            poly = (plus if op == 'add' else times)(a['poly'], b['poly'])
        magnitude = ceiling(sum(abs(v) * H**i * Y**j for (i, j), v in poly.items()), 40)
        propagation = Q(0)
        if op in ('add', 'mul'):
            propagation = a['error'] + b['error'] if op == 'add' else (
                a['magnitude']*b['error'] + b['magnitude']*a['error'] + a['error']*b['error'])
            error = ceiling(propagation + U*(magnitude+propagation) + ETA, 190)
            assert magnitude + propagation < 100
        else:
            error = Q(0)
        self.nodes.append(dict(op=op, args=list(args), value=value, poly=poly,
                               magnitude=magnitude, propagation=propagation, error=error))
        return len(self.nodes)-1


def graph(tab):
    g = Graph()
    h, y, zero = g.add('h'), g.add('y'), g.add('literal', value=Q(0))
    # x - 0 is real x + 0. RN also agrees modulo zero sign; preserve the
    # operation here instead of assuming RN is idempotent for arbitrary reals.
    seed = g.add('add', (y, zero))
    derivatives = [g.add('add', (y, zero))]
    stages = [y]
    for weights in [row[:i] for i, row in enumerate(tab['A']) if i] + [tab['b']]:
        acc = zero
        for weight, derivative in zip(weights, derivatives):
            coefficient = g.add('literal', value=weight)
            product = g.add('mul', (coefficient, derivative))
            acc = g.add('add', (acc, product))
        state = g.add('add', (g.add('mul', (acc, h)), seed))
        state = g.add('add', (state, zero))
        stages.append(state)
        if len(derivatives) < len(tab['b']):
            derivatives.append(g.add('add', (state, zero)))
    return g, stages


def model_run(g, h, y, rounded):
    values = []
    for node in g.nodes:
        op = node['op']
        if op in ('h', 'y', 'literal'):
            value = h if op == 'h' else y if op == 'y' else node['value']
        else:
            a, b = [values[k] for k in node['args']]
            value = a+b if op == 'add' else a*b
            if rounded:
                value = round_binary(value, 113)
        values.append(value)
    return values[-1]


def emit(method, g):
    name = 'RKFLinear' if method == 'rkf' else 'PDLinear'
    lines = ['import LinearSupport', '/- GPL-2.0-or-later. Generated connected proof; see generate.py. -/',
             'set_option maxRecDepth 8192', 'set_option maxHeartbeats 1600000',
             'set_option exponentiation.threshold 2048', 'set_option linter.unusedVariables false',
             'namespace FindOrbLinear', 'noncomputable section', 'namespace ' + name]
    audits = []
    for i, node in enumerate(g.nodes):
        op, args = node['op'], node['args']
        if op in ('h', 'y', 'literal'):
            exact = 'h' if op == 'h' else 'y' if op == 'y' else q(node['value'])
            rounded = exact
        else:
            symbol = '+' if op == 'add' else '*'
            exact = f'exact{args[0]} h y {symbol} exact{args[1]} h y'
            rounded = f'rnd (rounded{args[0]} rnd h y {symbol} rounded{args[1]} rnd h y)'
        lines += [f'def exact{i} (h y : ℝ) : ℝ := {exact}',
                  f'def rounded{i} (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := {rounded}',
                  f'theorem polynomial{i} (h y : ℝ) : exact{i} h y = evaluate {terms(node["poly"])} h y := by',
                  '  simp only [' + ', '.join([f'exact{i}'] + [f'polynomial{k}' for k in dict.fromkeys(args)] + ['evaluate']) + '] <;> ring',
                  f'theorem bound{i} (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :',
                  f'    |exact{i} h y| ≤ {q(node["magnitude"])} := by',
                  f'  rw [polynomial{i}]',
                  f'  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])',
                  f'theorem error{i} (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)',
                  f'    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :',
                  f'    |rounded{i} rnd h y - exact{i} h y| ≤ {q(node["error"])} := by']
        if op in ('h', 'y', 'literal'):
            lines += [f'  simp [rounded{i}, exact{i}]']
        else:
            a, b = args
            lines += [f'  unfold rounded{i} exact{i}',
                      '  apply rounded_step rnd hrnd (propagation := ' + q(node['propagation']) + ') (magnitude := ' + q(node['magnitude']) + ')']
            if op == 'add':
                lines += [f'  · convert FindOrb.add_error (error{a} rnd hrnd h y hh hy) (error{b} rnd hrnd h y hh hy) using 1 <;> norm_num']
            else:
                lines += [f'  · convert FindOrb.mul_error (bound{a} h y hh hy) (bound{b} h y hh hy)',
                          f'      (error{a} rnd hrnd h y hh hy) (error{b} rnd hrnd h y hh hy) using 1 <;> norm_num']
            lines += [f'  · exact bound{i} h y hh hy', '  · norm_num', '  · norm_num']
        audits.extend([f'polynomial{i}', f'error{i}'])
    end = len(g.nodes)-1
    polynomial = g.nodes[end]['poly']
    taylor = {(i, 1): Q(1, math.factorial(i)) for i in range(16)}
    difference = plus(polynomial, {p: -v for p, v in taylor.items()})
    coefficient = sum(abs(v)*H**i*Y**j for (i, j), v in difference.items())
    tail = Y*H**16*Q(17, math.factorial(16)*16)
    rounding = g.nodes[end]['error']
    total = coefficient + tail + rounding
    target = Q(1075, 10**14) if method == 'rkf' else Q(2895, 10**21)
    assert total < target
    lines += [f'def step := rounded{end}',
              'theorem stored_vs_taylor (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :',
              f'    |exact{end} h y - y * (∑ m ∈ Finset.range 16, h^m / m.factorial)| ≤ {q(coefficient)} := by',
              f'  have hid : exact{end} h y - y * (∑ m ∈ Finset.range 16, h^m / m.factorial) =',
              f'      evaluate {terms(difference)} h y := by',
              f'    rw [polynomial{end}]',
              '    norm_num [evaluate, Finset.sum_range_succ, Nat.factorial] <;> ring',
              '  rw [hid]',
              '  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])',
              'theorem local_error (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)',
              '    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :',
              f'    |step rnd h y - y * Real.exp h| ≤ {q(target)} := by',
              f'  have ht : |y * (∑ m ∈ Finset.range 16, h^m / m.factorial) - y * Real.exp h| ≤ {q(tail)} := by',
              '    rw [← mul_sub, abs_mul, abs_sub_comm]',
              '    exact le_trans (mul_le_mul hy (exp_taylor_bound h hh) (abs_nonneg _) (by norm_num)) (by norm_num [Nat.factorial])',
              f'  have he := FindOrb.error_trans (error{end} rnd hrnd h y hh hy)',
              '    (FindOrb.error_trans (stored_vs_taylor h y hh hy) ht)',
              '  exact le_trans he (by norm_num)',
              'theorem multiple_steps (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)',
              '    (values steps : Nat → ℝ) (initial initialError : ℝ)',
              '    (hstep : ∀ n, |steps n| ≤ 1/16) (hstate : ∀ n, |values n| ≤ 1/2)',
              '    (hrec : ∀ n, values (n+1) = step rnd (steps n) (values n))',
              '    (hzero : |values 0 - initial| ≤ initialError) :',
              '    ∀ n, |values n - initial * Real.exp (elapsedTime steps n)| ≤',
              f'      FindOrb.errorBudget (16/15) {q(target)} initialError n := by',
              '  apply FindOrb.global_error_bound (ha := by norm_num)',
              '  · simpa [elapsedTime] using hzero',
              '  · intro n',
              '    rw [hrec n, sampled_solution_step]',
              '    exact accumulated_step (hstep n) (local_error rnd hrnd (steps n) (values n) (hstep n) (hstate n))',
              '#print axioms stored_vs_taylor', '#print axioms local_error', '#print axioms multiple_steps']
    lines += ['#print axioms ' + n for n in audits]
    lines += ['end ' + name, 'end', 'end FindOrbLinear']
    (HERE / (name + '.lean')).write_text('\n'.join(lines) + '\n')
    return dict(module=name, nodes=len(g.nodes), theoremRoots=len(audits)+3,
                storedPolynomial=terms(polynomial), coefficientDifferenceBound=qjson(coefficient),
                exponentialTailBound=qjson(tail), roundingBound=qjson(rounding),
                totalBound=qjson(total), advertisedBound=qjson(target))


def main():
    outfile = HERE / 'evidence/certificate.json'
    outfile.parent.mkdir(parents=True, exist_ok=True)
    outfile.write_text(json.dumps({'passed': False, 'status': 'running'}) + '\n')
    if sys.flags.optimize:
        raise RuntimeError('Unoptimized Python required')
    original, corrected, provenance = sources(ROOT / '.wasm-engine/sources')
    report = {'schema': 1, 'passed': False, 'source': provenance,
              'domain': 't0=0; zero reference; n_vals=n_orbit_params=6; first coordinate RHS copies its input and other derivatives zero; valid initialized disjoint buffers and successful allocation; |h|<=1/16, |y0|<=1/2; output first coordinate only; finite numerical values modulo zero sign',
              'rounding': 'Explicit real predicate |rnd(z)-z|<=2^-113*|z|+2^-200 for |z|<100; no C++/WASM or IEEE bridge is claimed here',
              'methods': {}, 'finiteInterpreterCorrespondence': [], 'recordedCompiledCorrespondence': []}
    compiled_path = ROOT / 'verification/integrator/evidence/compiled.json'
    compiled = json.loads(compiled_path.read_text())
    assert compiled['source']['correctedSha256'] == provenance['correctedSha256']
    report['recordedCompiledEvidenceSHA256'] = hashlib.sha256(compiled_path.read_bytes()).hexdigest()
    for method in ['rkf', 'pd']:
        tab = tableau(corrected, method, True)
        function_name = 'take_rk_stepl' if method == 'rkf' else 'take_pd89_step'
        require_source_contract(definition(corrected, function_name), FUNCTION_SHA256[method])
        assert tab['functionSha256'] == FUNCTION_SHA256[method]
        g, stages = graph(tab)
        report['methods'][method] = emit(method, g)
        for power in range(4, 9):
            h = Q(1, 2**power)
            for signed in (h, -h):
                observed = model_run(g, signed, Y, True)
                expected, _ = exact_scalar(tab, 9, signed, 113)
                assert observed == expected
                report['finiteInterpreterCorrespondence'].append({'method': method, 'step': qjson(signed), 'exactFiniteNumericalEquality': True})
        for configuration in ('wasmO0', 'wasmO3'):
            cases = [case for case in compiled['runs'][configuration]['cases']
                     if case['method'] == method and case['variant'] == 'corrected'
                     and case['equation'] == 9 and case['stepPower'] == 4]
            assert len(cases) == 1
            expected = decode(cases[0]['valueBits'], 113)
            assert expected == model_run(g, H, Y, True)
            report['recordedCompiledCorrespondence'].append({'method': method, 'configuration': configuration,
                'step': qjson(H), 'initial': qjson(Y), 'valueBits': cases[0]['valueBits'],
                'exactFiniteNumericalEqualityModuloZeroSign': True,
                'scope': 'Corroboration from the recorded source-extracted compiled probe, not a fresh compiler run or universal translation validation'})
        report['methods'][method]['functionSHA256'] = tab['functionSha256']
    report['passed'] = True
    report['status'] = 'complete'
    report['generatedLeanSHA256'] = {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                   for name in ('RKFLinear.lean', 'PDLinear.lean')}
    report['generatorSHA256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    outfile.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: {'nodes': value['nodes'], 'total': value['totalBound']['approx'],
                           'rounding': value['roundingBound']['approx']}
                      for key, value in report['methods'].items()}, indent=2))


if __name__ == '__main__':
    main()
