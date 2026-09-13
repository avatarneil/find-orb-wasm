"""GPL-2.0-or-later. Exact-rational witnesses and explicit backend conformance probes.

These finite checks do not replace the universal Lean rounding theorem.
"""
from fractions import Fraction as Q
import hashlib
import json
import subprocess
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError('Optimized Python is forbidden for rounding verification')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DELTA = Q(1, 2**1074)


def decode(bits):
    exponent, fraction = (bits >> 52) & 2047, bits & (2**52 - 1)
    if exponent == 2047:
        raise ValueError('Nonfinite binary64 encoding')
    magnitude = (fraction if exponent == 0 else 2**52 + fraction) * DELTA * 2**max(0, exponent - 1)
    return -magnitude if bits >> 63 else magnitude


def round_bits(value):
    absolute = abs(value)
    if absolute >= 2**1023:
        raise ValueError('Outside proved conservative overflow guard')
    n = max(0, absolute.numerator.bit_length() - absolute.denominator.bit_length() + 1022)
    step = DELTA * 2**n
    while absolute >= 2**53 * step:
        step *= 2
        n += 1
    while n and absolute < 2**52 * step:
        step /= 2
        n -= 1
    scaled = absolute / step
    q, remainder = divmod(scaled.numerator, scaled.denominator)
    twice = 2 * remainder
    if twice > scaled.denominator or (twice == scaled.denominator and q % 2):
        q += 1
    if q == 2**53:
        exponent, fraction = n + 2, 0
    elif q >= 2**52:
        exponent, fraction = n + 1, q - 2**52
    else:
        if n:
            raise ValueError('Impossible unnormalized candidate')
        exponent, fraction = 0, q
    return ((1 if value < 0 else 0) << 63) + (exponent << 52) + fraction


def run():
    edges = []
    for exponent in [0, 1, 2, 511, 1022, 1023, 1024, 1535, 2044, 2045, 2046]:
        for fraction in [0, 1, 2, 2**51, 2**52 - 2, 2**52 - 1]:
            for sign in [0, 1]:
                edges.append((sign << 63) + (exponent << 52) + fraction)
    partners = [0, 1, 2, 3, 0x0010000000000000, 0x3fe0000000000000,
      0x3fefffffffffffff, 0x3ff0000000000000, 0x3ff8000000000000,
      0x4000000000000000, 0x3ca0000000000000, 0x3cb0000000000000]
    partners += [v | 2**63 for v in partners]
    vectors, expected = [], []
    underflow, ties, binade_carries = 0, 0, 0
    for left in edges:
        a = decode(left)
        for right in partners:
            b = decode(right)
            for op in ['add', 'sub', 'mul', 'div']:
                if op == 'div' and not b:
                    continue
                exact = {'add': lambda: a+b, 'sub': lambda: a-b,
                  'mul': lambda: a*b, 'div': lambda: a/b}[op]()
                if abs(exact) >= 2**1023:
                    continue
                bits = round_bits(exact)
                error = abs(decode(bits) - exact)
                bound = Q(1, 2**53) * abs(exact) + DELTA / 2
                if error > bound:
                    raise ValueError('Rational encoder contradicts proved bound')
                if exact and abs(exact) < 2**52 * DELTA:
                    underflow += 1
                neighbors = [v for v in [bits-1, bits+1] if 0 <= v < 2**64 and (v >> 52) & 2047 != 2047]
                if error and any(error == abs(decode(other) - exact) for other in neighbors):
                    ties += 1
                    if bits % 2:
                        raise ValueError('Odd tie result')
                if error and bits % 2**52 == 0 and ((bits >> 52) & 2047) > 0:
                    binade_carries += 1
                vectors.append({'op': op, 'left': f'{left:016x}', 'right': f'{right:016x}'})
                expected.append(bits)
    process = subprocess.run(['node', str(HERE / 'wasm_probe.mjs')], cwd=ROOT,
      input=json.dumps(vectors), text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    if process.returncode:
        raise RuntimeError('WebAssembly backend probe failed: ' + process.stderr)
    actual = json.loads(process.stdout)
    if len(actual['results']) != len(expected):
        raise RuntimeError('Incomplete WebAssembly probe output')
    for vector, want, got in zip(vectors, expected, actual['results']):
        got = int(got, 16)
        # The Lean real-valued theorem intentionally quotients +0 and -0.
        if got != want and not (decode(got) == decode(want) == 0):
            raise RuntimeError('WebAssembly/model mismatch: ' + str(vector))
    report = {'schema': 1, 'passed': True, 'cases': len(vectors),
      'subnormalExactResults': underflow, 'midpointTies': ties, 'roundedBinadeBoundaries': binade_carries,
      'node': actual['node'], 'v8': actual['v8'],
      'wasmBinarySHA256': hashlib.sha256(bytes.fromhex(actual['wasmBinaryHex'])).hexdigest(),
      'vectorsSHA256': hashlib.sha256(json.dumps(vectors, sort_keys=True).encode()).hexdigest(),
      'scope': 'Finite direct-WASM primitive conformance probes against exact rational nearest-even decoding; not a proof of the runtime or compiler. Signed zeros compared through the proved real-value quotient.'}
    (HERE / 'evidence').mkdir(exist_ok=True)
    (HERE / 'evidence/conformance.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Matched', len(vectors), 'direct WebAssembly primitive results', flush=True)
    return report


if __name__ == '__main__':
    run()
