"""GPL-2.0-or-later. Generate exact polynomial and binary64 error certificates.

All numbers serialized into the certificate are exact rationals. No float is
used to establish an error inequality. Binary64 is used only to decode pinned
coefficient values and compare their magnitudes before exact rationalization.
"""
from __future__ import annotations
import json
import math
import struct
from fractions import Fraction as Q
from pathlib import Path
from source import HERE, ROOT, checked, digest

UNIT = Q(1, 2**53)
ETA = Q(1, 2**100)  # Conservative replacement for half a subnormal ulp 2^-1075.
GRID = 2**100
DATA_SHA = '29915576d0a6555766b99485ac3056ee415e86df4fce282611c31afb329ad062'


def encode(value: Q | int) -> str:
    value = Q(value)
    return f'{value.numerator}/{value.denominator}'


def ceil_grid(value: Q) -> Q:
    return Q(-(-(value * GRID).numerator // (value * GRID).denominator), GRID)


def trim(poly):
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_add(a, b, sign=1):
    return trim([(a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b)))])


def poly_mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)


class Graph:
    def __init__(self):
        self.nodes = []
    def node(self, op, args, magnitude, error, poly=None, **extra):
        entry = {'op': op, 'args': args, 'magnitude': encode(magnitude), 'error': encode(error), **extra}
        if poly is not None:
            entry['polynomial'] = poly
        self.nodes.append(entry)
        return len(self.nodes) - 1
    def literal(self, number):
        return self.node('literal', [], abs(number), 0, [number], value=number)
    def operation(self, op, a, b):
        left, right = self.nodes[a], self.nodes[b]
        ma, mb, ea, eb = (Q(left['magnitude']), Q(right['magnitude']), Q(left['error']), Q(right['error']))
        poly = None
        if 'polynomial' in left and 'polynomial' in right:
            pa, pb = left['polynomial'], right['polynomial']
            if op in ('add', 'sub'):
                poly = poly_add(pa, pb, 1 if op == 'add' else -1)
            elif op == 'mul':
                poly = poly_mul(pa, pb)
        if op in ('add', 'sub'):
            propagated, magnitude = ea + eb, ma + mb
        elif op == 'mul':
            propagated, magnitude = ma * eb + mb * ea + ea * eb, ma * mb
        else:
            raise ValueError('Division is admitted only for exact power-of-two scaling')
        if poly is not None:
            magnitude = sum(abs(x) for x in poly)
        error = ceil_grid(propagated + UNIT * (magnitude + propagated) + ETA)
        return self.node(op, [a, b], magnitude, error, poly)
    def expression(self, tree, variables):
        if isinstance(tree, str):
            return variables[tree]
        if tree[0] == 'constant':
            return self.literal(tree[1])
        return self.operation(tree[0], self.expression(tree[1], variables), self.expression(tree[2], variables))


def coefficient_envelopes(data: bytes) -> list[dict]:
    if digest(data) != DATA_SHA:
        raise ValueError('Unpinned DE440 data')
    start, end, step = struct.unpack_from('<3d', data, 2652)
    if (start, end, step, len(data)) != (2287184.5, 2688976.5, 32.0, 102272352):
        raise ValueError('Unsupported DE440 layout')
    profiles = []
    names = ['mercury', 'venus', 'earth-moon-barycenter', 'mars', 'jupiter', 'saturn', 'uranus', 'neptune', 'pluto', 'geocentric-moon', 'barycentric-sun', 'nutations', 'librations']
    expected = 3
    for i, name in enumerate(names):
        pointer, ncf, na = struct.unpack_from('<3I', data, 2696 + i * 12 if i < 12 else 2844)
        ncm = 2 if i == 11 else 3
        if pointer != expected or not 2 <= ncf < 18 or na not in (1, 2, 4, 8):
            raise ValueError('Unsupported interpolation table')
        profiles.append({'name': name, 'pointer': pointer, 'ncf': ncf, 'na': na, 'ncm': ncm, 'maxima': [0.] * ncf})
        expected += ncf * ncm * na
    if expected != 1019:
        raise ValueError('Coefficient coverage is incomplete')
    for record in range(12556):
        values = struct.unpack_from('<1018d', data, (record + 2) * 8144)
        if values[:2] != (start + record * 32, start + (record + 1) * 32):
            raise ValueError('Record time mismatch')
        for p in profiles:
            for component in range(p['ncm'] * p['na']):
                offset = p['pointer'] - 1 + component * p['ncf']
                for k in range(p['ncf']):
                    value = abs(values[offset + k])
                    if not math.isfinite(value):
                        raise ValueError('Nonfinite coefficient')
                    if value > p['maxima'][k]:
                        p['maxima'][k] = value
    for p in profiles:
        p['bounds'] = [encode(Q(value)) for value in p.pop('maxima')]
    return profiles


def generate(data: bytes) -> dict:
    expressions, source = checked()
    graph = Graph()
    zero, one, two = (graph.literal(value) for value in (0, 1, 2))
    x = graph.node('input-x', [], 1, 0, [0, 1])
    # twot=tc+tc is exact for representable |tc|<=1; its basis-rounding
    # certificate conservatively permits a rounding error as well.
    twot = graph.operation('add', x, x)
    p, d, a = [one, x], [zero, one], [zero, zero]
    for n in range(2, 17):
        p.append(graph.expression(expressions['position'], {'twot': twot, 'p1': p[-1], 'p2': p[-2]}))
    for n in range(2, 17):
        d.append(graph.expression(expressions['velocity'], {'twot': twot, 'd1': d[-1], 'd2': d[-2], 'p1': p[n - 1]}))
    for n in range(2, 17):
        a.append(graph.expression(expressions['acceleration'], {'twot': twot, 'a1': a[-1], 'a2': a[-2], 'd1': d[n - 1]}))
    profiles = coefficient_envelopes(data)
    for profile in profiles:
        cf = [graph.node('coefficient', [], Q(bound), 0, degree=k, profile=profile['name']) for k, bound in enumerate(profile['bounds'])]
        profile['coefficientNodes'] = cf
        outputs = {}
        for kind, basis, lower in [('position', p, 0), ('velocity', d, 1), ('acceleration', a, 0)]:
            total = zero
            for k in reversed(range(lower, profile['ncf'])):
                product = graph.operation('mul', basis[k], cf[k])
                total = graph.operation('add', total, product)
            if kind != 'position':
                scale = graph.node('exact-scale', [], Q(profile['na'], 16), 0, na=profile['na'], step=32)
                total = graph.operation('mul', total, scale)
                if kind == 'acceleration':
                    total = graph.operation('mul', total, scale)
            outputs[kind] = total
        profile['outputs'] = outputs
    return {'schema': 1, 'source': source, 'expressions': expressions,
      'arithmetic': {'format': 'IEEE-754 binary64', 'rounding': 'nearest, ties to even', 'unitRoundoff': encode(UNIT),
        'underflowAllowance': encode(ETA), 'exactHalfMinimumSubnormal': '1/' + str(2**1075),
        'overflowGuard': encode(Q(2**1023)), 'certificateGrid': encode(Q(1, GRID)),
        'assumptions': ['No fast-math/reassociation/FMA contraction', 'Gradual underflow', 'Finite representable input tc in [-1,1]',
          'Inputs are the stored binary64 JPL coefficients, interpreted as exact dyadic reals', 'Successful JPL I/O and initialized, unmodified cache']},
      'data': {'sha256': DATA_SHA, 'recordCount': 12556, 'recordBytes': 8144, 'profiles': profiles},
      'nodes': graph.nodes, 'basis': {'position': p, 'velocity': d, 'acceleration': a},
      'scope': 'Per-component absolute arithmetic error at the return of source-ordered interp(), relative to exact evaluation of the same stored polynomial. Bounds stop BEFORE km-to-AU conversion, barycentric/heliocentric subtraction, Earth/Moon combinations, and target-center combinations. They exclude JPL model/fit error, coefficient-generation error, time-scale conversion error, and whole-orbit error.'}


if __name__ == '__main__':
    data = (ROOT / '.cache/linux_p1550p2650.440').read_bytes()
    result = generate(data)
    target = HERE / 'evidence/certificate.json'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + '\n')
    print('Generated', len(result['nodes']), 'local arithmetic certificates in', target)
