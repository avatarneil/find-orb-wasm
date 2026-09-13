"""GPL-2.0-or-later. Independent exact-arithmetic certificate checker.

Does not import generate.py. Reconstructs polynomial arithmetic with sparse
maps, checks source-derived expression trees and source-ordered sum topology,
and verifies each error inequality with Python arbitrary-precision integers.
The separate Lean export lets a proof-assistant kernel recheck the arithmetic.
"""
from __future__ import annotations
import json
import math
import struct
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as Rational
from source import HERE, ROOT, checked, digest


def require(condition, message):
    if not condition:
        raise ValueError(message)


def coefficients(poly):
    require(isinstance(poly, list) and poly and all(type(n) is int for n in poly), 'Noninteger polynomial')
    require(len(poly) == 1 or poly[-1] != 0, 'Noncanonical polynomial')
    return {i: x for i, x in enumerate(poly) if x}


def combine(op, a, b):
    result = dict(a) if op in ('add', 'sub') else {}
    if op in ('add', 'sub'):
        for i, value in b.items():
            result[i] = result.get(i, 0) + (value if op == 'add' else -value)
    else:
        for i, x in a.items():
            for j, y in b.items():
                result[i + j] = result.get(i + j, 0) + x * y
    return {i: x for i, x in result.items() if x}


def derivative(poly):
    return {i - 1: i * x for i, x in poly.items() if i and x}


def check_data(certificate, data):
    expected = '29915576d0a6555766b99485ac3056ee415e86df4fce282611c31afb329ad062'
    require(digest(data) == expected == certificate['data']['sha256'], 'Data hash mismatch')
    require(len(data) == 102272352, 'Data length mismatch')
    profiles = certificate['data']['profiles']
    names = ['mercury', 'venus', 'earth-moon-barycenter', 'mars', 'jupiter', 'saturn', 'uranus', 'neptune', 'pluto', 'geocentric-moon', 'barycentric-sun', 'nutations', 'librations']
    require([profile['name'] for profile in profiles] == names, 'Canonical profile names/order mismatch')
    require(len(profiles) == 13 and certificate['data']['recordCount'] == 12556 and certificate['data']['recordBytes'] == 8144, 'Data profile shape mismatch')
    bit_limits = []
    for index, profile in enumerate(profiles):
        pointer, ncf, na = struct.unpack_from('<III', data, 2696 + index * 12 if index < 12 else 2844)
        require((profile['pointer'], profile['ncf'], profile['na'], profile['ncm']) == (pointer, ncf, na, 2 if index == 11 else 3), 'Profile header mismatch')
        require(len(profile['bounds']) == ncf and 2 <= ncf < 18 and na in (1, 2, 4, 8), 'Unsupported profile')
        limits = []
        for bound in profile['bounds']:
            number = Rational(bound)
            require(number >= 0 and math.isfinite(float(number)) and Rational(float(number)) == number, 'Coefficient bound is not a finite exact binary64')
            limits.append(struct.unpack('<Q', struct.pack('<d', float(number)))[0])
        bit_limits.append(limits)
    # Nonnegative finite IEEE-754 encodings have the same order as unsigned
    # integers. This scan uses bit order, independent of generator float max().
    count = 0
    for record in range(12556):
        words = struct.unpack_from('<1018Q', data, (record + 2) * 8144)
        for profile, limits in zip(profiles, bit_limits):
            for slot in range(profile['ncm'] * profile['na']):
                begin = profile['pointer'] - 1 + slot * profile['ncf']
                for degree, bound in enumerate(limits):
                    absolute_bits = words[begin + degree] & ((1 << 63) - 1)
                    require(absolute_bits <= bound, f'Coefficient envelope violated: {profile["name"]}/{degree}/{record}')
                    count += 1
    return count


def check(certificate, data=None):
    expressions, contract = checked()
    require(certificate['schema'] == 1 and certificate['source'] == contract and certificate['expressions'] == expressions, 'Source contract mismatch')
    arithmetic = certificate['arithmetic']
    u, eta = Rational(arithmetic['unitRoundoff']), Rational(arithmetic['underflowAllowance'])
    require(u == Rational(1, 2**53) and eta == Rational(1, 2**100), 'Rounding model changed')
    require(Rational(arithmetic['exactHalfMinimumSubnormal']) == Rational(1, 2**1075) <= eta, 'Underflow allowance unsound')
    require(Rational(arithmetic['overflowGuard']) == 2**1023, 'Overflow threshold changed')
    nodes, polynomials = certificate['nodes'], {}
    require(len(nodes) < 10000, 'Unbounded certificate graph')
    for index, node in enumerate(nodes):
        op, args = node['op'], node['args']
        require(all(type(arg) is int and 0 <= arg < index for arg in args), 'Graph must be topologically sorted')
        m, e = Rational(node['magnitude']), Rational(node['error'])
        require(m >= 0 and e >= 0, 'Negative magnitude or error')
        exact_poly = None
        if op == 'literal':
            require(not args and node['value'] in (0, 1, 2, 4) and type(node['value']) is int, 'Invalid literal')
            require(e == 0 and m == abs(node['value']), 'Literal is not exact')
            exact_poly = coefficients([node['value']])
        elif op == 'input-x':
            require(not args and e == 0 and m == 1, 'Input domain changed')
            exact_poly = {1: 1}
        elif op == 'coefficient':
            profile = next(p for p in certificate['data']['profiles'] if p['name'] == node['profile'])
            require(not args and e == 0 and 0 <= node['degree'] < profile['ncf'] and m == Rational(profile['bounds'][node['degree']]), 'Coefficient input mismatch')
        elif op == 'exact-scale':
            require(not args and node['na'] in (1, 2, 4, 8) and node['step'] == 32 and e == 0 and m == Rational(node['na'], 16), 'Nonexact or unsupported derivative scaling')
        else:
            require(op in ('add', 'sub', 'mul') and len(args) == 2, 'Unsupported arithmetic operation')
            left, right = (nodes[arg] for arg in args)
            ma, mb, ea, eb = (Rational(left['magnitude']), Rational(right['magnitude']), Rational(left['error']), Rational(right['error']))
            if op in ('add', 'sub'):
                magnitude, propagation = ma + mb, ea + eb
            else:
                magnitude, propagation = ma * mb, ma * eb + mb * ea + ea * eb
            if args[0] in polynomials and args[1] in polynomials:
                exact_poly = combine(op, polynomials[args[0]], polynomials[args[1]])
                magnitude = sum(abs(x) for x in exact_poly.values())
            require(m == magnitude, 'Exact magnitude certificate mismatch at ' + str(index))
            require(e >= propagation + u * (m + propagation) + eta, 'Rounding error bound too small at ' + str(index))
            require(m + propagation < 2**1023, 'Intermediate may overflow')
        if exact_poly is None:
            require('polynomial' not in node, 'Spurious exact polynomial')
        else:
            require(coefficients(node['polynomial']) == exact_poly, 'Polynomial certificate mismatch at ' + str(index))
            polynomials[index] = exact_poly
        require(m + e < 2**1023, 'Rounded result may overflow')

    p, d, a = (certificate['basis'][kind] for kind in ('position', 'velocity', 'acceleration'))
    require(all(len(series) == 17 for series in (p, d, a)), 'Incomplete generic recurrence range')
    require(polynomials[p[0]] == {0: 1} and polynomials[p[1]] == {1: 1} and polynomials[d[0]] == {} and polynomials[d[1]] == {0: 1} and polynomials[a[0]] == polynomials[a[1]] == {}, 'Incorrect recurrence seeds')
    for n in range(17):
        require(polynomials[d[n]] == derivative(polynomials[p[n]]), 'First derivative identity failed')
        require(polynomials[a[n]] == derivative(polynomials[d[n]]), 'Second derivative identity failed')
        require(sum(polynomials[p[n]].values()) == 1, 'T_n(+1) identity failed')
        require(sum(value * (-1)**degree for degree, value in polynomials[p[n]].items()) == (-1)**n, 'T_n(-1) identity failed')
        require(sum(polynomials[d[n]].values()) == n*n, 'T_n derivative endpoint failed')
        require(sum(polynomials[a[n]].values()) == n*n*(n*n-1)//3, 'T_n second derivative endpoint failed')

    def match(index, tree, bindings):
        if isinstance(tree, str):
            require(index == bindings[tree], 'Source variable binding mismatch')
        elif tree[0] == 'constant':
            require(nodes[index]['op'] == 'literal' and nodes[index]['value'] == tree[1], 'Source literal mismatch')
        else:
            require(nodes[index]['op'] == tree[0] and len(nodes[index]['args']) == 2, 'Source operation order changed')
            match(nodes[index]['args'][0], tree[1], bindings)
            match(nodes[index]['args'][1], tree[2], bindings)
    # twot is shared across every basis recurrence, just as in iinfo.
    twot = nodes[nodes[p[2]]['args'][0]]['args'][0]
    require(nodes[twot]['op'] == 'add' and nodes[twot]['args'] == [p[1], p[1]], 'twot source mismatch')
    for n in range(2, 17):
        match(p[n], expressions['position'], {'twot': twot, 'p1': p[n-1], 'p2': p[n-2]})
        match(d[n], expressions['velocity'], {'twot': twot, 'd1': d[n-1], 'd2': d[n-2], 'p1': p[n-1]})
        match(a[n], expressions['acceleration'], {'twot': twot, 'a1': a[n-1], 'a2': a[n-2], 'd1': d[n-1]})
    outputs = []
    for profile in certificate['data']['profiles']:
        cf = profile['coefficientNodes']
        require(len(cf) == profile['ncf'], 'Coefficient vector length mismatch')
        for degree, index in enumerate(cf):
            require(nodes[index]['op'] == 'coefficient' and nodes[index]['degree'] == degree and nodes[index]['profile'] == profile['name'], 'Coefficient order mismatch')
        for kind, basis, low in [('position', p, 0), ('velocity', d, 1), ('acceleration', a, 0)]:
            output = current = profile['outputs'][kind]
            for _ in range({'position': 0, 'velocity': 1, 'acceleration': 2}[kind]):
                require(nodes[current]['op'] == 'mul', 'Derivative output must be scaled after sum')
                previous, scale = nodes[current]['args']
                require(nodes[scale]['op'] == 'exact-scale' and nodes[scale]['na'] == profile['na'], 'Derivative scale mismatch')
                current = previous
            for degree in range(low, profile['ncf']):
                require(nodes[current]['op'] == 'add', 'Missing source sum operation')
                previous, product = nodes[current]['args']
                require(nodes[product]['op'] == 'mul' and nodes[product]['args'] == [basis[degree], cf[degree]], 'Coefficient sum order or range changed')
                current = previous
            require(nodes[current]['op'] == 'literal' and nodes[current]['value'] == 0, 'Source sum must start at zero')
            error = Rational(nodes[output]['error'])
            with localcontext() as context:
                context.prec = 12
                context.rounding = ROUND_CEILING
                decimal_upper = str(Decimal(error.numerator) / Decimal(error.denominator))
            outputs.append({'profile': profile['name'], 'quantity': kind, 'errorExact': str(error), 'errorDecimalUpper': decimal_upper,
                'units': ('radian' if profile['name'] in ('nutations', 'librations') else 'km') + {'position': '', 'velocity': '/day', 'acceleration': '/day^2'}[kind]})
    checked_coefficients = check_data(certificate, data) if data is not None else None
    return {'schema': 1, 'nodesChecked': len(nodes), 'polynomialIdentitiesChecked': 17 * 6, 'coefficientsChecked': checked_coefficients,
      'outputs': outputs, 'scope': certificate['scope'], 'checker': 'Independent Python exact-rational checker; see Lean export for kernel arithmetic checks',
      'trustedBase': ['Python interpreter/arbitrary-precision integer and Fraction implementation', 'Source extractor, hash contract, and restricted arithmetic parser',
        'IEEE binary64 nearest-even rounding error theorem and gradual underflow (explicit real-rounding premise in Lean)',
        'Standalone Python arithmetic claims are independently strengthened by Lean polynomial/L1 proofs and the instantiated rounded DAG',
        'Correct source-to-compiler correspondence, caller preconditions, successful I/O, and runtime implementation are separate obligations']}


if __name__ == '__main__':
    certificate = json.loads((HERE / 'evidence/certificate.json').read_text())
    result = check(certificate, (ROOT / '.cache/linux_p1550p2650.440').read_bytes())
    (HERE / 'evidence/checked.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Checked', result['nodesChecked'], 'nodes and', result['coefficientsChecked'], 'stored coefficients')
    for row in result['outputs']:
        print(row['profile'], row['quantity'], '<=', row['errorDecimalUpper'], row['units'])
