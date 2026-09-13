"""GPL-2.0-or-later. Source-anchored loop, address, selection and cache VCs.

These SMT-LIB obligations are solver checked, not claimed as Lean theorems.
Recurrence algebra and numerical certificate inequalities have separate Lean
proofs. Invariant-to-C++ control-flow correspondence is explicitly reviewed.
"""
import json
import z3
from source import HERE, checked


def run():
    checked()
    folder = HERE / 'evidence/control-obligations'
    folder.mkdir(parents=True, exist_ok=True)
    results = []
    def prove(name, assumptions, claim):
        solver = z3.Solver()
        solver.set(timeout=10000)
        solver.add(*assumptions, z3.Not(claim))
        (folder / (name + '.smt2')).write_text(solver.to_smt2())
        result = solver.check()
        if result != z3.unsat:
            raise ValueError(name + ': ' + str(result) + ' ' + (str(solver.model()) if result == z3.sat else solver.reason_unknown()))
        results.append({'name': name, 'result': 'unsat'})

    na, ticks = z3.Ints('na ticks')
    q = 2**36  # 32 days at the binary64 JD spacing 2^-31 days.
    valid_time = [z3.Or(na == 1, na == 2, na == 4, na == 8), 0 <= ticks, ticks <= q]
    raw_l = na * ticks / q
    l = z3.If(raw_l == na, raw_l - 1, raw_l)
    numerator = z3.If(raw_l == na, q, 2 * ((na * ticks) % q) - q)
    prove('subinterval.index-in-bounds-including-right-endpoint', valid_time, z3.And(0 <= l, l < na))
    prove('subinterval.tc-in-closed-unit-interval', valid_time, z3.And(-q <= numerator, numerator <= q))
    prove('subinterval.right-endpoint-is-last-record-tc-one', valid_time + [ticks == q], z3.And(l == na - 1, numerator == q))
    prove('subinterval.left-endpoint-is-first-record-tc-minus-one', valid_time + [ticks == 0], z3.And(l == 0, numerator == -q))
    prove('subinterval.all-coordinate-numerators-fit-53-significant-bits', valid_time,
      z3.And(0 <= na*ticks, na*ticks < 2**53, -2**53 < numerator, numerator < 2**53))

    ncf, ncm, sub, component, k, available = z3.Ints('ncf ncm sub component k available')
    domain = [2 <= ncf, ncf < 18, 1 <= ncm, ncm <= 3, 1 <= na, na <= 8, 0 <= sub, sub < na, 0 <= component, component < ncm]
    offset = ncf * (component + sub * ncm)
    prove('coefficient.read-in-bounds', domain + [0 <= k, k < ncf], z3.And(0 <= offset+k, offset+k < ncf*ncm*na))
    prove('coefficient.one-past-pointer-in-bounds', domain, z3.And(0 < offset+ncf, offset+ncf <= ncf*ncm*na))
    prove('position.basis-read-in-bounds', domain + [0 <= k, k < ncf], z3.And(0 <= k, k < 18))
    prove('velocity.omits-zero-derivative-only', domain + [1 <= k, k < ncf], z3.And(1 <= k, k < 18, 0 <= offset+k, offset+k < ncf*ncm*na))
    loop = domain + [2 <= available, available < ncf, available <= k, k < ncf]
    prove('recurrences.all-array-reads-and-writes-in-bounds', loop, z3.And(0 <= k-2, k-1 < 18, k < 18))
    prove('recurrences.counter-decreases-and-stops-at-ncf', loop, z3.And(ncf-(k+1) >= 0, ncf-(k+1) < ncf-k))
    prove('cache.hit-with-larger-prefix-covers-smaller-request', domain + [ncf <= available, available < 18, 0 <= k, k < ncf], k < available)
    prove('outputs.position-velocity-acceleration-in-bounds', domain + [0 <= k, k < 3],
      z3.And(k*ncm+component >= 0, k*ncm+component < 3*ncm))
    other_kind, other_component = z3.Ints('other_kind other_component')
    prove('outputs.position-velocity-acceleration-injective-and-disjoint', domain + [0 <= k, k < 3,
      0 <= other_kind, other_kind < 3, 0 <= other_component, other_component < ncm,
      z3.Or(k != other_kind, component != other_component)],
      k*ncm+component != other_kind*ncm+other_component)
    prove('all-interp-pointer-products-fit-wasm32', domain, z3.And(8*ncf*ncm*na < 2**32, 8*18 < 2**32, 8*3*ncm < 2**32))

    array = z3.Array('cache', z3.IntSort(), z3.RealSort())
    exact = z3.Array('exact', z3.IntSort(), z3.RealSort())
    error = z3.Array('error', z3.IntSort(), z3.RealSort())
    value = z3.Real('computed_value')
    j = z3.Int('j')
    valid_prefix = z3.ForAll(j, z3.Implies(z3.And(0 <= j, j < k), z3.Abs(array[j]-exact[j]) <= error[j]))
    updated = z3.Store(array, k, value)
    prove('cache.extending-prefix-preserves-every-certified-bound', [2 <= k, k < 17, valid_prefix, z3.Abs(value-exact[k]) <= error[k]],
      z3.ForAll(j, z3.Implies(z3.And(0 <= j, j < k+1), z3.Abs(updated[j]-exact[j]) <= error[j])))
    tc = z3.Real('tc')
    reset = z3.Store(array, 1, tc)
    prove('cache.position-reset-restores-exact-two-element-seed', [array[0] == 1, -1 <= tc, tc <= 1], z3.And(reset[0] == 1, reset[1] == tc))
    prove('cache.cold-start-sentinel-always-forces-reset', [-1 <= tc, tc <= 1], tc != -2)

    nr, cached, contents, nrecords = z3.Ints('nr cached contents nrecords')
    io_ok = z3.Bool('io_ok')
    hit = nr == cached
    post_contents = z3.If(hit, contents, nr)
    prove('record-cache.successful-io-or-valid-hit-has-correct-record',
      [0 <= nr, nr < nrecords, z3.Implies(hit, contents == cached), z3.Or(hit, io_ok)], post_contents == nr)
    prove('record-read-address-within-pinned-data', [0 <= nr, nr < 12556], z3.And((nr+2)*8144 >= 16288, (nr+3)*8144 <= 102272352))
    # A real source edge case: curr_cache_loc is changed before a failed read.
    # Ignoring the error and retrying same nr can accept stale buffer contents.
    bad = z3.Solver()
    bad.add(cached == nr, contents != nr, 0 <= nr, nr < 12556)
    if bad.check() != z3.sat:
        raise ValueError('Failed-I/O counterexample disappeared')
    (folder / 'record-cache.failed-io-retry-counterexample.smt2').write_text(bad.to_smt2())
    report = {'schema': 1, 'z3Version': z3.get_version_string(), 'proved': results,
      'counterexample': {'name': 'record-cache.failed-io-retry', 'result': 'sat', 'model': str(bad.model()),
        'mitigation': 'Strict Find_Orb wrapper terminates on any failed JPL evaluation; cache validity is asserted only for successful I/O, never for recovery after ignored read failure.'},
      'scope': 'Integer/real source-anchored loop and cache invariant obligations. Z3/Python are trusted here; dumped SMT-LIB is reproducible but not kernel checked.',
      'coordinateExactness': 'For finite DE440 JDs in [2^21,2^22), the binary64 grid is2^-31 days. Subtraction of .5-aligned endpoints yields <2^53-bit dyadic numerators; division by32, multiplication by1/2/4/8, fractional-part extraction, and2*frac-1 preserve representability. This arithmetic representation argument supplies the integer ticks abstraction.'}
    (HERE / 'evidence/control.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Proved', len(results), 'control obligations and retained the failed-I/O counterexample')
    return report


if __name__ == '__main__':
    run()
