#!/usr/bin/env python3
"""GPL-2.0-or-later. Source-anchored SMT obligations, not whole-program proof.

The lower-bound search transition is manually encoded and guarded by an exact
function hash. Vector expressions are parsed directly from pinned C++ source.
"""
from __future__ import annotations

import argparse
import ast
import json
import re
import time
from pathlib import Path

import z3
from common import ROOT, checked_sources


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, default=ROOT / ".wasm-engine/sources")
    parser.add_argument("--output", type=Path, default=ROOT / "results/local/proofs.json")
    args = parser.parse_args()
    functions, contracts = checked_sources(args.sources)
    results = []

    def prove(name, assumptions, conclusion):
        solver = z3.Solver()
        solver.set(timeout=30000)
        solver.add(*assumptions, z3.Not(conclusion))
        obligation_dir = args.output.parent / "proof-obligations"
        obligation_dir.mkdir(parents=True, exist_ok=True)
        (obligation_dir / (name + ".smt2")).write_text(solver.to_smt2())
        start = time.monotonic()
        result = solver.check()
        record = {"name": name, "result": str(result), "seconds": time.monotonic() - start}
        results.append(record)
        print(f"{name}: {result}", flush=True)
        if result != z3.unsat:
            detail = solver.model() if result == z3.sat else solver.reason_unknown()
            raise AssertionError(f"{name}: {result}: {detail}")

    # A monotone comparator is represented exactly by [L,U), the equal range.
    # L==U means no equal key. Any sorted array with a deterministic consistent
    # comparator maps to these thresholds, independently of record values.
    N, L, U, lo, n = z3.Ints("N L U lo n")
    found = z3.Bool("found")
    domain = [0 <= N, N <= 2**32 - 1, 0 <= L, L <= U, U <= N]

    def invariant(base, count, seen):
        return z3.And(0 <= base, 0 <= count, base + count <= N,
                      base <= L, L <= base + count,
                      z3.Implies(seen, L < U),
                      z3.Or(seen, L == U, L < base + count))

    prove("search.initial-invariant", domain, invariant(0, N, z3.BoolVal(False)))
    mid = lo + n / 2
    active = domain + [invariant(lo, n, found), n > 0]
    prove("search.read-in-bounds", active, z3.And(lo <= mid, mid < lo + n, mid < N))
    branches = [
        ("right", mid < L, mid + 1, (n - 1) / 2, found),
        ("equal", z3.And(L <= mid, mid < U), lo, n / 2, z3.BoolVal(True)),
        ("left", U <= mid, lo, n / 2, found),
    ]
    for name, condition, next_lo, next_n, next_found in branches:
        assume = active + [condition]
        prove(f"search.{name}-preserves-invariant", assume,
              invariant(next_lo, next_n, next_found))
        prove(f"search.{name}-strictly-decreases", assume,
              z3.And(0 <= next_n, next_n < n, next_n <= n / 2))
    prove("search.terminal-is-first-match-or-insertion", domain + [invariant(lo, n, found), n == 0],
          z3.And(lo == L, found == (L < U)))
    # Every branch at least halves count. Unsigned wasm32 count therefore has
    # a 32-iteration upper bound (including N=UINT32_MAX).
    bound = N
    for _ in range(32):
        bound = bound / 2
    prove("search.wasm32-termination-bound", domain, bound == 0)
    size, address, index = z3.Ints("element_size base_address index")
    memory = 536870912  # Build's maximum linear memory; includes one-past result.
    layout = domain + [size > 0, address >= 0, address + N * size <= memory,
                       0 <= index, index <= N]
    prove("search.byte-offset-and-address-fit-wasm32", layout,
          z3.And(index * size <= 2**32 - 1, address + index * size <= memory))

    # jpl_state maps epoch to a record and interpolation fraction. On the
    # pinned DE440 interval, binary64 JDs lie on a 2^-31-day grid and its
    # 32-day records have Q=2^36 ticks. Differences occupy <53 significant
    # bits and division by 32 is exact. This integer-grid correspondence is
    # a reviewed mathematical assumption, not a compiler translation proof.
    # Complete coefficient records are copied separately by data/compact.mjs.
    ticks, first, count, full_count = z3.Ints("ticks first count full_count")
    Q = 2**36
    crop_domain = [0 <= first, 0 < count, first + count <= full_count,
                   full_count < 2**14, first * Q < ticks,
                   ticks <= (first + count) * Q]
    old_q, old_r = ticks / Q, ticks % Q
    new_ticks = ticks - first * Q
    new_q, new_r = new_ticks / Q, new_ticks % Q
    old_boundary = z3.And(old_r == 0, old_q > 0)
    new_boundary = z3.And(new_r == 0, new_q > 0)
    old_record = old_q - z3.If(old_boundary, 1, 0)
    new_record = new_q - z3.If(new_boundary, 1, 0)
    old_fraction = z3.If(old_boundary, Q, old_r)
    new_fraction = z3.If(new_boundary, Q, new_r)
    prove("de440.crop-selects-identical-record", crop_domain,
          old_record == first + new_record)
    prove("de440.crop-identical-interpolation-coordinate", crop_domain,
          old_fraction == new_fraction)
    prove("de440.crop-read-in-bounds", crop_domain,
          z3.And(0 <= new_record, new_record < count))
    prove("de440.tick-differences-fit-binary64-significand", crop_domain,
          z3.And(0 < ticks, ticks < 2**53, 0 < new_ticks, new_ticks < 2**53))
    prove("de440.lower-endpoint-record-mismatch", [first > 0, ticks == first * Q],
          old_record != first + new_record)

    # Parse a deliberately tiny C expression subset; unsupported syntax fails.
    a = [z3.Real(f"a{i}") for i in range(3)]
    b = [z3.Real(f"b{i}") for i in range(3)]
    def expression(source, arrays):
        def visit(node):
            if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
                position = node.slice.value
                if not isinstance(position, int) or not 0 <= position < 3:
                    raise ValueError("Unsupported array index")
                return arrays[node.value.id][position]
            if isinstance(node, ast.BinOp):
                left, right = visit(node.left), visit(node.right)
                if isinstance(node.op, ast.Add): return left + right
                if isinstance(node.op, ast.Sub): return left - right
                if isinstance(node.op, ast.Mult): return left * right
            raise ValueError(f"Unsupported C-expression subset: {ast.dump(node)}")
        return visit(ast.parse(source.strip(), mode="eval").body)

    dot_expression = re.fullmatch(r".*?\{\s*return\(\s*(.*?)\);\s*\}",
                                  functions["dot_product"], re.S).group(1)
    cross_body = functions["vector_cross_product"].split("{", 1)[1].rsplit("}", 1)[0]
    statements = [s.strip() for s in cross_body.split(";") if s.strip()]
    if len(statements) != 3:
        raise ValueError("Cross product implementation changed")
    cross = []
    for i, statement in enumerate(statements):
        lhs, rhs = statement.split("=", 1)
        if lhs.strip() != f"xprod[{i}]":
            raise ValueError("Cross product storage order changed")
        cross.append(expression(rhs, {"a": a, "b": b}))
    dot = lambda x, y: expression(dot_expression, {"a": x, "b": y})
    prove("real-vector.dot-symmetry", [], dot(a, b) == dot(b, a))
    prove("real-vector.cross-orthogonal-to-a", [], dot(cross, a) == 0)
    prove("real-vector.cross-orthogonal-to-b", [], dot(cross, b) == 0)
    prove("real-vector.lagrange-identity", [],
          dot(cross, cross) == dot(a, a) * dot(b, b) - dot(a, b) * dot(a, b))
    prove("real-vector.squared-length-nonnegative", [], dot(a, a) >= 0)

    # Concrete IEEE binary64 witnesses formalize why algebraically valid
    # rewrites are not automatically valid accuracy-preserving optimizations.
    rm, fp = z3.RNE(), z3.Float64()
    x, y, z = (z3.FPVal(v, fp) for v in ["10000000000000000", "-10000000000000000", "1"])
    lhs = z3.fpAdd(rm, z3.fpAdd(rm, x, y), z)
    rhs = z3.fpAdd(rm, x, z3.fpAdd(rm, y, z))
    prove("binary64.reassociation-counterexample", [], z3.Not(z3.fpEQ(lhs, rhs)))
    # (1+2^-27)*(1-2^-27)-1 rounds to zero when split, but FMA is -2^-54.
    x, y, z = (z3.FPVal(v, fp) for v in [1 + 2**-27, 1 - 2**-27, -1])
    split = z3.fpAdd(rm, z3.fpMul(rm, x, y), z)
    fused = z3.fpFMA(rm, x, y, z)
    prove("binary64.contraction-counterexample", [], z3.Not(z3.fpEQ(split, fused)))

    report = {"schema": 1, "solver": z3.get_version_string(), "obligations": results,
              "sourceContracts": contracts, "scope": {
                  "search": "Inductive proof for all wasm32 counts, sorted records, consistent comparator, valid nonwrapping allocation; source-to-model transition manually reviewed and hash guarded.",
                  "vectors": "Identities over exact real arithmetic, expressions parsed from actual sources; separate input/output arrays.",
                  "ephemeris": "Source-anchored manual model of jpl_state record/fraction selection for exact DE440 binary64 grid, complete 32-day records, exclusive lower endpoint. Does not prove file copying or Chebyshev evaluation.",
                  "floatingPoint": "Concrete IEEE binary64 counterexamples; no end-to-end floating-point error bound.",
                  "trustedBase": "Z3, Python/source extraction, threshold abstraction, C++ compiler and WebAssembly runtime; no independent proof-certificate checking."}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {len(results)} obligations; report: {args.output}")


if __name__ == "__main__":
    main()
