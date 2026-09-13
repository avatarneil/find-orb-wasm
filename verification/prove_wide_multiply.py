#!/usr/bin/env python3
"""GPL-2.0-or-later. Exact proof of the experimental binary128 integer helper.

This proves the source-anchored base-2^32 algorithm, not the whole compiler or
all IEEE arithmetic. The C-to-integer-model correspondence is manually reviewed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

import z3
from common import ROOT


CONTRACT = json.loads((ROOT / "verification/wide-multiply-contract.json").read_text())
SOURCE = CONTRACT["path"]
SHA256 = CONTRACT["sha256"]
B = 2**32


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / SOURCE)
    parser.add_argument("--output", type=Path, default=ROOT / "results/local/wide-multiply-proofs.json")
    args = parser.parse_args()
    digest = hashlib.sha256(args.source.read_bytes()).hexdigest()
    if digest != SHA256:
        raise ValueError("Wide-multiply source changed; review the model before updating its contract")
    results = []
    obligation_dir = args.output.parent / "wide-multiply-obligations"
    obligation_dir.mkdir(parents=True, exist_ok=True)

    def prove(name, assumptions, conclusion):
        solver = z3.Solver()
        solver.set(timeout=30000)
        solver.add(*assumptions, z3.Not(conclusion))
        (obligation_dir / (name + ".smt2")).write_text(solver.to_smt2())
        start = time.monotonic()
        result = solver.check()
        results.append({"name": name, "result": str(result), "seconds": time.monotonic() - start})
        print(f"{name}: {result}", flush=True)
        if result != z3.unsat:
            raise AssertionError(f"{name}: {solver.model() if result == z3.sat else solver.reason_unknown()}")

    a, b, old, carry = z3.Ints("a_limb b_limb existing_digit carry")
    limbs = [0 <= value for value in [a, b, old, carry]] + [value < B for value in [a, b, old, carry]]
    value = a * b + old + carry
    prove("limbs.uint64-accumulator-does-not-overflow", limbs,
          z3.And(0 <= value, value <= 2**64 - 1))
    # Includes all sequential partial sums: every addend is nonnegative.
    prove("limbs.partial-sums-do-not-overflow", limbs,
          z3.And(a * b <= value, a * b + old <= value))
    z = z3.Int("accumulator")
    prove("limbs.divmod-preserves-value-and-ranges", [0 <= z, z <= 2**64 - 1],
          z3.And(z % B + B * (z / B) == z, 0 <= z % B, z % B < B,
                 0 <= z / B, z / B < B))
    word = z3.BitVec("uint64_word", 64)
    prove("limbs.cast-and-shift-reconstruct-uint64", [],
          z3.ZeroExt(32, z3.Extract(31, 0, word)) + (z3.LShR(word, 32) << 32) == word)
    integer128 = z3.BitVec("input128", 128)
    extracted = [z3.Extract(i * 32 + 31, i * 32, integer128) for i in range(4)]
    reconstructed = z3.BitVecVal(0, 128)
    for i, digit in enumerate(extracted):
        reconstructed = reconstructed | (z3.ZeroExt(96, digit) << (i * 32))
    prove("limbs.input-slicing-preserves-all-128-bits", [], reconstructed == integer128)

    # Execute the exact source's constant 4x4 write schedule. Introduce each
    # quotient as a fresh integer. The new digit is value-B*quotient, which
    # the independently proved divmod obligation equates to the uint32 cast.
    # Proving the weighted invariant for arbitrary quotient choices is stronger
    # than requiring this one legal quotient; legal ranges come from divmod.
    av = [z3.Int(f"a{i}") for i in range(4)]
    bv = [z3.Int(f"b{i}") for i in range(4)]
    out = [z3.IntVal(0) for _ in range(8)]
    full_b = sum(bv[j] * B**j for j in range(4))
    for i in range(4):
        row_carry = z3.IntVal(0)
        for j in range(4):
            k = i + j
            update = av[i] * bv[j] + out[k] + row_carry
            row_carry = z3.Int(f"quotient_{i}_{j}")
            out[k] = update - B * row_carry
        prove(f"limbs.row-{i}-carry-destination-is-zero", [], out[i + 4] == 0)
        out[i + 4] = row_carry
        weighted = sum(out[k] * B**k for k in range(8))
        partial_a = sum(av[h] * B**h for h in range(i + 1))
        prove(f"limbs.row-{i}-weighted-product-invariant", [],
              weighted == partial_a * full_b)
    full_a = sum(av[i] * B**i for i in range(4))
    low = sum(out[i] * B**i for i in range(4))
    high = sum(out[i + 4] * B**i for i in range(4))
    prove("limbs.complete-128-by-128-product", [],
          low + B**4 * high == full_a * full_b)
    # Output shifts are performed after conversion to 128 bits. Bitwise OR
    # occupies disjoint 32-bit fields, giving exactly the intended limb order.
    digits = [z3.BitVec(f"output{i}", 32) for i in range(8)]
    def assemble(items):
        result = z3.BitVecVal(0, 128)
        for i, digit in enumerate(items):
            result = result | (z3.ZeroExt(96, digit) << (32 * i))
        return result
    prove("limbs.output-assembly-preserves-all-256-bits", [],
          z3.Concat(assemble(digits[4:]), assemble(digits[:4])) == z3.Concat(*reversed(digits)))
    i, j = z3.Ints("row column")
    prove("limbs.all-array-accesses-in-bounds", [0 <= i, i < 4, 0 <= j, j < 4],
          z3.And(0 <= i + j, i + j < 8, 0 <= i + 4, i + 4 < 8))
    left, right = z3.Ints("unsigned128_a unsigned128_b")
    prove("limbs.product-fits-256-bits", [0 <= left, left < 2**128, 0 <= right, right < 2**128],
          z3.And(0 <= left * right, left * right < 2**256))

    # Special path: move a low-64-zero operand to b, multiply a by b/2^64
    # using four-by-two limbs, then shift the exact 192-bit product by 64.
    # The source's initial swap leaves the full product unchanged.
    prove("special.swap-preserves-product", [], left * right == right * left)
    narrowed = z3.Extract(63, 0, integer128)
    prove("special.zero-low64-implies-exact-factorization", [narrowed == 0],
          integer128 == (z3.ZeroExt(64, z3.Extract(127, 64, integer128)) << 64))
    short_b = bv[0] + B * bv[1]
    out = [z3.IntVal(0) for _ in range(6)]
    for i in range(4):
        row_carry = z3.IntVal(0)
        for j in range(2):
            k = i + j
            update = av[i] * bv[j] + out[k] + row_carry
            row_carry = z3.Int(f"short_quotient_{i}_{j}")
            out[k] = update - B * row_carry
        prove(f"special.row-{i}-carry-destination-is-zero", [], out[i + 2] == 0)
        out[i + 2] = row_carry
        weighted = sum(out[k] * B**k for k in range(6))
        partial_a = sum(av[h] * B**h for h in range(i + 1))
        prove(f"special.row-{i}-weighted-product-invariant", [], weighted == partial_a * short_b)
    low = out[0] * B**2 + out[1] * B**3
    high = sum(out[i + 2] * B**i for i in range(4))
    prove("special.complete-product-after-exact-64bit-shift", [],
          low + B**4 * high == full_a * (short_b * B**2))
    zero32 = z3.BitVecVal(0, 32)
    prove("special.shifted-output-assembly-preserves-all-bits", [],
          z3.Concat(assemble(digits[2:6]), assemble([zero32, zero32, *digits[:2]]))
          == z3.Concat(*reversed(digits[:6]), z3.BitVecVal(0, 64)))
    i, j = z3.Ints("special_row special_column")
    prove("special.all-array-accesses-in-bounds", [0 <= i, i < 4, 0 <= j, j < 2],
          z3.And(0 <= i + j, i + j < 6, 0 <= i + 2, i + 2 < 6))
    prove("special.intermediate-product-fits-192-bits",
          [0 <= left, left < 2**128, 0 <= right, right < 2**64],
          z3.And(0 <= left * right, left * right < 2**192))

    report = {"schema": 1, "solver": z3.get_version_string(),
              "source": {"path": SOURCE, "sha256": digest}, "obligations": results,
              "claim": "Exact 128x128 -> 256 unsigned integer product for every input pair, including swapped low64-zero specialization and generic path, with uint64 accumulator bounds, correct carries, limb extraction/assembly, and array indices; conditional on manually reviewed source-to-model correspondence.",
              "composition": "Substitution into otherwise unchanged compiler-rt fp_mul_impl.inc preserves the productHi/productLo bits consumed by normalization and IEEE binary128 rounding. Independent binary128 implementation correctness and compiler translation are not proved.",
              "preconditions": "rep_t is unsigned 128 bits; uint32_t/uint64_t have the named widths; hi and lo point to distinct writable rep_t objects; standard unsigned shifts/casts and no compiler miscompilation.",
              "trustedBase": "Z3, Python, source hash, source-to-model mapping, standard unsigned C arithmetic; no independent proof kernel certificate check."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {len(results)} exact-multiplication obligations; report: {args.output}")


if __name__ == "__main__":
    main()
