# Verify finite IEEE rounding

This directory derives the floating-point error envelope from an explicit finite binary format and nearest-value selection. **The error envelope is a proved result, not an input assumption.** It instantiates the earlier ephemeris `RoundingModel` with `roundBinary64`, and supplies a precision-113 model for the integrator proofs.

The result remains a mathematical model of IEEE rounding. Proving that every executed compiler/runtime instruction implements this model is a separate boundary. Direct WebAssembly conformance probes provide additional evidence without claiming to prove that backend.

## Reproduce

After installing the repository's pinned Lean/mathlib tools and compiling the central kernel dependencies, run from the repository root:

```sh
python3 verification/rounding/run.py
```

The runner compiles four Lean modules with `--trust=0`, audits every exposed theorem, rejects five mathematical mutations and three tool-failure mutations, and compares direct WebAssembly arithmetic with an exact rational encoder. It checks the central toolchain/dependency pins, cleans inherited Lean settings, and rejects optimized Python. Output is [evidence/report.json](evidence/report.json).

The central raw-kernel workflow can compile these modules once, then run the remaining controls:

```sh
python3 verification/rounding/run.py --negatives-only --modules .cache/kernel-modules
```

This records `kernel.performed: false` and points to the central raw replay report. Its output is `evidence/central-controls.json`. The default local module directory is `.cache/rounding-modules`; `--lean-root` and `--mathlib` support alternate local tool locations. `BridgeSupport`, `Roundoff`, and `Foundations` must already exist in `.cache/kernel-modules`.

Required mathlib imports, in addition to the existing arithmetic tactics, are `Data.Real.Archimedean`, `Algebra.Order.Floor.Ring`, `Data.Finset.Max`, `Data.Fintype.Prod`, and `Data.Nat.Find`. All use the existing pinned mathlib revision. No global installation or toolchain-lock modification is required.

## What the 32 theorems establish

| Module | Result |
| --- | --- |
| [FiniteFormat.lean](FiniteFormat.lean) | Integer nearest rounding has error at most one half and selects even integers at exact halves. A finite, nonempty encoded format has a nearest value. The defined format rounder chooses an even significand whenever an even nearest candidate exists. Exact representable values round to themselves. Signed zeros have the same real value. |
| [SpacingBound.lean](SpacingBound.lean) | Every nonnegative real in the guarded range has a sufficiently close, valid encoded candidate. The proof handles subnormal spacing, ordinary binades, and significand carry into the next binade. Nearest selection yields the universal error bound, for any precision and positive minimum subnormal spacing. |
| [IEEEBounds.lean](IEEEBounds.lean) | Concrete binary64 and binary128 bounds, including their actual half-minimum-subnormal terms. The binary64 model satisfies the existing ephemeris rounding predicate. Binary128 also satisfies the integrator's conservative precision-113 envelope. |
| [Binary64Bits.lean](Binary64Bits.lean) | The finite format fields encode bijectively into finite binary64 words. Sign, exponent, and fraction extraction round-trip. Significand parity equals the least significant stored bit, connecting the even-significand policy to even bit patterns. |

All exposed theorem dependencies are restricted to `propext`, `Classical.choice`, and `Quot.sound`. Finite nearest selection uses a mathematical choice operator; existence and the nearest/even properties are proved. It does not invoke an executable platform floating-point operation during the proof.

The generic `Encoding f N` has a sign, an exponent in `0 .. N+2`, and an `f`-bit fraction. Exponent zero represents subnormals as `fraction * δ`. Other exponents represent `(2^f + fraction) * δ * 2^(exponent-1)`. Thus `f+1` is the normal significand precision. The format parameters are:

| Format | Fraction bits `f` | Maximum bin index `N` | Minimum positive subnormal `δ` | Proved input guard |
| --- | ---: | ---: | --- | --- |
| binary64 | 52 | 2044 | 2^-1074 | abs(x) < 2^1023 |
| binary128 | 112 | 32764 | 2^-16494 | abs(x) < 2^16383 |

The binary64 bit encoding is `sign*2^63 + exponent*2^52 + fraction`. The codec theorem covers every finite 64-bit word, excluding exponent 2047. It preserves both signed-zero encodings while their interpreted real values agree. The binary128 result instantiates the same finite field model; this directory does not supply a separate packed 128-bit codec theorem.

## Why the error bound follows

The proof chooses the smallest bin index `n` for which `a < 2^(f+1) * δ * 2^n`, where `a = |x|`. A candidate rounds `a/(δ*2^n)` to a nearest-even integer. That integer is bounded so it can be encoded, including the upper carry case.

Within a bin, the error is at most half its spacing, `δ*2^n/2`. In the first bin this is `δ/2`. In later bins, minimality implies `2^f*δ*2^n ≤ a`, so half-spacing is at most `a/2^(f+1)`. The nearest representable value cannot be farther away than this explicit candidate. No assumption about a pre-existing floating-point error bound enters this argument.

Consequently:

```text
|roundBinary64(x) − x|  ≤ 2^-53  |x| + 2^-1075
|roundBinary128(x) − x| ≤ 2^-113 |x| + 2^-16495
```

The proof then enlarges the subnormal allowances to `2^-100` and `2^-200`, respectively. These inequalities are also kernel-checked; the enlargement simplifies later exact-rational arithmetic without ignoring subnormals.

`FindOrbRounding.binary64_roundingModel` has type `FindOrbEphemerisBridge.RoundingModel FindOrbRounding.roundBinary64`. `binary128_bounded_error x hx` gives the precision-113 plus `2^-200` bound when `hx : |x| < 100`. `any_nearest_error` applies the same result to any encoded nearest value, regardless of the tie choice.

## Negative controls and backend evidence

Five source mutations must fail for their expected mathematical reason: prefer odd midpoint integers, drop the binade carry, move the exponent field by one bit, halve the claimed relative error, and delete the subnormal allowance. PANIC with exit zero, a logged error with exit zero, and an admitted-proof marker are rejected separately. Neither a timeout nor an unrelated tool failure counts as a successful negative control.

[conformance.py](conformance.py) uses exact rational decoding and nearest-even quantization. [wasm_probe.mjs](wasm_probe.mjs) executes a tiny explicit WebAssembly module containing primitive `f64.add`, `f64.sub`, `f64.mul`, and `f64.div`. The checked run matched **10,868 results**, including **504 midpoint cases**, **1,196 subnormal exact results**, and **1,532 results rounded onto nonzero binade boundaries**. Signed zeros are compared through the proved real-value quotient. These finite tests establish conformance for those cases on the recorded Node/V8 version; they are not the universal theorem.

## Limits, sources, and license

The mathematical operators minimize distance within the finite format. Outside the stated guard they are not claimed to implement IEEE overflow to infinity. NaNs, infinities, signaling behavior, exception flags, signed-zero propagation rules, transcendental functions, decimal parsing, FMA contraction, and compiler reassociation are not covered. The guarded arithmetic error theorem does not require any claims about those cases.

The remaining backend assumption is semantic: an executed instruction returns the nearest encoded value with the prescribed tie rule. This is a format-and-operation implementation obligation rather than an assumed numerical error estimate. The bit codec and direct runtime probes narrow that boundary but do not eliminate it.

The [WebAssembly core specification](https://www.w3.org/TR/wasm-core/#floating-point-operations) specifies nearest-even arithmetic and the [binary floating-point value format](https://www.w3.org/TR/wasm-core/#floating-point). The proof uses mathlib's [floor properties](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Algebra/Order/Floor/Ring.lean) and [finite minimum-image theorem](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Data/Finset/Max.lean). It defines its own nearest-even integer operation; mathlib's differently rounded `round` function is not treated as ties-to-even.

This verification code is GPL-2.0-or-later, matching the port. Lean/mathlib retain their upstream licenses as tooling dependencies.
