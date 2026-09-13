# Integrator verification

This directory analyzes the **actual active Find_Orb integration kernels** at upstream commit `9cc932997837c5ab994fbf015db59f5d0da852e5`. It found and reproduced a substantial stage-time indexing defect and a memory leak in `take_pd89_step`; the reviewed port fixes both. It also separates exact mathematical order, stored-coefficient defects, arithmetic roundoff, and the limits of embedded error estimates.

## Reproduce

From the repository root after fetching the pinned sources and SDK:

```sh
.venv/verification/bin/python verification/integrator/analyze.py
.venv/verification/bin/python verification/integrator/compiled.py
```

The analyzer requires only Python's standard library. The compiled probe also requires Clang, Node, and the local Emscripten SDK. Both commands accept `--sources` and `--output`; the compiled probe accepts `--sdk`. Python assertions are required: the shared import rejects `-O`, `-OO`, and nonzero `PYTHONOPTIMIZE`; the compiled driver tests the `-O` and `PYTHONOPTIMIZE` rejection paths. Generated translation units and executables stay in `.cache/integrator-verification/`. No source or build files are modified. Native binary64, x87 extended, and binary128 `long double` formats are supported; the recorded native run is Apple arm64 binary64, and the WASM run uses binary128. Only little-endian probe serialization is supported.

The evidence files are [analysis.json](evidence/analysis.json) and [compiled.json](evidence/compiled.json). Rational values contain decimal-string `numerator` and `denominator`; `approx` is only a display value. Numerical bounds and counterexamples use the rational fields.

## Source and coefficient contracts

`core.py` checks the Git revision and immutable original `runge.cpp` obtained with `git show`. It accepts only the recorded original or the exact reviewed correction as the current source:

| Variant | Whole-source SHA-256 |
| --- | --- |
| Original | `bdb2104b973a575ccdfbc707232644db7ddca9ddde793c780ffc3ea3881bbb2c` |
| Corrected | `112613edaf6ca9e84da2a95c29e2674d83d386f42bb5be0ba9edd03987d64d58` |

The source defines `ORIGINAL_FEHLBERG_CONSTANTS`, so its active six-stage method is the rational Fehlberg branch despite a neighboring comment discussing Cash–Karp. Extraction follows the active preprocessor branch and the actual `bvals`, `avals`, and error-coefficient initializers. Matrix `A` is obtained from the triangular packed array, `b` from its final output row, and `c` from the derivative-stage times. The final reference-state evaluation time is recorded separately.

Every relevant floating literal is unsuffixed. C++ therefore types it as `double`, and these expressions are evaluated in binary64 before exact widening to WASM binary128 `long double`. The extractor preserves textual macro expansion and C integer-versus-floating division, and uses exact rational round-to-nearest, ties-to-even for literals and arithmetic. It does not silently parse coefficients through host floats. The C++ literal typing rule is specified in [working draft N4861, lex.fcon](https://timsong-cpp.github.io/cppwp/n4861/lex.fcon).

Two semantics are reported separately: exact rational interpretation of the written decimal literals, and actual stored binary64 constant expressions. For PD, even the long decimal strings are rounded approximations to the published method. Neither those decimals nor later binary64 values are treated as exact high-order coefficients. PD's stored error coefficients also differ from the exact differences of stored output weights at two entries because subtraction is evaluated in binary64.

## Rooted-tree order conditions

The analyzer enumerates unordered rooted trees recursively. Counts for orders 1–9 are `1,1,2,4,9,20,48,115,286`. For a leaf, the stage elementary weight is the all-ones vector. For a tree with children, it is the componentwise product of `A` applied to each child's weight. The residual is `bᵀΦ(tree) − 1/γ(tree)`, with tree factorial `γ(tree) = order(tree) × product γ(children)`. This is the recursive formulation of [Bornemann's proof of Butcher's theorem](https://arxiv.org/html/math/0211049v1), equations 5, 7, and 8. Nonautonomous applicability additionally needs stage-time consistency `c=A1`; the analyzer checks this separately and computes direct time-polynomial moments.

| Formula | Exact arithmetic conclusion | Largest relevant stored-coefficient residual |
| --- | --- | --- |
| Active Fehlberg advancing weights | All 17 conditions through order 5 vanish exactly; order 6 fails | `6.72e-17` through order 5 |
| Active Fehlberg embedded weights | All 8 conditions through order 4 vanish exactly; order 5 fails | Recorded individually |
| PD advancing decimal weights | Nonzero residuals through order 8, at most `9.60e-29`; order 9 has a residual above `8.30e-6` | `1.63e-15` through order 8 |
| PD embedded decimal weights | Nonzero small residuals through order 7; order 8 has a residual above `1.06e-4` | Recorded individually |

These are exact rational evaluations of every equation, not tolerance-based declarations that a residual is zero. The PD evidence supports the intended **8(7)** identification, but is **not an exact order-8 proof for stored constants**. Netlib's [RKSUITE source](https://www.netlib.org/ode/rksuite/rksuite.f), `CONST` / method 3, attributes the pair to Prince and Dormand, acknowledges their implementation assistance, and records 13 stages with embedded order 7. The associated paper is [Prince and Dormand, “High order embedded Runge–Kutta formulae,” 1981](https://doi.org/10.1016/0771-050X(81)90010-3). Its full text was not available from the publisher during this work; the source, exact residuals, and implementation evidence support the claims made here. A [GSL implementation discussion by Luc Maisonobe](https://ecos.sourceware.org/ml/gsl-discuss/2002-q3/msg00132.html) documents the historical order-9 naming and rounded-coefficient ambiguity.

For the ideal active Fehlberg method, the embedded difference starts at order 5. For PD it has substantial order-8 terms. The port's controller currently allows step doubling only below `0.9*tolerance/2^9`. Under an error model proportional to `h^8`, this is more conservative than the corresponding exponent-8 growth threshold. It was left unchanged: order nomenclature alone does not establish an accuracy bug in that growth decision. Neither model supplies a universal error guarantee, especially near coefficient/roundoff floors or when the controller accepts a forced minimum step.

## Confirmed PD failures and correction

The original PD `avals` starts `{0,A_1,A_2,...}`, although `A_1` is already zero. All later derivative stages therefore use the previous abscissa while the packed stage-state coefficients advance normally. For zero reference, `y'=t`, `t0=y0=0`, and `h=1`, exact evaluation of the stored original tableau produces `0.3286746718087251` instead of `0.5`. Its defect is about `−0.1713253281912749`; this is not floating-point noise. The default integration selector uses Fehlberg, so this defect concerns selection of the PD path.

The correction changes the initializer to `{A_1,A_2,...,A_13,1.}` and frees `ivals[0]` before return. The final `1.` belongs to the output reference evaluation, not another derivative stage. The compiled probe observes one allocation and zero frees per original PD call, versus one allocation and one free after correction. It cleans original leaks outside the tested kernel after recording that evidence, so sanitizer success is not misrepresented as proof that original PD is leak-free.

## Compiled evidence

`compiled.py` compiles both original and corrected function bodies, preserving upstream definitions and the copyright/GPL notice. The C correspondence is scoped to `n_vals=n_orbit_params=6`, initialized valid disjoint input/output buffers, successful allocation, and zero reference. Only external reference and RHS dependencies are replaced with explicit test doubles. It runs native O0, native O3, native ASan/UBSan, WASM O0, and WASM O3 with fast-math and contraction disabled.

Each configuration checks all **169 constant expressions** and **240 step outputs** for exact finite numerical equality against a separate exact-rational interpreter with explicit rounding at each source arithmetic operation. The comparison identifies positive and negative zero, so it does not establish signed-zero preservation. Cases cover `t^k` for `k=0..8`, `y`, `y²`, and the polynomial below; five power-of-two step lengths; both kernels; and both source variants. Native and WASM are compared to their respective precision semantics, rather than pretending their `long double` types agree. Raw output and error-norm bits are retained. The `sqrtl` norm is recorded but not independently proved, except that its exact numerical value must be zero in the `q` counterexample. This is finite compiler validation of extracted kernels, not whole-program equivalence or a compiler proof.

## Embedded estimate cannot universally bound true error

For each actual stored set of stage abscissae, define the smooth polynomial

```text
q(t) = product_i (t - c_i)^2.
```

On `[0,1]`, `0≤q≤1` and `|q'|≤2s`, where `s` is the number of stages. In the scalar ODE `y'=q(t)`, with zero reference, `y(0)=0`, and `h=1`, every sampled derivative vanishes exactly. The actual compiled kernels return state zero and embedded estimate zero. Yet exact rational polynomial integration gives a strictly positive solution:

| Actual stored abscissae | Exact integral, approximate display |
| --- | --- |
| Fehlberg | `3.9358535586244784e-7` |
| Original PD | `3.159207055243313e-11` |
| Corrected PD | `7.217111135707479e-13` |

The roots, complete rational polynomial, and positive rational integral are in `invisibleRhsCounterexamples`. This disproves a universal inequality of true local error bounded by any finite multiple of the embedded estimate, even for smooth bounded RHS functions. It makes no claim that this specially constructed RHS is the astronomical force model.

## Conditional arithmetic and ODE error envelopes

`roundingEnvelopes` gives exact rational certificates from a triangle-inequality/Lipschitz induction following the actual sequential source sums. Its explicit domain is `|h|≤1/16`, `|t0|≤1`, `||y0||∞≤1`, exact RHS norm at most 1, time/state Lipschitz constants at most 1, and RHS evaluation error at most `2^-100`, with zero reference. The bounds compare an actual binary128 step to the corrected exact-decimal/rational tableau, not to the exact ODE solution. All stages must lie in a common domain satisfying those hypotheses. The RHS hypotheses are not proved for Find_Orb's force model.

The resulting implementation-discrepancy bounds are below `2.259e-18` for Fehlberg and `1.620e-17` for corrected PD. Original PD has a much larger bound, approximately `0.003106`, from its incorrect stage times. The arithmetic model uses relative unit roundoff `2^-113` and an absolute `2^-200` slack that dominates half the smallest binary128 subnormal. It assumes finite intermediates, gradual underflow, round-to-nearest, and no contraction/fast-math. The relative-error model and sequential-sum analysis follow the standard approach in [Higham, “The Accuracy of Floating Point Summation,” 1993](https://nhigham.com/wp-content/uploads/2023/10/high93s.pdf); the absolute slack explicitly covers underflow rounding in this analysis.

`linearOdeEnvelopes` additionally bounds one actual step against the **exact ODE solution** for `y'=y`, zero reference, `t0=0`, any exactly represented `|h|≤1/16` and `|y0|≤1/2`. It computes the exact stored-tableau stability polynomial, bounds its exponential Taylor discrepancy, and adds a source-order arithmetic bound. Total bounds are below `1.075e-11` for Fehlberg and `2.895e-18` for PD. Binary128 arithmetic contributions alone are below `7.344e-35` and `2.250e-34`; truncation and stored coefficient perturbations dominate in these particular domains.

These envelopes are exact rational calculations implementing mathematical inductions, with Python, its `Fraction` implementation, and the derivations trusted. Their dimension-independent mathematical form is a conditional abstraction; correspondence to the source is restricted to the six-value, valid-buffer, successful-allocation domain above. General embedded-estimator and error-norm arithmetic remain unverified beyond the tested exact-zero controls. The envelopes are not independently kernel-checked theorems in this directory. They do not cover nonzero Encke reference motion, arbitrary astronomical force derivatives, ephemeris/model uncertainty, global multi-step error, or adaptive-controller completeness. The repository's separate proof-kernel work consumes selected exact certificates; its coverage must be assessed separately.

## Negative checks and limits

The separate [connected linear-ODE development](../integrator_certified/README.md) now kernel-checks the stored-coefficient graph, exponential remainder, local endpoint bound and repeated-graph stability theorem for the prescribed `y'=y` domain. It retains the source's zero-reference operations and instantiates the [proved finite binary128 rounding model](../rounding/README.md). This extends the earlier Python envelope; it still does not prove the complete compiled integrator or astronomical force bounds.

The analyzer rejects altered source hashes, a weight perturbation, a shifted stage time, an altered stage coefficient, treating PD stored error weights as exact subtraction, and an incorrect rounding-tie interpretation. The compiled driver's exact-zero gate rejects the smallest positive binary128 subnormal in either the state or error norm, even though converting that value to a Python display float produces zero. The original PD implementation itself supplies a compiled negative control. Exact rooted-tree enumeration is checked against known counts; all equation residuals remain inspectable.

No result here proves that the complete astronomical orbit fit is correct, that all LLVM transformations preserve it, that the embedded estimate bounds physical uncertainty, or that a successful sanitizer/corpus run establishes universal memory safety. The strongest results are the source-backed exact Fehlberg order conditions, precisely bounded special domains, and reproduced defects/limitations that would have escaped ordinary orbit-output comparisons.

The upstream library is [Bill Gray's Find_Orb](https://github.com/Bill-Gray/find_orb), copyright Project Pluto, GPL-2.0-or-later. Source extractions retain its notice; this verification code uses the repository's same GPL-2.0-or-later license.
