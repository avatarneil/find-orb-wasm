# Verify JPL interpolation

This directory verifies the pinned Find_Orb JPL `interp()` arithmetic with exact rational certificates and Lean proofs. It also checks source-anchored selection, cache, and memory-index obligations with Z3. The arithmetic bounds concern evaluation of the **stored polynomial**, not its agreement with the physical Solar System.

The mathematical result is conditional: for every real rounding function satisfying the stated binary64 error envelope, every `tc` in `[-1, 1]`, and every coefficient vector within the scanned DE440 envelopes, the modeled source-ordered computation satisfies the final per-component error bound. Source-to-model translation, IEEE correspondence, compiled code, and successful I/O remain explicit obligations outside that theorem.

The extended [finite-format proof](../rounding/README.md) now derives that rounding predicate for an explicit nearest-representable binary64 operation. The [production-slice validator](../production/README.md) separately connects all 114 component/quantity expressions to the retained interpolation instructions under explicit entry-state assumptions. These results narrow the model/implementation gap while preserving the remaining interpreter, IEEE implementation, I/O, and numerical-cache boundaries.

## Reproduce

Run from the repository root after the normal engine build has acquired the pinned sources and full DE440 file:

```sh
python3 -m venv .cache/ephemeris-venv
.cache/ephemeris-venv/bin/pip install -r verification/ephemeris/requirements.txt
.cache/ephemeris-venv/bin/python verification/ephemeris/run.py
```

The runner requires Lean 4.24.0 at `.cache/proof-tools/lean-4.24.0-darwin_aarch64`, and mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` at `.cache/mathlib`, with its compiled dependencies available. Use `--lean-root PATH --mathlib PATH` on another platform. The repository's kernel tool bootstrap provides these pinned tools; this runner verifies their versions and does not install global tools. Missing prerequisites fail the run.

Inputs are `.wasm-engine/sources/jpl_eph/{jpleph.cpp,jpl_int.h}` and `.cache/linux_p1550p2650.440`. The full file must have SHA-256 `29915576d0a6555766b99485ac3056ee415e86df4fce282611c31afb329ad062`. Generated `.olean` files stay under `.cache/ephemeris-kernel`; source, certificates, SMT-LIB, theorem dependency audits, and the final report stay here.

The complete output is [evidence/report.json](evidence/report.json). Exact and upward-rounded decimal bounds are in [evidence/checked.json](evidence/checked.json). Individual checks can be run directly:

```sh
python3 verification/ephemeris/check.py
.cache/ephemeris-venv/bin/python verification/ephemeris/control.py
python3 verification/ephemeris/negative.py
```

The central research runner can avoid duplicate Lean compilation:

```sh
.cache/ephemeris-venv/bin/python verification/ephemeris/run.py --certificates-only
python3 verification/kernel/check.py
python3 verification/ephemeris/kernel_negatives.py
```

`--certificates-only` performs the full data/source/rational/SMT/mutation checks and regenerates Lean source, but records `kernel.performed: false` and links the central kernel report. It does not count stale kernel logs as a new pass. The separate mutation runner reuses `.cache/kernel-modules` after the central check; `--modules PATH` supports another checked module directory. It records both arithmetic rejection results in [evidence/kernel-negatives.json](evidence/kernel-negatives.json). The default command still compiles everything and runs these same mutations locally.

Both proof paths check the central Lean/mathlib/dependency pins and use the central clean proof environment. A reported `PANIC`, including one with exit status zero, fails verification. Expected mutation failures must be nonzero and contain the specific mathematical rejection. All entrypoints importing this checker reject Python `-O` and `PYTHONOPTIMIZE`. Run `python3 verification/ephemeris/test_runner.py` for these failure-path controls.

## What is proved

| Layer | Checked result | Boundary |
| --- | --- | --- |
| [Recurrences.lean](Recurrences.lean) | For every natural degree, the implemented velocity recurrence is the polynomial derivative of the position recurrence, and acceleration is the second derivative; differentiation commutes with the coefficient sum. Affine time substitution proves the one/two derivative scale factors. | Exact rational polynomials. |
| [Roundoff.lean](Roundoff.lean) | For every real polynomial coefficient list and `|tc| ≤ 1`, absolute evaluation is bounded by the sum of absolute coefficients. | A universal theorem, including the cancellation-aware polynomial representation used below. |
| [NumericalCertificates.lean](NumericalCertificates.lean) | Every generated polynomial identity, local rational error inequality, and overflow inequality. | Concrete exact arithmetic; no floating-point evaluation occurs in the proof. |
| [BridgeSupport.lean](BridgeSupport.lean), [RoundedDAG.lean](RoundedDAG.lean) | Induction through every exact/rounded DAG node; 39 final position, velocity, and acceleration bounds across all 13 DE440 profiles. | Explicit rounding-function and coefficient-bound premises; does not assert compiled C++ semantics. |
| [check.py](check.py) | Independent sparse polynomial arithmetic, differentiation, endpoint identities, graph topology, descending coefficient order, velocity omission of degree zero, two acceleration scale operations, and exhaustive coefficient envelopes. | Python interpreter, integer arithmetic, parsing, and data interpretation. |
| [control.py](control.py) | 20 selection/index/termination/cache obligations, including disjoint output addresses. | Source-anchored integer/real abstraction checked by Z3, not a Lean theorem. |

Lean runs with `--trust=0`. Every exposed theorem is audited with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` are accepted. Tactics build proof terms rather than supplying unchecked numerical answers. The parent kernel workflow can additionally replay exported terms independently of elaboration.

The coefficient scan covers **12,756,896 stored doubles**, all 12,556 records, all components, and all subintervals. It is exhaustive over this pinned finite dataset, not a sampling experiment. The independent checker compares absolute IEEE bit patterns against each bound; the generator separately computes floating maxima and converts them to exact dyadic rationals.

A compact pack that retains these records and coefficient bytes unchanged satisfies the same envelopes. The pack's byte-preservation and supported-date checks remain separate dataset validation; this runner deliberately checks the full original file.

## Rounding model and supported domain

Each source `+`, `-`, and `*` is a separate rounded node. The velocity source expression retains both additions of the position term; acceleration retains its two left-associated final scale multiplications. Coefficient sums run in descending source order. No reassociation, fused multiply-add, or approximate Chebyshev evaluation is assumed.

For each exact real operation result `z` with `|z| < 2^1023`, the Lean premise is:

```text
|rnd(z) − z| ≤ 2^-53 |z| + 2^-100.
```

Nearest-even binary64 with gradual underflow satisfies the usual relative bound plus half the minimum subnormal, `2^-1075`. The certificate deliberately uses the larger `2^-100` allowance and kernel-checks that comparison. It separately proves the operation arguments stay below the conservative overflow threshold. The connection between this abstract `rnd` and the actual platform instruction remains an IEEE/compiler premise. [Gappa's arithmetic model](https://gappa.gitlabpages.inria.fr/gappa/arithmetic.html) distinguishes rounding from overflow; [Flocq's rounding results](https://flocq.gitlabpages.inria.fr/theos.html) state nearest-rounding error bounds.

The graph covers source basis indices 0–16 (`2 ≤ ncf < 18`). The pinned data uses `ncf` 6–14, subinterval counts 1, 2, 4, or 8, and 32-day records. The final coefficient functions are constrained only at their explicit input nodes; their values elsewhere are irrelevant. Constant derivative scales `2*na/32` are exact dyadic inputs in this domain.

Polynomial magnitudes use the exact monomial coefficient L1 norm. This allows cancellation within a node without assuming that rounded intermediates cancel exactly: propagated input errors and the next rounding error are added separately. For multiplication, propagation is `Ma*Eb + Mb*Ea + Ea*Eb`. For addition/subtraction it is `Ea + Eb`. The instantiated DAG proof combines these formulas, polynomial magnitudes, and local certificates through every predecessor; the final theorem is not merely a collection of independent inequalities.

Representative conservative bounds, per component at `interp()` return:

| Profile | Position | Velocity | Acceleration |
| --- | ---: | ---: | ---: |
| Mercury | 2.50386325081e-8 km | 3.95238039336e-9 km/day | 9.07416535157e-10 km/day² |
| Geocentric Moon | 2.16291773379e-10 km | 9.91303175050e-11 km/day | 5.52956423373e-11 km/day² |
| Pluto | 1.48334653062e-6 km | 1.59911123020e-10 km/day | 4.51673923705e-14 km/day² |

The largest certified Cartesian position bound across all profiles is below **1.484 mm**. This is an arithmetic evaluation bound, not ephemeris model accuracy. Nutation and libration quantities use radians and their time derivatives; all 39 results and exact fractions are in the report.

## Selection, endpoints, and cache

The pinned full DE440 file covers JD 2287184.5 through 2688976.5 in 32-day records. In this JD binade, representable binary64 dates lie on a `2^-31`-day grid. A record has `2^36` ticks. Subtraction of the `.5`-aligned record endpoint, division by 32, multiplication by the supported powers of two, and fractional-coordinate conversion have representable dyadic results. The SMT obligations prove integer numerator/index bounds, including both endpoints and the `l == na` correction to the last subinterval with `tc = 1`.

That representation argument is reviewed correspondence between IEEE values and integer ticks; it is **not** a Lean proof of all date-selection C++ instructions. The dataset's compact-window fail-closed policy and its open left boundary are separate wrapper behavior.

Array obligations require valid buffers, `1 ≤ ncm ≤ 3`, initialized cache state, and the source `ncf` bound. They show coefficient/basis indices and one-past pointers are in range, recurrence counters decrease, output addresses are injective, and prefix extension preserves supplied numerical error bounds. They do not prove arbitrary pointers are valid or that another thread cannot modify cache storage.

The upstream record cache sets `curr_cache_loc` before a potentially failing read. Ignoring a read error and retrying the same record can reuse stale contents. The report preserves a satisfiable counterexample instead of asserting unconditional recovery correctness. This port's strict wrapper terminates on a failed JPL evaluation, so the stated cache invariant assumes successful I/O or a previously valid hit.

## Source anchoring and negative controls

[source-contract.json](source-contract.json) pins complete `interp`, `jpl_state`, and initialization function hashes plus the interpolation header. [source.py](source.py) extracts and parses the three actual arithmetic recurrence expressions, preserving association and rejecting unsupported syntax. It is a deliberately narrow reviewed frontend, not a complete C++ parser. The source loop-to-DAG mapping is checked against frozen source and independently checked graph shape; arbitrary new C++ syntax requires renewed review.

The run rejects twelve deliberate defects: false error/envelope bounds, a wrong derivative polynomial, changed arithmetic, omitted coefficient accumulation, changed time scale, ignored subnormals, an unsupported function call, three actual source mutations, and consistently relabeled body/unit metadata. Two further kernel controls delete an exact derivative term and replace a rounded multiplication with addition while retaining the claimed bound. Each must fail for the expected verification reason.

## Limits and provenance

Bounds stop **before km-to-AU conversion, barycentric/heliocentric subtraction, Earth/Moon combinations, and target-center combinations**. They exclude coefficient generation, JPL model/fit error, astronomical time-scale conversion, forces, orbit integration, orbit fitting, optimizer convergence, observation uncertainty, and application output formatting. They do not establish whole-program memory safety or a verified C++ compiler.

The source is [Bill Gray's `jpl_eph`, pinned at a73f25e](https://github.com/Bill-Gray/jpl_eph/blob/a73f25e54d02b99b1c0d9a9d6c61acfbb2fa3a26/jpleph.cpp), under its existing GPL-2.0-or-later license. This verification code is GPL-2.0-or-later. Data provenance is [JPL's planetary ephemeris export documentation](https://ssd.jpl.nasa.gov/planets/eph_export.html). The derivative and recurrence interpretation is consistent with [NIST DLMF 18.9.E21](https://dlmf.nist.gov/18.9.E21) and [the recurrence table](https://dlmf.nist.gov/18.9.T1). [Gappa's proof-producing workflow](https://gappa.gitlabpages.inria.fr/gappa/invoking.html) informed the certificate design; this implementation uses Lean instead of claiming an unproduced Gappa/Coq proof.
