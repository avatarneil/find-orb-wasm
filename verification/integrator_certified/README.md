# Connected linear-ODE integrator proof

This suite proves a one-step error bound for a source-pinned Runge–Kutta arithmetic graph with the **actual stored coefficients**, instantiated with the explicitly defined finite binary128 nearest-rounding model. It strengthens the earlier Python-only linear-ODE envelope. It does not prove the astronomical force model, the complete compiled integrator, or adaptive tolerance selection.

The test problem is `y′ = y`, with exact solution `y0 * exp(t)`. Lean proves the derivative and initial value, connects every stage operation to its exact polynomial, propagates rounding through the same operation graph, and bounds the difference from the exponential solution.

| Method | Graph nodes | Proved absolute one-step bound |
|---|---:|---:|
| Active original-coefficient Fehlberg branch | 91 | `1.075e-11` |
| Corrected Prince–Dormand branch | 329 | `2.895e-18` |

The domain is `t0=0`, `abs(h) <= 1/16`, and `abs(y0) <= 1/2`. Source correspondence is restricted to `n_vals=n_orbit_params=6`, valid initialized disjoint buffers, successful allocation, zero reference, and a prescribed RHS that copies the first state coordinate and sets the other derivatives to zero. The theorem bounds the first output coordinate. C++ input values must be exactly representable. Finite numerical equality identifies both zero signs.

## What is connected

`generate.py` reads immutable pinned upstream source and the reviewed corrected variant through the existing strict extractor. It checks whole-file and function hashes and interprets the actual unsuffixed C constant expressions as binary64 before their exact widening to binary128. The source/parser/constant-evaluator correspondence remains trusted; existing compiled probes independently corroborate selected evaluated constants and outputs.

The generated graph retains each sequential multiply and accumulation, the step multiplication, the state addition, and the zero-reference additions/subtractions. Even operations that are IEEE identities on representable inputs remain in the graph. Subtracting real zero is expressed as adding real zero; sign-of-zero effects are outside its numerical specification. The autonomous RHS does not depend on stage times.

Every exact node has a polynomial identity and magnitude bound. Every rounded node has a composed error theorem using its predecessor errors. The proof checks that each arithmetic input has magnitude below 100. Polynomial magnitudes use exact rational coefficients and outward-rounded rational bounds; cancellation never substitutes for accumulated floating-point error.

The final stored stability polynomial is compared with the exponential series through degree 15. Mathlib's universal exponential remainder bound controls the remaining tail for both positive and negative steps. This proves the difference from the exact ODE solution, including stored-coefficient differences and arithmetic errors. It does not identify rounded coefficients with the ideal order conditions. `CanonicalLinear.lean` instantiates the complete graph with `FindOrbRounding.roundBinary128` using a proved finite-format rounding bound, so its final theorems do not assume an arithmetic-error envelope.

The concrete rounding function is a mathematical finite-format nearest selection. Relating actual compiler/runtime operations to that selection or to the general rounding predicate is a separate boundary. The conditional graph theorem also applies to any rounding function satisfying the proved numerical envelope; the canonical instance does not by itself prove compiler preservation.

## Repeated steps

The connected multiple-step theorem compares the repeated mathematical graph with `y0 * exp(sum of steps)`. Its error satisfies the existing explicit `errorBudget` recurrence with multiplier `16/15` and the method's local bound. The exponential stability factor is proved. The theorem assumes every numerical input remains in `[-1/2,1/2]`, every step remains in `[-1/16,1/16]`, and the stated recurrence is followed. It does not prove that an adaptive controller enforces these invariants, or that all repeated C++ calls satisfy their time/assertion/buffer preconditions.

## Reproduce

Use the pinned research environment and Lean/mathlib setup in the top-level README. The additional cached Mathlib module is `Mathlib.Analysis.SpecialFunctions.ExpDeriv`. The rounding modules must be compiled first; they live under `verification/rounding/`.

```sh
.venv/research/bin/python verification/integrator_certified/generate.py
.venv/research/bin/python verification/integrator_certified/check.py
.venv/research/bin/python verification/integrator_certified/negative.py
```

The checker compiles with trust level zero, audits the theorem roots, replays their dependency closures using the existing empty-kernel checker, and records source hashes. Failed or interrupted reruns leave success invalidated. `--no-replay` and `--support-only` write separate development evidence. The central kernel runner is responsible for verifying the installed Lean release against its pinned archive.

`evidence/certificate.json` records generated bounds and correspondence observations. `evidence/report.json` records the completed Lean run. `evidence/negative.json` records controls. A changed first-stage weight and a zero rounding budget must fail mathematical goals inside Lean. A changed stage time must fail the strict source-function contract; it cannot change this autonomous mathematical RHS, so that control is explicitly a source-integrity check.

The new graph agrees with the earlier independent exact interpreter on 20 signed-step cases, and with four recorded source-extracted WASM O0/O3 observations at `h=1/16`, `y0=1/2`. These observations are finite corroboration, not universal translation validation. General estimator/error-norm arithmetic, physical uncertainty, nonzero references, other dimensions, and nonlinear force evaluations are outside this proof.

All new code is GPL-2.0-or-later. Original solver provenance and notices remain in the top-level distribution. The mathematical exponential theorem is provided by the pinned [Mathlib source](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Analysis/Complex/Exponential.lean); the upstream solver is [Bill Gray's Find_Orb](https://github.com/Bill-Gray/find_orb).
