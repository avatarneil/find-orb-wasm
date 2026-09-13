# Proof-kernel validation

This directory contains explicit Lean proof terms and a replay checker for selected mathematical claims. It does not prove the whole C++ program or a compiler correct. See [the research report](../../docs/correctness-research.html) for the claim boundaries.

After the [repository setup](../../README.md), run:

```sh
npm run verify:research
```

This regenerates source/data certificates, runs compiler and integrator checks, compiles the Lean theorems with `--trust=0`, audits their axioms, rechecks their dependency closures in an empty raw kernel environment, and rejects deliberately invalid artifacts. For development, `npm run verify:kernel` only checks existing proof sources; it does not repeat source extraction or the coefficient scan. `check.py --foundations-only` is explicitly a separate smoke check.

## Theorems and their scope

| Proof source | Established statement | Boundary |
|---|---|---|
| `Foundations.lean` | Real addition, subtraction and multiplication error composition; rounding envelopes; an all-step error recurrence and its geometric identity | Rounding, local error and stability assumptions are explicit premises, not established astronomical force bounds |
| `../ephemeris/Recurrences.lean` | For every polynomial degree, the position recurrence differentiates to the velocity recurrence and then acceleration; affine time substitution gives the required scale factors | Exact polynomial model; source correspondence is checked separately |
| `../ephemeris/Roundoff.lean` | Polynomial magnitude bounded by coefficient L1 norm on the unit interval | Real arithmetic |
| `../ephemeris/NumericalCertificates.lean` | Concrete polynomial identities, rational error budgets, and finite-intermediate inequalities for every modeled arithmetic node | These local inequalities alone are not a complete forward-error theorem |
| `../ephemeris/BridgeSupport.lean`, `RoundedDAG.lean` | Those budgets compose through the complete exact/rounded operation graph, giving 39 final output bounds for all 13 DE440 profiles | Explicit rounding-function and coefficient-envelope premises; stops at `interp()` before AU conversion and body combinations |
| `IntegratorCertificates.lean` | Exact ideal Fehlberg tree-stage identities and all 17 advancing/8 embedded order conditions; a real differentiable ODE with zero sampled stages but positive exact solution; a rational PD stage-time defect | The general Butcher theorem, stored-coefficient order, compiled loops, adaptive control, and astronomical force model are not formalized here |
| `../rounding/FiniteFormat.lean`, `SpacingBound.lean`, `IEEEBounds.lean`, `Binary64Bits.lean` | Finite nearest-even selection, subnormal/binade error bounds, binary64 codec, and concrete binary64/binary128 rounding predicates | Guarded finite formats; actual executable IEEE/compiler semantics remain separate |
| `../integrator_certified/LinearSupport.lean`, `RKFLinear.lean`, `PDLinear.lean`, `CanonicalLinear.lean` | Connected stored-coefficient graph errors against the exponential solution, concrete binary128 nearest-rounding instantiation, and repeated-step error propagation | Prescribed scalar `y'=y` graph, zero reference, bounded states/steps; source correspondence, compiled arithmetic and controller invariants remain separate |

The final counterexample takes one step from 0 to 1 and uses the actual six stored Fehlberg abscissae as exact rational roots. Lean proves the derivative of its explicit antiderivative, its initial value and positive endpoint, each sampled derivative being zero, and every weighted sum of these samples being zero. This refutes a universal bound of true local error by any finite multiple of the embedded estimate. It is a mathematical counterexample, not a claim that this force occurs in astronomy.

Generated files retain explicit theorem statements and `#print axioms` audits. The generator is not trusted for the truth of the propositions Lean checks, but it remains trusted for selecting the intended propositions and connecting them to the source/data model. A proof of the wrong specification would not establish program correctness. The complete rounded graph avoids treating isolated arithmetic lemmas as an end-to-end result.

## What is trusted

The checking base includes the pinned Lean 4.24.0 executable/runtime and C++ kernel, its standard inductive/quotient machinery, the three foundational axioms `propext`, `Classical.choice`, and `Quot.sound`, the small raw-replay adapter/driver, Python's orchestration and archive/hash code, the OS, and hardware. The allowed axioms' universe parameters and exact expression types are compared with canonical core declarations from the verified Lean release; matching an axiom name alone is insufficient.

`bootstrap.py` pins the Lean release archive by SHA-256, mathlib by Git commit, and transitive source dependencies through mathlib's lock file. Checking verifies the installed Lean tree against that archive. Tool integrity is reproducibility evidence, not a proof that the compiler used to build Lean or the host machine is correct.

Cached mathlib declarations are not accepted merely because elaboration loaded them. `Replay.lean` collects the complete dependency closure, rejects unsafe/partial declarations and unapproved axioms, reconstructs and checks declarations through raw `Kernel.Environment.addDeclCore` at trust level zero, and starts with an empty kernel environment. Canonical equality is rechecked; the quotient primitive is installed once. Constructor/recursor metadata is checked during reconstruction. This uses the **same Lean kernel implementation**, not a second independently implemented kernel.

The adapter derives from [Lean 4.24.0's replay utility](https://github.com/leanprover/lean4/blob/v4.24.0/src/Lean/Replay.lean). The frontend replay API was unsuitable here: a private-name collision emitted an internal panic while the process recovered with exit status zero. The raw kernel API avoids that frontend state. The runner rejects internal panics regardless of exit code and never counts that earlier run as evidence.

SMT obligations elsewhere are checked by solvers, not by Lean. The source-to-WASM checker trusts its two restricted interpreters, Clang's AST, memory abstraction, and SMT solvers. The ephemeris proof additionally needs the documented C++/IEEE-to-graph correspondence, time/index model, successful I/O and source-cache assumptions, and the exhaustive coefficient-envelope scan. Neither bytecode execution nor astronomical model accuracy follows from these conditional real theorems.

## Failures must remain failures

The runner invalidates its prior result before checking. A successful report requires all expected theorem audits and replay roots, only allowed canonical axioms, and successful negative controls. Nonzero exits, missing audits, `sorryAx`, custom axioms, unsupported proof inputs, internal panics, and incomplete runs fail. Smoke evidence has its own output path and scope.

Negative controls include replacing a theorem proof with `True.intro`, forging an allowed-name axiom's signature, importing an unapproved axiom, requesting an absent theorem, and simulated panic/admission output. Separate ephemeris controls delete a required derivative term and replace a rounded multiplication with addition; Lean must reject both. Logs and exact source/tool hashes accompany `evidence/report.json`.

The proof sources and new adapters use GPL-2.0-or-later, except `RawReplay.lean`, adapted from Kim Morrison's Apache-2.0 code. Its original notice and [Apache license](LEAN-LICENSE.txt) are retained. Lean/mathlib are development dependencies; no Lean runtime is linked into the WASM solver.
