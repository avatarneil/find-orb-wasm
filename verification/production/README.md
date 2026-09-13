# Production JPL interpolation validation

This checker validates the interpolation slice **inside the actual distributed
`fo.wasm`**, under explicit entry assumptions. It connects that machine code to
the pinned `interp` source and the existing rounded Chebyshev DAG certificates.
It does not prove the whole `jpl_state` function, compiler, or orbit solver.

Run from the repository root after building the distribution and generating the
ephemeris certificate:

```sh
.venv/verification/bin/python verification/production/run.py
```

The existing verification environment supplies Z3 and cvc5. Node.js and the
project Emscripten SDK are also required. The default run takes approximately
30 seconds on the development Apple Silicon machine. `--shipped`, `--sdk`, and
`--output` accept alternate paths. On SDK installations without bundled Python,
the layout compiler uses the current Python interpreter. The command runs its
17 checker regressions automatically; they can also run separately:

```sh
.venv/verification/bin/python verification/production/test_checker.py
```

## Checked result

The initial validated distribution has SHA-256
`256e850727f91a441f2344217a6a15727dfefcabb91f03b61e8d694d9d03cd57`.
Its retained `jpl_state` is function 286, with a 5,157-byte body. The validated
interpolation slice occupies bytes `[429695, 431501)`, with its actual selection
guard immediately before it at `[429680, 429693)`. These numbers are evidence,
not hardcoded selection criteria: the runner decodes the actual function and
requires a unique structured branch containing the two interpolation-cache
counter updates. It then executes the selected raw instructions, including
their control, addressing, loads, and stores.

| Evidence | Coverage |
| --- | --- |
| 14,796 symbolic cases | `ncf=6..14`, one/two/three components, Sun and external-output destinations, quantities 1/2/3, cold cache and every `2 <= velocity-prefix <= position-prefix <= 17` |
| 5,265 setup correspondences | Actual body selectors 0–14, quantities 1–3, each coefficient count, and all 13 distinct coefficient-pointer fields in the DE440 certificate |
| Universal affine addressing | Every `na` in `{1,2,4,8}` and every integer subinterval `0 <= L < na` |
| 114 certificate correspondences | All 13 DE440 profiles, their components, and position/velocity/acceleration expressions |
| 12 dual-solver UNSAT obligations | Classified addition/multiplication symmetry, coefficient geometry, unrolled-loop partitions, cache self-comparison, actual selection predicate, coefficient base-address arithmetic, and four exact derivative scales |
| 5 mutation controls | Three changed real bytecode operations with observable WebAssembly execution witnesses; invalid memory access and unsupported executed operation rejection |
| 17 checker regressions | Type/alias/bounds failures, symbolic branches, loop and stack failures, ambiguous selection, and forbidden floating rewrites |

The symbolic cases range over **all coefficient and cached floating encodings**
within their entry assumptions. They are not sampled astronomical inputs.
The structured interpreter executes every integer iteration for the finite
control domain; floating expressions remain symbolic. Coverage records include
instructions unreachable in this domain, without claiming they were validated
on some other domain.

## What the argument establishes

`source_model.py` follows the cache updates and descending accumulation loops of
the frozen C++ function. The three recurrence expressions are parsed from that
actual source by the existing narrow ephemeris parser. This is a reviewed,
restricted source interpreter; it is not a general C++ frontend proof.

`decoder.py` reads the retained production body directly. `machine.py` implements
the supported structured WebAssembly instructions, integer control, typed
object memory, and floating expression DAG. It rejects unsupported executed
instructions, symbolic conditions without a proved domain rule, out-of-bounds
or overlapping typed accesses, coefficient writes, incomplete exits, and
exceeded execution bounds. The interpreter includes the optimized recurrence
and accumulation loops; it does not replace them with assumed source loops.

Both interpreters must produce identical caller-visible memory and cache
counters. Floating equality is DAG congruence after commuting only addition and
multiplication. It preserves evaluation association and signed zeros and does
not simplify addition by zero. NaN payload and sign are quotiented; a caller
that observes NaN payload bits is outside this guarantee.

The actual integer setup prefix must have no stores. For all body selectors and
DE440 pointer fields, its live inputs to the arithmetic core must match one of
the four exhaustively checked destination/component classes. This discharges
the setup-to-core composition; it does not assume that a manually chosen block
has the right output pointer. Affine coefficient addresses retain symbolic
`L`, and every load must stay inside its selected coefficient block. The SMT
address lemma proves allocation bounds for each allowed `na`.

`dag-bridge.json` records equality between cold/recomputed production expressions
and each existing certificate output. Thus existing kernel-checked bounds can
apply to these production expressions **when their numerical premises hold**.
Those premises include the coefficient envelopes, correct normalized input,
the rounding premise, and exact `vfac = (2*na)/32`. The four scale calculations
are separately checked with native IEEE binary64 SMT operations.

## Explicit entry assumptions

The proof begins at the selected interpolation branch after outer `jpl_state`
date, `modf`, subinterval, record-selection, and I/O setup. It checks the actual
guard `quantities != 0 && ipt.na == grouping_na`, then the selected body. It does
not establish reachability or these incoming source-to-local mappings from
function entry:

| Incoming local(s) | Required meaning |
| --- | --- |
| 0 | Valid ephemeris structure |
| 3, 4, 7, 10, 17 | Caller output pointers, Sun-selection flag, `pvsun`, and selected body index |
| 6, 12, 19 | Selected `ipt` entry, matching grouping `na`, and quantities 1–3 |
| 15 | Valid private interpolation stack scratch |
| 22, 27 | Velocity and position cache bases |
| 26, 30 | Loaded coefficient-record base and selected subinterval `L` |
| 33, 34 | Ephemeris-relative helper pointers at offsets 480 and 336 |
| 42, 43, 48 | `vfac`, finite normalized `tc` in `[-1,1]`, and already computed `tc + tc` |

For body indices below 10, the output base is represented relative to that
body's selected output view; the actual integer offset computation is executed.
Likewise coefficient memory is an object view relocated by the actual DE440
pointer field. The model assumes corresponding absolute pointers can be formed
without wrapping and that the allocated coefficient, output, ephemeris, and
stack objects are appropriately aligned and disjoint, except for the explicit
Sun destination inside the ephemeris object. The selected output has at least
`ncm * quantities` doubles. Layout assertions use the real source header and
wasm32 compiler target.

The initial cache seeds are `p[0]=1`, `d[0]=0`, and `d[1]=1`. On a cold cache,
the old counters are arbitrary i32 values and must be overwritten before use.
On a warm cache, `cached_tc == tc` under IEEE comparison; all cached polynomial
values and `twot` may otherwise be arbitrary in the translation proof. The
numerical bound additionally requires a correct warm numerical cache. Warm
cache counters outside the enumerated range, including 18, are not covered.

## Floating rule and trusted-base boundary

The two commutation lemmas use explicit classified WebAssembly numeric rules:
NaNs, infinities, signed zeros, and finite arithmetic followed by an arbitrary
deterministic rounding function. Z3 and cvc5 prove symmetry over every input bit
encoding in that model. The finite-value interpretation and rounding function
are unconstrained, so this proof does not depend on sample values or a chosen
implementation of rounding.

The correspondence of that classified model to the WebAssembly numeric
specification remains a **reviewed specification assumption**. Direct native
SMT floating-point commutativity attempts timed out; those attempts are not
reported as successful proofs. Neither the classified rules nor the Python
interpreters are independently kernel-checked by this command. Z3 and cvc5 are
independent solver implementations, not independent proofs of the source
interpreter or the WebAssembly decoder. The existing Lean DAG and rounding
certificates have separate runners and reports.

The trusted base also contains Python, the source-contract mapping, compiler
layout assertions, the host validator, and the WebAssembly runtime used for
negative witnesses. Tool hashes and versions record provenance rather than
attesting to the host OS. No conclusion covers outer time selection, I/O,
absolute allocation, concurrency, km-to-AU conversion, barycentric subtraction,
Earth/Moon combinations, or physical ephemeris-model accuracy.

## Evidence and failure behavior

The runner invalidates `evidence/report.json` before work and writes
`passed: true` only after all checks finish. Solver `unknown`, timeout,
unsupported semantics, source-lock mismatch, or any changed frozen input fails
the run. Inputs include the shipped module and manifest, source lock, C++
source/header, certificate, source parser, both imported checker modules and
solver harness, local checker files, and the selected compiler/Python/Node
binaries. The central verification runner additionally freezes the whole
verification run's source and tool set.

Retained artifacts include `jpl_state.body.bin`, `interp-slice.bin`, exact SMT-LIB
queries and their hashes, per-case state hashes, control coverage, the
certificate bridge, compiler layout assertions, and mutation modules/fixtures.
The negative witnesses embed the exact original slice bytes into a small
module and then change one real opcode; no optimizer rebuild stands in for the
production slice. They compare caller-visible cache and output bytes, excluding
stack scratch. Sampled witnesses test rejection, while the positive argument
uses universal symbolic expressions and exhaustive bounded control.

## Primary sources

- [Pinned Project Pluto JPL ephemeris source](https://github.com/Bill-Gray/jpl_eph/blob/a73f25e54d02b99b1c0d9a9d6c61acfbb2fa3a26/jpleph.cpp)
- [WebAssembly binary instruction encoding](https://webassembly.github.io/spec/core/binary/instructions.html)
- [WebAssembly numeric semantics](https://webassembly.github.io/spec/core/exec/numerics.html)
- [SMT-LIB floating-point theory](https://smt-lib.org/theories-FloatingPoint.shtml)
- [cvc5 Python API](https://cvc5.github.io/docs/latest/api/python/python.html)

The verification code is GPL-2.0-or-later, consistent with this repository.
Upstream source attribution and licensing remain in the root distribution.
