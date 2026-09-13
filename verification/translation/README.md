# Source-to-WebAssembly translation validation

Prove equivalence of actual compiled function bodies for every modeled binary64
input. This is a restricted translation validator, not a proof of the complete
compiler or orbit solver.

```sh
.venv/verification/bin/python -m pip install -r verification/translation/requirements.txt
.venv/verification/bin/python verification/translation/verify.py
.venv/verification/bin/python verification/translation/test_checker.py
.venv/verification/bin/python verification/translation/replay.py
```

The first command installs only into the local verification environment. The
main command recompiles pinned source, validates the current `dist/fo.wasm`,
checks its manifest/source lock, runs negative controls, and refreshes
`evidence/report.json`. It accepts `--sources`, `--sdk`, `--shipped`, and
`--output`. Missing distribution metadata or every production correspondence
being unavailable is a failure. The replay command checks stored SMT hashes
and reruns both solvers; it does not validate current distribution files.

## Established coverage

| Actual upstream function | Extracted O0 | Extracted O3 | Current shipped module |
|---|---|---|---|
| `dot_product` | Verified | Verified | No retained named body |
| `vector_cross_product` | Verified | Verified | Verified retained body |
| `vector3_length` | Verified | Verified | No retained named body |
| `normalize_vect3` | Verified | Verified | No retained named body |

All ten positive obligations (eight extracted comparisons, one production
comparison, and one IEEE square-root lemma) return UNSAT in Z3 4.15.4 and cvc5
1.3.4. Four negative arithmetic/control/memory-store mutations return SAT in
both solvers with concrete IEEE inputs, and each witness changes behavior when
replayed in Node's actual WebAssembly engine. Four additional controls reject
an out-of-bounds read, an unsupported WASM instruction, an invalid binary, and
an unsupported source operator. Ten checker regression tests exercise rejection
and semantic distinctions, including signed zero and solver `unknown`.

The absence of three production names may reflect inlining or elimination;
absence alone does not establish which. Their extracted proofs do not validate
inlined production call sites. The driver never adds exports or changes the
production binary to improve its coverage.

## How the proof works

1. Check the actual upstream commit and exact function hashes. Match the full
   source file against the shipped source lock and the binary against its
   manifest. Reject distribution changes during validation.
2. Extract unchanged definitions into a small translation unit, adding only a
   math include, an empty `DLL_FUNC`, and external C linkage. Obtain Clang's
   actual JSON AST and retain its semantic tree. Compile with pinned Emscripten,
   `-fno-fast-math -ffp-contract=off -g2`, at O0 and O3.
3. Interpret the restricted source AST as IEEE binary64 operations and explicit
   memory effects. Independently decode actual WASM bytes and symbolically
   execute their instructions. The proof does not use a disassembler's output.
4. Compare return values, all caller-visible cells, and path coverage. Retained
   production functions are resolved using debug-name metadata and checked for
   parameter/return ABI agreement; their exact raw bodies and hashes are saved.
5. Discharge the IEEE lemma `sqrt(x) == 0` iff `x == 0` for all binary64 values
   with both solvers. The optimizer actually changes this condition in
   `normalize_vect3`. Instantiate only this checked lemma in the comparison.
6. Use a sound congruence overapproximation: identical FP arithmetic terms share
   one fresh arbitrary FP value; different terms remain unrelated. An exact
   substitution round trip is checked. Every concrete IEEE valuation is an
   instance of the stronger model, so UNSAT establishes concrete equivalence.
   This avoids bit-blasting unchanged multipliers. An abstract SAT is never
   called a real counterexample or accepted as a proof.
7. Replay the emitted SMT-LIB obligation with independent cvc5. Unknown,
   timeout, SAT on a positive obligation, unsupported semantics, and malformed
   artifacts all fail. Save concrete formulas, abstraction substitutions,
   obligations, AST, compiler commands, binary bodies, and hashes.

This proves an interesting control-flow optimization and reversed store order
in addition to arithmetic expression correspondence. Positive validation does
not sample floating-point inputs. Concrete input fixtures are used only to
witness intentionally incorrect binary mutations.

## Exact domain and trusted base

Inputs range over all IEEE binary64 values, including signed zeros, subnormals,
infinities, and NaN classes. Equality distinguishes positive and negative zero.
NaN payload and sign are deliberately unobservable: SMT-LIB FP has a single NaN,
and WASM permits non-deterministic NaN payload propagation. Do not interpret this
as a proof of identical raw NaN bit patterns.

Each pointer denotes a distinct aligned 24-byte array, disjoint from other
arguments and stack. Arrays contain initialized doubles and have valid wasm32
addresses with no wrapping. The normalizer may update its own array. The
checker models the compiler's typed stack spills in up to 512 valid bytes;
stack scratch bytes are outside the observable output. Conditional pointer
selection, type-punned or overlapping accesses, arbitrary pointer bit
operations, uninitialized reads, and out-of-bounds accesses are rejected.
Pointers are represented by object identity plus constant byte offset, so
absolute placement is irrelevant under these allocation preconditions.
Disjointness is a verification restriction: overlapping double arrays can be
legal C++. This work does not prove that every production caller meets the
restriction, and does not classify all aliasing calls as undefined behavior.

No concurrency, volatile effects, floating-environment/exception observation,
`errno` observation, dynamic rounding mode, or NaN payload/sign inspection is
modeled. The source interpretation fixes IEEE round-to-nearest ties-to-even and
IEEE `sqrt` semantics. Source constructs/opcodes outside the implemented subset
fail closed. Loops, direct/indirect calls, SIMD, and global writes are unsupported.
Unexecuted module initialization and runtime internals are not verified.

The trusted base includes source extraction, Clang's parser/AST, both custom
interpreters, the binary decoder, memory abstraction, congruence substitution,
Z3, cvc5, and the host binary validator. Independent solver replay reduces
single-solver risk but is not an independently kernel-checked proof certificate.
The result establishes behavior for the named function bodies, not all compiler
passes, all solver call sites, physical astronomy, or total solver accuracy.

## Why not claim an Alive2 proof?

[Alive2](https://github.com/AliveToolkit/alive2) supports LLVM translation
validation and is a reasonable further tool for arithmetic transformations. Its
LLVM integration requires a compatible LLVM build with RTTI and exceptions,
usually tracking LLVM main; it also does not support interprocedural
transformations. That would require a separate matching LLVM build rather than
using the installed Emscripten tools directly. No Alive2 validation was run or
claimed here. This validator instead checks final WASM instruction bodies,
including backend/Binaryen changes, within its explicitly smaller supported
subset.

Primary references:

- [Clang AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html) and
  [floating-point controls](https://clang.llvm.org/docs/UsersManual.html#controlling-floating-point-behavior).
- [WASM numeric semantics](https://webassembly.github.io/spec/core/exec/numerics.html)
  and [instruction/memory semantics](https://webassembly.github.io/spec/core/exec/instructions.html).
- [SMT-LIB floating point](https://smt-lib.org/theories-FloatingPoint.shtml).
- [cvc5 Python API](https://cvc5.github.io/docs/cvc5-1.3.4/api/python/python.html).
- [Original lunar kernels](https://github.com/Bill-Gray/lunar/blob/d95191818d7975c22613f231fea160341203abbe/miscell.cpp).
