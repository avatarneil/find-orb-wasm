# Retained compiler-runtime verification

This suite validates four function bodies directly from the shipping `dist/fo.wasm`:

| Function | Specification |
| --- | --- |
| `__ashlti3` | Logical left shift of a 128-bit word, for `0 <= shift < 128`. |
| `__lshrti3` | Logical right shift of a 128-bit word, for `0 <= shift < 128`. |
| `__extenddftf2` | Exact binary64-to-binary128 field conversion, including subnormal normalization and explicit NaN payload policy. |
| `__trunctfdf2` | Binary128-to-binary64 nearest-even conversion, including underflow, overflow, signed zeros, and quieted NaN payloads. |

The actual retained instructions, branch paths, helper calls, byte-addressed memory effects, and stack-pointer restoration are interpreted symbolically. All input bits are universally quantified. The validator rejects reachable traps, unapproved calls, unsupported instructions, incomplete paths, and solver unknown/timeout results. It never converts these conditions into passed obligations.

The source hashes identify the pinned Emscripten compiler-rt files for audit. This result compares **production WASM instructions to a bit-field specification**, not C ASTs to compiled code. It does not prove the compiler or the complete binary128 runtime correct. Arithmetic routines such as `__addtf3`, `__multf3`, `__divtf3`, and `sqrtl` remain outside this result.

## Preconditions and observable behavior

Memory is the module's declared minimum size, or a larger actual memory with this minimum prefix valid. The output occupies 16 valid bytes, disjoint from a reserved 32-byte stack region. Stack instrumentation bounds are initialized, and the stack pointer lies within those bounds. All memory bytes initially have arbitrary values. Unaligned accesses are allowed by WASM. Shift helpers require a shift count below 128; conversion proofs execute their actual helper calls without replacing them with assumed summaries.

Every function has four universal obligations: reachable-path coverage, memory bounds, result refinement, and unchanged globals/memory outside its output and scratch regions. Scratch memory is unobserved. The narrowing routine has no output-pointer writes. Stack globals are restored. These are entry-state assumptions, not proofs that every caller establishes them.

The binary64 round trip is also proved for every 64-bit encoding. Ordinary values and both zeros return their exact original bits; a NaN returns the original encoding with the binary64 quiet bit set. Widening preserves the original NaN sign and payload shifted into binary128. Narrowing preserves the sign, keeps the high payload bits, and sets the quiet bit. Floating-point exception flags are not modeled.

## Solvers and the IEEE specification bridge

Seventeen positive obligations use bit vectors and arrays in normal Z3 4.15.4 and cvc5 1.3.4 modes. Two additional obligations compare the independent field-conversion specifications with SMT IEEE nearest-even conversion for every non-NaN input. SMT equality distinguishes signed zero. NaNs use the explicit bit policy instead.

Those two bridges require cvc5's **experimental `fp-exp` mode**, which cvc5 labels as having known issues; Z3 uses its standard FP128 support. They are corroborating results with an additional solver qualification, not independently kernel-checked certificates. Direct production-to-field-specification proofs and the round-trip theorem do not use experimental floating-point support.

The field specification rounds the decoded significand once to its target quantum. It does not transcribe the implementation's sequence of sticky-bit shifts. However, its correspondence to the intended IEEE operation still relies on the SMT floating-point semantics and the trusted specification/checker code.

## Reproduce

Build the production distribution and install the pinned research requirements, then run:

```sh
.venv/research/bin/python verification/runtime/verify.py
.venv/research/bin/python verification/runtime/test_machine.py
.venv/research/bin/python verification/runtime/witnesses.py
```

The central `npm run verify:research` includes all three stages. Evidence records the binary and body hashes, visited instructions, source provenance, symbolic obligations, solver versions, elapsed times, and frozen checker inputs. A rerun invalidates its result before checking prerequisites. An interrupted run cannot leave a success result for that run.

The 11 interpreter regressions exercise structured branches, result-stack handling, implicit function returns, masked shifts, signed shifts, `clz`, unaligned little-endian memory, nonwrapping effective addresses, unsupported operations, and solver unknown rejection.

Execution witnesses add 310 finite cases for unchanged production functions. Test-only raw-bit wrappers avoid JavaScript NaN-payload conversion; all original function bodies are byte-for-byte preserved. Four actual opcode mutations produce SAT counterexamples in both solvers. Node then executes each original and mutated body on the same witness and observes the required difference. These finite cases share the field specification with the proof and are execution corroboration, not independent universal proofs.

## Trusted boundary and references

The trusted base includes the raw binary decoder, symbolic integer interpreter, memory/precondition specification, bit-field specification, Z3/cvc5, Python, and the machine executing them. The host WASM validator checks the original module. Test wrappers and Node/V8 are additionally trusted for execution evidence. No independently checked SMT proof certificate, formal interpreter-correctness proof, whole-function caller proof, or Lean connection to `roundBinary128` is claimed.

The intended semantics are documented in the [WebAssembly numerical specification](https://webassembly.github.io/spec/core/exec/numerics.html). The pinned SDK contains [LLVM compiler-rt](https://github.com/llvm/llvm-project/tree/main/compiler-rt/lib/builtins); exact local source hashes appear in the report, so the moving upstream link is attribution rather than a revision lock. LLVM/Emscripten runtime notices remain in the distribution. New verification code is GPL-2.0-or-later, matching the [Find_Orb port](https://github.com/avatarneil/find-orb-wasm), with original [Find_Orb attribution](https://github.com/Bill-Gray/find_orb) preserved.
