# Verification

Run targeted formal obligations and executable compiler checks against the
pinned sources fetched by `npm run build`. These do **not** verify the entire
orbit solver. Read [the scope and findings](../docs/verification.html).

```sh
python3 -m venv .venv/verification
.venv/verification/bin/python -m pip install -r verification/requirements.txt
.venv/verification/bin/python verification/prove.py
python3 verification/compiler_checks.py
.venv/verification/bin/python verification/prove_wide_multiply.py
node verification/check-wide-multiply.mjs
```

The SMT command needs Python 3.9+ and the pinned Z3 wheel. Compiler checks need
Clang++, Node, and the installed pinned Emscripten SDK at `.wasm-toolchain`.
Both commands accept `--sources PATH`; compiler checks also accept `--sdk PATH`.
They do not fetch upstream code or change the engine. Reports go under
`results/local/` by default; `--output PATH` overrides that. Each formal
obligation is also emitted as SMT-LIB beside the proof report for inspection
or replay in another solver.

`source-contracts.json` checks exact upstream commits and function SHA-256s.
The search and JPL record-selection models are manually reviewed abstractions;
vector expressions are parsed directly from the actual C++ definitions. A
source change fails closed: review the proof/model before updating its hash.
Never refresh hashes just to make checks pass.

The compiler probe compiles actual extracted functions with native O0/O3,
native address/undefined/function sanitizers, and WASM O0/O3. It compares 50,121
vector cases, checks 21,229 search cases against a linear oracle, checks nested
callback contexts, probes binary64/subnormal/FMA behavior, and reports the
native versus WASM long-double ABI. NaN payloads/signs are normalized in the
comparison hash; other output bits, including signed zero, are preserved.
Sanitizers cover these extracted functions and this corpus only.

Recorded results from 2026-09-13 are in `evidence/`. Re-run the commands for
current evidence. Do not interpret a sampled hash match as universal compiler
correctness, or an exact-real vector identity as a floating-point error bound.

The experimental compiler-rt multiplication helper has a separate source
contract in `wide-multiply-contract.json`. Its 31 SMT obligations prove the
complete unsigned 128×128→256 product using local overflow/carry bounds and
the weighted-digit invariant through all four rows, for every input pair,
including the low-64-zero specialization and operand swap.
The model-to-C correspondence remains manually reviewed. A separate BigInt
oracle compares the actual compiled helper against exact integer products for
36,868 input pairs in native O3 with sanitizers and WASM O0/O3. These checks
establish the integer helper's behavior; adopting it in a solver still requires
confirming that the linked binary actually calls it and passes end-to-end
accuracy/benchmark gates. IEEE binary128 normalization and rounding remain in
the unchanged upstream compiler-rt code.
