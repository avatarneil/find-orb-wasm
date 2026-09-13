# Find_Orb WebAssembly

A standalone WebAssembly port of [Bill Gray / Project Pluto’s Find_Orb](https://github.com/Bill-Gray/find_orb), the original C/C++ orbit-determination solver. This is an experimental independent port, not an official Project Pluto release.

Extracted from the latest `webastrometrica` `origin/main` at `c86e53ccf9fa662bc43fb0b3eed67594790e52a2`. See [provenance.json](provenance.json) for exact source-file hashes. The browser application and its job policy remain in WebAstrometrica.

Read the [correctness research](docs/correctness-research.html) for kernel-checked numerical theorems, restricted translation validation of selected WASM functions, and reproduced integrator defects. The [earlier performance study](docs/findings.html) records native/WASM benchmarks and the **6.33 MB** compact data download.

The [short-arc accuracy study](docs/short-arc-research.html) separates weak range/range-rate information from propagation error, evaluates three alternative orbit representatives against withheld Horizons predictions, and measures additional-night recovery. Its mixed results preserve the released solver default. Reproducible experiments and hashed raw evidence are included; the study also identifies an upstream ranging/refinement control-flow issue and fixes a native comparator rebuild defect.

[GitHub release v0.1.0](https://github.com/avatarneil/find-orb-wasm/releases/tag/v0.1.0) preserves the initial unoptimized port at `fe8a88d`, with its runtime, full dataset, corresponding source, license notices, checksums, and seven-case accuracy results. Release [v0.2.0](https://github.com/avatarneil/find-orb-wasm/releases/tag/v0.2.0) ships the optimized runtime with a 6.33 MB compact download; the initial release predates these changes. Compact and full runtime archives each have their own matching manifest and data asset. Do not mix them. Versioned browser assets, source and notices are hosted at https://avatarneil.github.io/find-orb-wasm/v0.2.0/. The [release parity results](results/parity-v0.2.0.json) compare both packs with the unmodified pinned upstream executable.

## Build

Requires Node 24+, Git, GNU make, Python 3.10+, and a C/C++ toolchain on macOS or Linux. All downloads and builds remain local.

```sh
git clone https://github.com/emscripten-core/emsdk.git .wasm-toolchain
git -C .wasm-toolchain checkout --detach c0bb220cb6e6f4e0fabb6f6db9efd53390ef5e56
.wasm-toolchain/emsdk install 4.0.23
.wasm-toolchain/emsdk activate 4.0.23
npm run build
```

The build pins Find_Orb, lunar, jpl_eph, sat_code, Emscripten, and the full JPL DE440 ephemeris. To reuse a downloaded DE440 file, pass `npm run build -- --ephemeris /absolute/path/linux_p1550p2650.440`; its SHA-256 is verified. Optional `--sdk`, `--work`, and `--dist` select local directories. The local SDK's Python is selected automatically on macOS; Linux needs Python 3.10+ on its path.

## Use

Import `createSession` from `src/index.js`, supply the built `dist/find-orb-worker.js` source, and call `initialize(dataArrayBuffer, signal)` with `dist/find-orb.data`. Call `execute(args, files, outputPaths, signal)` and always `close()` the session in `finally`. Inputs and outputs are bounded text files under `/job/`; astronomical reference files live under `/engine/`. The low-level interface accepts trusted CLI arguments. Applications must validate observation and job policy.

Each command receives a fresh instance, heap, globals, and filesystem. The session retains the immutable compiled `WebAssembly.Module`, so repeated commands can reuse compiled code without retaining solver state. The worker supports cancellation and timeouts; initialization verifies the data and WASM checksums before compilation. See `src/index.d.ts` for the API.

Reference files use copy-on-write storage: jobs share verified bytes for reads and receive private copies if they write or truncate a reference file. Solver state is never shared between commands.

## Compact data without file selection

```sh
npm run data:compact
```

This creates `dist-compact/` with the unchanged solver and losslessly selected DE440 records for 2000–2040, plus boundary margins. The default pack retains **every auxiliary file**. It is 11,376,515 bytes raw or **6,329,416 bytes gzip**, versus the full pack's 109,894,483 bytes raw. The exact supported interval is `(1999-11-22, 2040-02-08]` in the ephemeris time scale. J2000 coverage is required by upstream's state-command initialization.

Applications can load the compressed pack automatically from their static host:

```js
import {createSessionFromUrls} from 'find-orb-wasm';
// Bundle or pin the corresponding manifest with your application.
const session = await createSessionFromUrls({
  workerURL: '/solver/find-orb-worker.js',
  dataURL: '/solver/find-orb.data.gz',
  compression: 'gzip',
  manifest: trustedBuildManifest,
  signal: abortController.signal,
});
try {
  const result = await session.execute(trustedArgs, jobFiles, outputPaths);
} finally {
  session.close();
}
```

The explicit API call starts the download, verifies both assets, and initializes the worker. No manual data selection is needed. Serve the `.gz` file as `application/gzip`; ordinary HTTP `Content-Encoding: gzip` is also handled. Initialization uses bounded decompression and supports cancellation. Once initialized, calculations need no network. First-load offline support still requires the host application to package or cache the assets.

Every actual JPL query must fit the supported interval, including intermediate integration, initialization, and light-time evaluations. Out-of-range, missing, or unreadable ephemerides **fail the job**; approximate fallback is disabled. Use the full pack for historical work or choose a wider window with `--start-jd` and `--end-jd`. See [dataset findings](docs/dataset.html) and [machine-readable evidence](results/dataset.json).

## Validation and benchmarks

Keep a copy of the pinned full DE440 file at `.cache/linux_p1550p2650.440`, or extract it from the full pack:

```sh
mkdir -p .cache
node --input-type=module -e "import fs from 'node:fs'; const m=JSON.parse(fs.readFileSync('dist/manifest.json')); const e=m.entries[m.ephemeris.filename]; fs.writeFileSync('.cache/'+m.ephemeris.filename,fs.readFileSync('dist/find-orb.data').subarray(e.offset,e.offset+e.size));"
npm run build:native
npm ci
npm test
npx playwright install chromium
npm run test:browser
npm run verify:data
npm run benchmark -- --output results/local/benchmark.json --warmup 2 --repetitions 7
```

The suite benchmarks the original native executable, a separately labeled native comparator with a matched ranging budget, and actual WASM. It covers short-arc fitting, independent JPL Horizons propagation and topocentric predictions, held-out recovery, and high-eccentricity/near-parabolic/hyperbolic propagation. Reports retain raw outputs, individual timings, setup costs, source/fixture hashes, host details, and accuracy checks. See [benchmark instructions](benchmark/README.md).

Run the source-anchored proofs and compiler probes separately:

```sh
python3 -m venv .venv/verification
.venv/verification/bin/pip install -r verification/requirements.txt
npm run verify:proofs
npm run verify:compiler
npm run verify:experimental
```

Proof obligations cover selected search/vector operations, floating-point counterexamples, and DE440 record-selection equivalence. Compiler probes compare extracted actual routines across native and WASM optimization levels and native sanitizers. The [verification report](docs/verification.html) defines each guarantee, assumptions, trusted components, and limitations.

The experimental command checks a separately built exact integer multiplication helper, including its 31 proof obligations and binary128 differential corpus. This helper is not enabled in the shipping solver: its measured fitting gain was too small to establish an improvement. Default port obligations and experiments remain separately identified in the evidence.

## Numerical policy

Preserve upstream precision: binary64 `double`, Emscripten software binary128 `long double`, no fast-math, and disabled FP contraction throughout all four source projects. Keep a fresh C runtime for each job. Checked portability patches replace a mismatched function-pointer cast, disable unsupported POSIX process controls in WASM, and complete the configured statistical-ranging candidate budget instead of stopping after a CPU-dependent half second. External timeouts reject incomplete jobs.

Research identified and corrected a shifted stage-time array and an unreleased workspace in the optional Prince–Dormand integration path. The default Fehlberg path is unchanged. The original PD path returned approximately `0.328675` for a one-step `y'=t` problem whose exact answer is `0.5`. Both original and corrected bodies are tested against exact arithmetic models; see [integrator evidence](verification/integrator/README.md). All patches are explicit in `build/patches.mjs`.

Native/WASM agreement is a port regression check, not independent astronomical truth or a proof of universal numerical accuracy.

## Reproduce the short-arc study

```sh
npm run test:short-arcs
python3 experiments/short-arcs/archive-evidence.py --verify
python3 experiments/short-arcs/archive-evidence.py --extract results/local/short-arcs-restored
node experiments/short-arcs/replay.mjs
node experiments/short-arcs/analyze.mjs results/local/short-arcs-restored/results/local/short-arcs
python3 experiments/short-arcs/plot.py
node experiments/short-arcs/report.mjs
```

Archive verification/extraction needs standard Python; figure generation needs Matplotlib and NumPy. The sanitizer tests need a C++ compiler and the pinned source checkout; unavailable prerequisites are reported as skips. The [evidence manifest](results/short-arcs/evidence-manifest.json) covers raw commands/results, failures, batch counts, source snapshots, and fixture references. Run the commands from the repository root; extraction refuses an existing target directory.

Fresh solver experiments require the native reference build, pinned SDK, and full DE440 input described above:

```sh
node experiments/short-arcs/build.mjs native
node experiments/short-arcs/build.mjs wasm
node experiments/short-arcs/run.mjs --split development --output results/local/new-development
```

These builders require unused experimental work directories. They create `.native-engine-short-arcs/` and `dist-short-arcs/`; released artifacts remain separate. Experimental CLI selectors are `SR_SELECTION=position|phase6d|min-rms`; the `predictive1d` method is a research-harness operation using an exported family and additional propagation commands. None changes the candidate family into a calibrated posterior. See the report for frozen object splits, noise assumptions, retrospective protocol amendments, and limitations.

On the measured Apple ARM host, native `long double` has 53 significand bits and WASM has 113. Native-versus-WASM timing therefore compares the actual implementations with their different extended-precision costs. The port preserves the WASM precision policy.

## Reproduce the correctness research

After building the solver, keep its pinned source checkouts in `.wasm-engine/sources/` and full DE440 file in `.cache/linux_p1550p2650.440`. Use Python 3.12+ (the SDK's Python 3.13 is suitable):

```sh
.wasm-toolchain/python/3.13.3_64bit/bin/python3 -m venv .venv/research
.venv/research/bin/python -m pip install -r verification/research-requirements.txt
npm run setup:proof-tools
npm run verify:research
npm run report:research
```

The first command uses the macOS SDK's Python; on Linux, substitute an installed Python 3.12+ executable. The setup downloads checksum-pinned Lean 4.24.0 and a pinned mathlib/dependency tree into `.cache/`; allow several GB of disk space. Verification uses local tools and data. A complete run takes several minutes and writes `verification/research-evidence.json`; failed reruns invalidate success. `npm run verify:kernel` checks only existing Lean artifacts and does not regenerate their source/data correspondence evidence.

The suite combines explicit real/rational theorems checked and replayed from an empty Lean kernel environment, source-anchored coefficient scans and certificates, restricted source-to-WASM equivalence checked by Z3 and cvc5, native/WASM integrator comparisons, and deliberately invalid proofs/programs. See the [kernel trusted base](verification/kernel/README.md), [ephemeris scope](verification/ephemeris/README.md), and [compiler scope](verification/translation/README.md). It does **not** prove the complete solver, compiler toolchain, astronomical model, or browser correct.

The extended suite derives rounding bounds from [finite-format nearest selection](verification/rounding/README.md), proves connected [linear-ODE integrator bounds](verification/integrator_certified/README.md), validates the [retained production interpolation slice](verification/production/README.md), and checks [production binary128 conversions and shifts](verification/runtime/README.md). Each result states its domain and remaining implementation assumptions.

## Rebuild corresponding source

Every build includes `corresponding-source.tar.gz`, the patched upstream code, local build/runtime/data recipes, all license notices, and a source-file checksum lock. With the SDK and full DE440 already available, rebuild directly from the archive without Git or source-network access:

```sh
mkdir source-release
tar -xzf dist/corresponding-source.tar.gz -C source-release
node source-release/build/build.mjs --sources source-release/sources \
  --sdk "$PWD/.wasm-toolchain" --work "$PWD/.wasm-engine-from-source" \
  --dist "$PWD/dist-from-source" --ephemeris "$PWD/.cache/linux_p1550p2650.440"
```

The archive rebuild requires an empty work directory and verifies source hashes before compilation. Retain the complete distribution, including the corresponding source archive and notices, when hosting the worker and data.

## License and attribution

Find_Orb and port additions are **GPL-2.0-or-later**. Preserve all upstream copyright notices. The pinned dependencies have different notices: `lunar` is GPL-2.0-or-later; `sat_code` is MIT; `jpl_eph` has GPL-2.0-or-later core source notices and a GPLv3 repository license file. The combined binary distribution uses GPLv3. See [NOTICE](NOTICE), [LICENSE](LICENSE), and [licenses/](licenses/).

Distribute the corresponding source archive and complete build recipes with solver binaries, together with the Emscripten/runtime notices. JPL DE440 data has separate provenance in `build/pins.mjs`.

Upstream projects: [Find_Orb](https://github.com/Bill-Gray/find_orb), [lunar](https://github.com/Bill-Gray/lunar), [jpl_eph](https://github.com/Bill-Gray/jpl_eph), [sat_code](https://github.com/Bill-Gray/sat_code), [Emscripten](https://github.com/emscripten-core/emscripten), [JPL ephemerides](https://ssd.jpl.nasa.gov/planets/eph_export.html).
