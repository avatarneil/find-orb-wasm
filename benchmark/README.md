# Find_Orb benchmark and accuracy suite

Build the pinned native reference and WebAssembly distribution, then run:

```sh
node build/native.mjs --ephemeris .cache/linux_p1550p2650.440
node benchmark/run.mjs --dist dist --native .native-engine --output results/run.json --warmup 2 --repetitions 7
node --test tests/accuracy/*.test.mjs
```

Recreate the measured pre-optimization baseline from webastrometrica commit `c86e53ccf9fa662bc43fb0b3eed67594790e52a2` using the original package bytes and hashes recorded in `provenance.json`:

```sh
# Requires the same installed .wasm-toolchain and verified .cache DE440 file.
node benchmark/build-baseline.mjs --source ../webastrometrica --work .wasm-engine-baseline-rebuild --dist dist-baseline
```

The local checkout only supplies immutable Git objects; its branch and files are untouched. Omit `--source` to fetch that exact commit into a new local temporary Git directory. `--extract-only` verifies/extracts the recipe without compiling. Use a new empty work directory on each historical build: its original build script predates the current clean-source safeguards. Recreate the final distribution with `npm run build` and retain both distributions separately.

The native build keeps the [original Find_Orb](https://github.com/Bill-Gray/find_orb) source pins pristine. `fo` retains upstream's CPU-time-dependent statistical-ranging budget. The separately identified `fo-count` comparator completes the configured candidate count, matching the WASM port. `engine.json` records binary hashes, compiler, flags, and this distinction. Native dependency arithmetic uses upstream defaults; Find_Orb itself disables fast-math and contraction. Native `long double` follows the host ABI: Apple arm64 uses 53 mantissa bits; WASM uses software binary128 with 113 mantissa bits. These benchmarks compare the real implementations, which have different intermediate precision and costs. The native ephemeris is a symlink to the existing checksum-verified download.

The suite runs real commands through the runtime embedded in each distribution's worker, including its fresh heap and filesystem. For distributions with `runtime.prepare`, it follows worker initialization by compiling and retaining one module per session, recording `setup.compileModuleMs`; every command still creates a fresh instance. Older distributions are measured without adding retention. It never imports the application's calculation code. `--only ceres-30d,ceres-heldout-fit` selects cases. `FIND_ORB_DIST` and `FIND_ORB_NATIVE` select distributions for the accuracy tests. Missing engines fail explicitly.

Every report retains the command, original output files, stdout, individual repetitions, median/min/max, fixture provenance, host, compiler, source pins, and binary hashes. The fixture files were copied byte-for-byte from the webastrometrica revision recorded in `fixtures/provenance.json`.

The seven cases cover a four-observation short-arc fit, 30-day Ceres propagation against independent JPL Horizons states, F52 topocentric position/range/rates/altitude against Horizons, 60-day retrograde propagation at eccentricities 0.95/0.999999/1.4 against native, and a fit to seven synthetic MPC80 observations with two held-out Horizons epochs. Full DE440 planetary forces are required. Every run checks finite outputs, time grids, observations retained, and relevant accuracy tolerances. The short arc must retain its broad uncertainty.

Per-command WASM phases are instantiation, data/input mounting, `callMain`, and output collection. Native solve timing includes process launch and dynamic loading. Pack reading and cryptographic verification are measured separately once; browser worker creation, transfer, network download, and browser-specific JIT behavior are excluded. Warmup uses fresh instances too. Small repetition counts are exploratory; repeat on an otherwise idle machine before claiming a stable speedup.

Native commands receive a temporary copy of the verified support files too: upstream may write `sof.txt` beside its data despite a separate output directory. The shared full ephemeris remains read-only. Native per-job support-file setup is included in `mountMs`; compare `processAndSolveMs` with WASM `solveMs` when examining compute costs. The early exploratory baseline/native measurements preceded this isolation hardening; the final paired report uses isolated native inputs.

Compare two reports, including direct numerical parity:

```sh
node benchmark/compare.mjs results/baseline.json results/optimized.json results/comparison.json
node --expose-gc benchmark/paired.mjs --before dist-baseline --after dist --output results/paired.json --warmup 2 --repetitions 8
```

The paired runner alternates before/after execution order with an even sample count and records the median paired speedup plus observed min/max. It runs synchronous GC before each WASM command and records that housekeeping time separately, outside measured command phases. Without this, the preceding variant's allocations can trigger a GC pause in the next variant's solve phase; the initial uncontrolled run is retained as `results/paired-gc-uncontrolled.json`. The controlled results describe warmed, isolated command costs, excluding GC and browser transfer/startup. It also benchmarks both native variants and checks every candidate directly against both baseline and the count-matched native reference. Run it after builds and other test processes finish; it cannot control unrelated host activity.

Use separate processes with natural GC for the primary latency comparison; retaining compiled WASM in the same process could warm another variant's code cache. The final natural-GC reports use identical two-warmup/eight-repetition settings:

```sh
node benchmark/run.mjs --dist dist-baseline --output results/baseline-natural.json --warmup 2 --repetitions 8
node benchmark/run.mjs --dist dist --output results/final-natural.json --warmup 2 --repetitions 8
node benchmark/compare.mjs results/baseline-natural.json results/final-natural.json results/final-natural-comparison.json
```

`final-natural-comparison.json` reports the ratio of independently measured medians and each variant's observed min/max. It also checks candidate output directly against baseline. `paired.json` separately reports the GC-controlled experiment; its speedups must not be presented as ordinary browser latency. All reports retain exact binary/worker/source hashes, and the setup figures account separately for the final session's retained-module compilation.

Profile the held-out fit and build an isolated precision-preserving full-LTO experiment:

```sh
node --cpu-prof --cpu-prof-dir=results --cpu-prof-name=heldout.cpuprofile benchmark/run.mjs --dist dist --only ceres-heldout-fit --output results/profile-run.json
node build/performance.mjs --variant lto
node benchmark/run.mjs --dist dist-lto --output results/lto.json
```

LTO retains binary128 `long double`, binary64 `double`, disabled fast-math, and disabled floating-point contraction. Its recipe and source tree live separately; the experiment does not replace the default distribution. CPU profiles can be inspected in Chrome DevTools. Differential tests and reference tolerances provide empirical accuracy evidence, not formal proof or assurance about unseen orbit regimes.

The bounded compiler experiments remain separate from the shipping runtime. Full LTO increased code size and slowed both fits on the measured Apple arm64 host. `node build/performance.mjs --variant quad` explores an exact integer implementation of the compiler-rt binary128 multiplication helper, including a path that skips zero low limbs. `node benchmark/check-quad.mjs` compares complete IEEE result bits on one million deterministic random operand pairs and 36,864 edge pairs. The helper also has source-anchored SMT proofs and independent native/WASM-versus-BigInt checks under `verification/`. Its isolated mixed-precision multiplication gain did not establish a stable end-to-end fit speedup, so the default build retains upstream compiler-rt. Existing benchmark JSON files identify their binary hashes; do not interpret an experimental result as a shipping-default measurement.

The module-retention investigation used separate Node processes for each `current`/`retained` × `natural`/`controlled` GC configuration; sharing a process would let a retained module warm the control's identical-byte compilation cache. Reports are `results/module-cache-*.json`. On the measured host, retention cost roughly 0.7 ms once, improved small natural-GC cases by up to 1.22×, and avoided recurring compile/JIT costs after GC (1.79–2.59× for propagation in that experiment). Fits remained compute-bound. These are session/runtime gains with unchanged binaries and precision, not a faster orbit integrator. The first uncontrolled paired report and COW-only controlled report are preserved to make the investigation inspectable.
