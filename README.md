# Find_Orb WebAssembly

A standalone WebAssembly port of [Bill Gray / Project Pluto’s Find_Orb](https://github.com/Bill-Gray/find_orb), the original C/C++ orbit-determination solver. This is an experimental independent port, not an official Project Pluto release.

Extracted from the latest `webastrometrica` `origin/main` at `c86e53ccf9fa662bc43fb0b3eed67594790e52a2`. See [provenance.json](provenance.json) for exact source-file hashes. The browser application and its job policy remain in WebAstrometrica.

## Build

Requires Node 24+, Git, GNU make, Python 3.10+, and a C/C++ toolchain on macOS or Linux. All downloads and builds remain local.

```sh
git clone https://github.com/emscripten-core/emsdk.git .wasm-toolchain
git -C .wasm-toolchain checkout --detach c0bb220cb6e6f4e0fabb6f6db9efd53390ef5e56
.wasm-toolchain/emsdk install 4.0.23
.wasm-toolchain/emsdk activate 4.0.23
npm run build
```

The build pins Find_Orb, lunar, jpl_eph, sat_code, Emscripten, and the full JPL DE440 ephemeris. To reuse a downloaded DE440 file, pass `npm run build -- --ephemeris /absolute/path/linux_p1550p2650.440`; its SHA-256 is verified. Optional `--sdk`, `--work`, and `--dist` select local directories.

## Use

Import `createSession` from `src/index.js`, supply the built `dist/find-orb-worker.js` source, and call `initialize(dataArrayBuffer, signal)` with `dist/find-orb.data`. Call `execute(args, files, outputPaths, signal)` and always `close()` the session in `finally`. Inputs and outputs are bounded text files under `/job/`; astronomical reference files live under `/engine/`. The low-level interface accepts trusted CLI arguments. Applications must validate observation and job policy.

Each command receives a fresh module, heap, and filesystem. The worker supports cancellation and timeouts; initialization verifies the data and WASM checksums. See `src/index.d.ts` for the API.

The initial reference pack is 109,894,483 bytes. It contains astronomical reference data, not precomputed fitted orbits. Build outputs also include `manifest.json`, `fo.wasm`, `fo.js`, `fo.cjs`, license notices, and `corresponding-source.tar.gz`.

## Numerical policy

Preserve upstream orbital arithmetic: binary64 `double`, Emscripten software binary128 `long double`, no fast-math, and disabled FP contraction in Find_Orb. Keep a fresh C runtime for each job. Checked portability patches replace a mismatched function-pointer cast, disable unsupported POSIX process controls in WASM, and complete the configured statistical-ranging candidate budget instead of stopping after a CPU-dependent half second. External timeouts reject incomplete jobs.

Native/WASM agreement is a port regression check, not independent astronomical truth or a proof of universal numerical accuracy.

## License and attribution

Find_Orb and port additions are **GPL-2.0-or-later**. Preserve all upstream copyright notices. The pinned dependencies have different notices: `lunar` is GPL-2.0-or-later; `sat_code` is MIT; `jpl_eph` has GPL-2.0-or-later core source notices and a GPLv3 repository license file. The combined binary distribution uses GPLv3. See [NOTICE](NOTICE), [LICENSE](LICENSE), and [licenses/](licenses/).

Distribute the corresponding source archive and complete build recipes with solver binaries, together with the Emscripten/runtime notices. JPL DE440 data has separate provenance in `build/pins.mjs`.

Upstream projects: [Find_Orb](https://github.com/Bill-Gray/find_orb), [lunar](https://github.com/Bill-Gray/lunar), [jpl_eph](https://github.com/Bill-Gray/jpl_eph), [sat_code](https://github.com/Bill-Gray/sat_code), [Emscripten](https://github.com/emscripten-core/emscripten), [JPL ephemerides](https://ssd.jpl.nasa.gov/planets/eph_export.html).
