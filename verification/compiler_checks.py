#!/usr/bin/env python3
"""Compile actual pinned kernels/search with native sanitizer and wasm32 checks."""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

from common import ROOT, checked_sources


def run(command: list[str], env: dict[str, str]) -> str:
    print("Running: " + " ".join(command), flush=True)
    result = subprocess.run(command, env=env, cwd=ROOT, text=True, capture_output=True, timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, default=ROOT / ".wasm-engine/sources")
    parser.add_argument("--sdk", type=Path, default=ROOT / ".wasm-toolchain")
    parser.add_argument("--output", type=Path, default=ROOT / "results/local/compiler-checks.json")
    args = parser.parse_args()
    functions, contracts = checked_sources(args.sources)
    work = ROOT / "results/local/compiler-probes"
    work.mkdir(parents=True, exist_ok=True)
    source = work / "actual-kernels.cpp"
    # Keep definitions byte-for-byte except the DLL_FUNC macro expands empty.
    # Upstream copyright/license retained in the generated translation unit.
    source.write_text("/* Copyright (C) Project Pluto. GPL-2.0-or-later; see LICENSE. */\n"
                      "#include <cstddef>\n#define DLL_FUNC\n" + "\n\n".join(
                          functions[name] for name in ["bsearch_ext_r", "bsearch_ext", "dot_product", "vector_cross_product"]
                      ) + "\n")
    probe = ROOT / "tests/verification/compiler-probe.cpp"
    compiler = os.environ.get("CXX", shutil.which("clang++") or "clang++")
    empp = args.sdk.resolve() / "upstream/emscripten/em++"
    sdk_pythons = sorted((args.sdk.resolve() / "python").glob("*/bin/python3"))
    em_command = [str(sdk_pythons[-1]), str(empp) + ".py"] if sdk_pythons else [str(empp)]
    env = dict(os.environ)
    config = args.sdk.resolve() / ".emscripten"
    if config.exists():
        env["EM_CONFIG"] = str(config)
    common = ["-std=c++17", "-fno-fast-math", "-ffp-contract=off", str(source), str(probe)]
    runs = {}
    for label, optimization, sanitize in [("nativeO0", "-O0", False), ("nativeO3", "-O3", False),
                                           ("nativeSanitized", "-O1", True)]:
        output = work / label
        flags = ["-fsanitize=address,undefined,function", "-fno-sanitize-recover=all"] if sanitize else []
        run([compiler, optimization, *common, *flags, "-o", str(output)], env)
        runs[label] = json.loads(run([str(output)], env))
    for label, optimization in [("wasmO0", "-O0"), ("wasmO3", "-O3")]:
        output = work / (label + ".cjs")
        run([*em_command, optimization, *common, "-sENVIRONMENT=node", "-sEXIT_RUNTIME=1",
             "-sASSERTIONS=1", "-sSTACK_OVERFLOW_CHECK=2", "-o", str(output)], env)
        runs[label] = json.loads(run(["node", str(output)], env))
    hashes = {result["kernelHash"] for result in runs.values()}
    if len(hashes) != 1:
        raise AssertionError(f"Native/WASM/optimization kernel divergence: {runs}")
    # Inspect optimized LLVM IR produced from the same source kernels.
    # This is a flag audit, not a proof of LLVM transformation correctness.
    ir = work / "kernels-wasm-O3.ll"
    run([*em_command, "-O3", "-fno-fast-math", "-ffp-contract=off", "-S", "-emit-llvm",
         str(source), "-o", str(ir)], env)
    text = ir.read_text()
    forbidden = re.compile(r"\b(?:fadd|fsub|fmul|fdiv|fcmp|call)\s+(?:fast|reassoc|nnan|ninf|nsz|arcp|contract|afn)\b|llvm\.fma\.")
    if forbidden.search(text):
        raise AssertionError("Unexpected relaxed FP semantics in optimized kernel IR")
    report = {"schema": 1, "nativeCompiler": run([compiler, "--version"], env).splitlines()[0],
              "wasmCompiler": run([*em_command, "--version"], env).splitlines()[0],
              "sourceContracts": contracts, "runs": runs,
              "llvmAudit": "No relaxed floating-point instruction flags or llvm.fma intrinsic in extracted kernels at -O3",
              "limits": "Finite corpus, extracted functions, no full-program sanitizer coverage, no compiler proof. Hash normalizes NaN payload/sign only. ABI probes expose rather than erase long-double differences."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"All five compiler runs agree; report: {args.output}")


if __name__ == "__main__":
    main()
