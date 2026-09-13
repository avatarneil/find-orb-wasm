#!/usr/bin/env python3
"""GPL-2.0-or-later. Actual source-extracted integrators, native and WASM."""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

from core import (ROOT, HERE, active_macros, coefficient_block, definition,
                  evaluate, qjson, round_binary, sha, sources, tableau)


PRELUDE = r'''
/* Copyright (C) Project Pluto. GPL-2.0-or-later; see repository LICENSE.
 * Original integrator definitions below are extracted without editing.
 * Corrected definitions differ only in the separately recorded two-line patch.
 * The reference and RHS are test doubles, NOT the astronomical force model. */
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cfloat>
static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "Probe serialization requires little endian");
#define ldouble long double
#define MAX_N_PARAMS 16
struct ELEMENTS { int central_obj; };
static int n_orbit_params=6, equation=0;
static ldouble qroots[13];
static int qcount=0;
static unsigned allocations=0, releases=0;
static void *live[128];
static void *tracked_calloc(size_t n,size_t s) {
  void *p=std::calloc(n,s); assert(p);
  for(auto &slot:live) if(!slot) {slot=p; allocations++; return p;}
  std::abort();
}
static void tracked_free(void *p) {
  for(auto &slot:live) if(slot==p) {slot=nullptr; releases++; std::free(p); return;}
  std::abort();
}
static void clean_test_leaks() {
  for(auto &slot:live) if(slot) {std::free(slot); slot=nullptr;}
}
static void compute_ref_state(ELEMENTS*,double *r,double) {
  for(int i=0;i<9;i++) r[i]=0.;
}
static void calc_derivativesl(ldouble t,const ldouble *y,ldouble *f,int) {
  for(int i=0;i<n_orbit_params;i++) f[i]=0.;
  if(equation<=8) {f[0]=1.; for(int j=0;j<equation;j++) f[0]*=t;}
  else if(equation==9) f[0]=y[0];
  else if(equation==10) f[0]=y[0]*y[0];
  else {f[0]=1.; for(int j=0;j<qcount;j++) {ldouble d=t-qroots[j]; f[0]*=d*d;}}
}
static void print_bits(ldouble value) {
  unsigned char bytes[sizeof(value)]; std::memcpy(bytes,&value,sizeof(value));
  const int meaningful=LDBL_MANT_DIG==64 ? 10 : sizeof(value);
  std::printf("\"");
  for(int j=meaningful-1;j>=0;j--) std::printf("%02x",bytes[j]);
  std::printf("\"");
}
#define calloc tracked_calloc
#define free tracked_free
'''


def harness(original: str, corrected: str) -> str:
    # Preserve the actual upstream copyright and full GPL notice verbatim.
    text = original[:original.index("*/") + 2] + "\n" + PRELUDE
    for label, source in [("original", original), ("corrected", corrected)]:
        text += "\nnamespace " + label + " {\n" + coefficient_block(source) + "\n}\n"
    text += '\n#undef calloc\n#undef free\nint main() {\n'
    text += 'std::printf("{\\\"longDoubleMantissaBits\\\":%d,\\\"longDoubleBytes\\\":%zu,\\\"coefficients\\\":{",LDBL_MANT_DIG,sizeof(ldouble));\n'
    macros = active_macros(original)
    expressions = {name: name for name in sorted(macros)}
    for method in ("rkf", "pd"):
        for i, expr in enumerate(tableau(original, method, True)["expressions"]["error"]):
            expressions[method + "Error" + str(i)] = expr
    for i, (name, expr) in enumerate(expressions.items()):
        text += '{double x=' + expr + '; uint64_t bits; std::memcpy(&bits,&x,8);'
        text += 'std::printf("' + (',' if i else '') + '\\\"' + name + '\\\":\\\"%016llx\\\"",(unsigned long long)bits);}\n'
    text += 'std::printf("},\\\"cases\\\":["); bool comma=false;\n'
    for label in ("original", "corrected"):
        for method, function in [("rkf", "take_rk_stepl"), ("pd", "take_pd89_step")]:
            cexprs = tableau(original if label == "original" else corrected, method, True)["expressions"]["cIncludingOutput"][:-1]
            text += "{ const ldouble roots[]={" + ",".join(cexprs) + "}; qcount=sizeof(roots)/sizeof(*roots); std::memcpy(qroots,roots,sizeof(roots)); }\n"
            text += '''
for(equation=0;equation<=11;equation++) for(int power=0;power<=4;power++) {
  ldouble input[6]={}, output[6]={}; ELEMENTS ref={0};
  if(equation==9) input[0]=.5;
  if(equation==10) input[0]=.125;
  ldouble h=1.; for(int j=0;j<power;j++) h*=.5;
  allocations=releases=0;
  ldouble error=''' + label + "::" + function + '''(0.,&ref,input,output,6,h);
  if(comma) std::printf(","); comma=true;
  std::printf("{\\\"variant\\\":\\\"''' + label + '''\\\",\\\"method\\\":\\\"''' + method + '''\\\",\\\"equation\\\":%d,\\\"stepPower\\\":%d,\\\"allocations\\\":%u,\\\"frees\\\":%u,\\\"valueBits\\\":",equation,power,allocations,releases);
  print_bits(output[0]); std::printf(",\\\"errorBits\\\":"); print_bits(error); std::printf("}");
  clean_test_leaks();
}
'''
    return text + 'std::printf("]}\\n"); return 0; }\n'


def decode(bits: str, precision: int) -> Q:
    """Decode a finite numerical value exactly; Fraction identifies +0 and -0."""
    raw = int(bits, 16)
    if precision == 64:  # x87: explicit integer bit, 15-bit exponent, 10 meaningful bytes.
        significand = raw & ((1 << 64) - 1)
        exponent = (raw >> 64) & 0x7fff
        assert exponent != 0x7fff, "Nonfinite probe output"
        value = Q(significand) * Q(2) ** ((exponent or 1) - 16383 - 63)
        return -value if raw >> 79 else value
    exponent_bits, fraction_bits, bias = (11, 52, 1023) if precision == 53 else (15, 112, 16383)
    assert precision in (53, 113)
    fraction = raw & ((1 << fraction_bits) - 1)
    exponent = (raw >> fraction_bits) & ((1 << exponent_bits) - 1)
    assert exponent != (1 << exponent_bits) - 1, "Nonfinite probe output"
    if exponent:
        fraction += 1 << fraction_bits
    value = Q(fraction) * Q(2) ** ((exponent or 1) - bias - fraction_bits)
    return -value if raw >> (fraction_bits + exponent_bits) else value


def require_zero_counterexample(value: Q, error: Q) -> None:
    assert value == 0 and error == 0, "Invisible-RHS counterexample must have exactly zero value and norm"


def zero_check_negative_controls() -> list[dict]:
    tiny = decode("00000000000000000000000000000001", 113)
    assert tiny == Q(1, 2 ** 16494) and tiny > 0 and float(tiny) == 0
    results = []
    for label, value, error in [("tiny-nonzero-binary128-error-norm", Q(0), tiny),
                                 ("tiny-nonzero-binary128-state", tiny, Q(0))]:
        try:
            require_zero_counterexample(value, error)
        except AssertionError:
            results.append({"mutation": label, "rejected": True,
                            "rawNonzeroBits": "00000000000000000000000000000001",
                            "pythonFloatDisplay": float(tiny)})
        else:
            raise AssertionError("Exact zero gate accepted " + label)
    # Make the oracle's intentional zero-sign limitation executable and visible.
    assert decode("80000000000000000000000000000000", 113) == decode("00000000000000000000000000000000", 113)
    return results


def optimization_negative_controls() -> list[dict]:
    results = []
    for label, command, env in [
        ("python-O", [sys.executable, "-O", str(Path(__file__).resolve()), "--help"], dict(os.environ)),
        ("PYTHONOPTIMIZE", [sys.executable, str(Path(__file__).resolve()), "--help"], {**os.environ, "PYTHONOPTIMIZE": "1"}),
    ]:
        process = subprocess.run(command, env=env, cwd=ROOT, text=True, capture_output=True, timeout=20)
        assert process.returncode != 0 and "Integrator verification requires Python assertions" in process.stderr, label
        results.append({"mutation": label, "rejected": True, "returnCode": process.returncode})
    return results


def exact_scalar(tab: dict, equation: int, h: Q, precision: int | None) -> tuple[Q, Q]:
    """Independent operation-order interpreter for this prescribed zero-reference RHS.

    No libm sqrt model: the returned error is the signed pre-norm estimator.
    All selected nonzero values are normal, so normal-only RN is sufficient.
    """
    rn = (lambda x: round_binary(x, precision)) if precision else (lambda x: x)
    y = Q(1, 2) if equation == 9 else (Q(1, 8) if equation == 10 else Q(0))
    derivatives = []
    for i, row in enumerate(tab["A"]):
        acc = Q(0)
        for j in range(i):
            acc = rn(acc + rn(row[j] * derivatives[j]))
        stage = rn(rn(acc * h) + y) if i else y
        time = rn(h * tab["c"][i])
        if equation <= 8:
            value = Q(1)
            for _ in range(equation):
                value = rn(value * time)
        elif equation <= 10:
            value = stage if equation == 9 else rn(stage * stage)
        else:
            value = Q(1)
            for c in tab["c"]:
                difference = rn(time - c)
                value = rn(value * rn(difference * difference))
        derivatives.append(value)
    acc, error = Q(0), Q(0)
    for b, e, value in zip(tab["b"], tab["e"], derivatives):
        acc = rn(acc + rn(b * value))
        error = rn(error + rn(e * value))
    return rn(rn(acc * h) + y), error * h


def execute(command: list[str], env: dict[str, str]) -> str:
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise RuntimeError(" ".join(command) + "\n" + result.stdout + result.stderr)
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, default=ROOT / ".wasm-engine/sources")
    parser.add_argument("--sdk", type=Path, default=ROOT / ".wasm-toolchain")
    parser.add_argument("--output", type=Path, default=HERE / "evidence/compiled.json")
    args = parser.parse_args()
    negative_controls = zero_check_negative_controls()
    optimization_controls = optimization_negative_controls()
    original, corrected, contract = sources(args.sources)
    work = ROOT / ".cache/integrator-verification"
    work.mkdir(parents=True, exist_ok=True)
    source = work / "integrator-probe.cpp"
    generated = harness(original, corrected)
    source.write_text(generated)
    env = {k: v for k, v in os.environ.items() if k not in {"EMCC_CFLAGS", "CFLAGS", "CXXFLAGS", "CPPFLAGS", "LDFLAGS"}}
    sdk = args.sdk.resolve()
    env["EM_CONFIG"] = str(sdk / ".emscripten")
    python = sorted((sdk / "python").glob("*/bin/python3"))
    empp = sdk / "upstream/emscripten/em++.py"
    em_command = [str(python[-1]), str(empp)] if python else [str(empp.with_suffix(""))]
    native = shutil.which("clang++") or "clang++"
    flags = ["-std=c++17", "-fno-fast-math", "-ffp-contract=off", str(source)]
    configurations = [("nativeO0", [native, "-O0"], False),
                      ("nativeO3", [native, "-O3"], False),
                      ("nativeSanitized", [native, "-O1", "-fsanitize=address,undefined", "-fno-sanitize-recover=all"], False),
                      ("wasmO0", [*em_command, "-O0"], True),
                      ("wasmO3", [*em_command, "-O3"], True)]
    runs = {}
    macros = active_macros(original)
    for label, compiler, wasm in configurations:
        output = work / (label + (".cjs" if wasm else ""))
        command = compiler + flags + (["-sENVIRONMENT=node", "-sEXIT_RUNTIME=1", "-sASSERTIONS=1"] if wasm else []) + ["-o", str(output)]
        execute(command, env)
        run = json.loads(execute((["node"] if wasm else []) + [str(output)], env))
        precision = run["longDoubleMantissaBits"]
        assert precision == 113 if wasm else precision in (53, 64, 113), "Unsupported long-double format"
        expressions = {name: name for name in macros}
        for method in ("rkf", "pd"):
            for i, expr in enumerate(tableau(original, method, True)["expressions"]["error"]):
                expressions[method + "Error" + str(i)] = expr
        for name, bits in run["coefficients"].items():
            assert decode(bits, 53) == evaluate(expressions[name], macros, True), (label, name)
        for case in run["cases"]:
            tab = tableau(original if case["variant"] == "original" else corrected, case["method"], True)
            expected, signed_error = exact_scalar(tab, case["equation"], Q(1, 2 ** case["stepPower"]), precision)
            actual = decode(case["valueBits"], precision)
            assert actual == expected, (label, case, qjson(actual - expected))
            assert case["allocations"] == (case["method"] == "pd")
            assert case["frees"] == (case["method"] == "pd" and case["variant"] == "corrected")
            exact_error = decode(case["errorBits"], precision)
            case["value"] = float(actual)
            case["error"] = float(exact_error)  # Display only; never an assertion oracle.
            case["signedErrorBeforeNorm"] = float(signed_error)
            if case["equation"] == 11 and case["stepPower"] == 0:
                require_zero_counterexample(actual, exact_error)
        run["coefficientExpressionsMatched"] = len(expressions)
        run["stepResultsExactFiniteEqualityModuloZeroSign"] = len(run["cases"])
        run["command"] = command
        runs[label] = run
        print(label + ": coefficients, all 240 scalar step results and allocation contracts pass", flush=True)
    report = {"schema": 1, "source": contract, "harnessSha256": sha(generated),
        "driverSha256": sha(Path(__file__).read_text()), "extractorSha256": sha((HERE / "core.py").read_text()),
        "nativeCompiler": execute([native, "--version"], env).splitlines()[0],
        "wasmCompiler": execute([*em_command, "--version"], env).splitlines()[0], "runs": runs,
        "zeroCheckNegativeControls": negative_controls,
        "optimizationNegativeControls": optimization_controls,
        "comparisonSemantics": "Exact finite numerical equality modulo zero sign: Fraction identifies +0 and -0. Raw bits are retained, but the oracle does not prove signed-zero preservation. Display floats never determine zero acceptance.",
        "scope": "Actual extracted function bodies with n_vals=n_orbit_params=6, initialized valid disjoint input/output buffers, successful allocation, zero reference, and prescribed RHS t^k (k=0..8), y, y^2, and q(t)=product(t-c_i)^2; only first state component active. 5 step lengths. y^2 starts at 1/8, y starts at 1/2, others start at 0. RHS/reference dependencies are test doubles. Original PD leak cleaned outside measured function after allocation accounting. Output bits independently interpreted with exact fractions and explicit RN operations; finite numerical equality is checked modulo zero sign. General estimator and sqrtl error-norm arithmetic remain unverified beyond the tested exact-zero controls; signed pre-norm values and norm bits are retained as evidence. Finite validation, not general compiler verification."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
