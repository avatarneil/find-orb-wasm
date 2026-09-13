#!/usr/bin/env python3
"""GPL-2.0-or-later. Compile proofs, audit axioms, replay EMPTY-kernel closures.

Nonzero status, errors, admissions, panics, missing roots, and unexpected axioms
all fail. No timeout/unknown/error becomes a passed obligation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

from bootstrap import ROOT, PIN, check_pins, installation_integrity, paths, proof_environment

HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROOF_FILES = [
    "verification/kernel/Foundations.lean",
    "verification/ephemeris/Recurrences.lean",
    "verification/ephemeris/Roundoff.lean",
    "verification/ephemeris/NumericalCertificates.lean",
    "verification/ephemeris/BridgeSupport.lean",
    "verification/ephemeris/RoundedDAG.lean",
    "verification/kernel/IntegratorCertificates.lean",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_success(code: int, output: str) -> None:
    if code != 0 or re.search(r"PANIC|sorryAx|declaration uses .sorry.|\berror(?:\(|:)", output):
        raise RuntimeError("Proof tool failed or logged an internal failure:\n" + output[-4000:])


def audit_axioms(output: str, expected: int) -> dict[str, list[str]]:
    result = {}
    # Lean wraps long axiom lists across lines. Each complete audit still has
    # an anchored header and closing bracket; malformed/partial audits cannot
    # satisfy the independently expected theorem count.
    pattern = re.compile(r"^'([^'\n]+)' (?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)[ \t]*$", re.M)
    for match in pattern.finditer(output):
        name = match[1]
        axioms = [x.strip() for x in (match[2] or "").split(",") if x.strip()]
        if name in result:
            raise RuntimeError("Duplicated theorem audit: " + name)
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError("Forbidden theorem axioms: " + str(unexpected))
        result[name] = axioms
    if len(result) != expected or expected < 1:
        raise RuntimeError(f"Missing/extra axiom audits: expected {expected}, found {len(result)}")
    return result


def execute(args: list[str], env: dict, log_path: Path, *, timeout: int = 900) -> tuple[int, str]:
    with log_path.open("w") as log:
        result = subprocess.run(args, cwd=ROOT, env=env, stdout=log,
                                stderr=subprocess.STDOUT, timeout=timeout)
    return result.returncode, log_path.read_text()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--foundations-only", action="store_true", help="Development smoke check only")
    args = parser.parse_args()
    if args.output is None:
        args.output = HERE / "evidence" / ("smoke-report.json" if args.foundations_only else "report.json")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    scope = "foundations-only smoke" if args.foundations_only else "complete research kernel suite"
    # Invalidate prior evidence before any prerequisite or compiler operation.
    args.output.write_text(json.dumps({"schema": 1, "scope": scope, "status": "incomplete",
                                      "passed": False, "startedAtUnix": time.time()}, indent=2) + "\n")
    if sys.flags.optimize:
        raise RuntimeError("Optimized Python is forbidden for proof checks")
    lean_root, mathlib, archive = paths()
    print("Checking pinned Lean release archive and installed contents", flush=True)
    integrity = installation_integrity(lean_root, archive)
    integrity_path = args.output.parent / "lean-installation.json"
    integrity_path.write_text(json.dumps(integrity, indent=2) + "\n")
    versions = check_pins(lean_root, mathlib)
    env = proof_environment(lean_root)
    lean = str(lean_root / "bin/lean")
    lake = str(lean_root / "bin/lake")
    search = subprocess.check_output([lake, "-d", str(mathlib), "env", "printenv", "LEAN_PATH"],
                                     env=env, text=True).strip()
    build = ROOT / ".cache/kernel-modules"
    build.mkdir(parents=True, exist_ok=True)
    evidence = args.output.parent
    evidence.mkdir(parents=True, exist_ok=True)
    logs = evidence / ("smoke-logs" if args.foundations_only else "logs")
    logs.mkdir(exist_ok=True)
    env["LEAN_PATH"] = str(build) + os.pathsep + search

    def compile_file(source: Path) -> tuple[str, str]:
        module = source.stem
        command = [lean, "--trust=0", "--root", str(source.parent), "-o", str(build / (module + ".olean")), str(source)]
        code, output = execute(command, env, logs / (module + ".compile.txt"))
        require_success(code, output)
        return module, output

    # The replay program is a small, reviewable adapter around raw kernel
    # addDeclCore. It is part of the trusted computing base, never a theorem.
    compile_file(HERE / "RawReplay.lean")
    compile_file(HERE / "Replay.lean")
    files = PROOF_FILES[:1] if args.foundations_only else PROOF_FILES
    report = {"schema": 1, "scope": scope,
              "toolchain": versions, "leanReleaseSHA256": digest(archive), "files": [],
              "installationIntegrity": {**{k: v for k, v in integrity.items() if k != "entries"},
                                        "manifestFile": integrity_path.name,
                                        "manifestFileSHA256": digest(integrity_path)},
              "allowedAxioms": sorted(ALLOWED_AXIOMS), "negativeControls": [],
              "replayImplementationSHA256": digest(HERE / "RawReplay.lean"),
              "replayDriverSHA256": digest(HERE / "Replay.lean"),
              "runnerSHA256": digest(Path(__file__)), "startedAtUnix": time.time()}
    for relative in files:
        source = ROOT / relative
        expected = len(re.findall(r"^#print axioms\s+", source.read_text(), re.M))
        print("Kernel compile + empty-environment replay: " + relative, flush=True)
        start = time.monotonic()
        module, output = compile_file(source)
        audits = audit_axioms(output, expected)
        command = [lean, "--run", str(HERE / "Replay.lean"), module, *audits]
        code, replay_output = execute(command, env, logs / (module + ".replay.txt"))
        require_success(code, replay_output)
        replay = json.loads(replay_output)
        if (not replay.get("passed") or replay.get("corrupt") or replay.get("forgedAxiom")
                or not replay.get("emptyInitialEnvironment") or not replay.get("canonicalSignaturesValidated")):
            raise RuntimeError("Invalid kernel replay result")
        if set(replay["theorems"]) != set(audits) or set(replay["axioms"]) - ALLOWED_AXIOMS:
            raise RuntimeError("Replayed theorem/axiom set mismatch")
        signatures = replay["canonicalSignatures"]
        expected_signatures = ALLOWED_AXIOMS | {"Eq", "Eq.refl", "Eq.rec", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"}
        if len(signatures) != len(expected_signatures) or {s["name"] for s in signatures} != expected_signatures:
            raise RuntimeError("Incomplete canonical core signature validation")
        if Path(replay["canonicalCorePath"]).resolve() != (lean_root / "lib/lean").resolve():
            raise RuntimeError("Canonical core was loaded outside the verified release")
        replay["canonicalSignaturesSHA256"] = hashlib.sha256(
            json.dumps(signatures, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        report["files"].append({"path": relative, "sha256": digest(source), "axiomAudits": audits,
                                "kernelReplay": replay, "elapsedSeconds": time.monotonic() - start})

    def reject(name: str, command: list[str], expected_message: str) -> None:
        code, output = execute(command, env, logs / ("negative-" + name + ".txt"))
        if code == 0 or expected_message not in output or "PANIC" in output:
            raise RuntimeError("Negative proof control failed for the wrong reason: " + name + "\n" + output[-2000:])
        report["negativeControls"].append({"name": name, "rejected": True,
                                            "exitCode": code, "expectedMessage": expected_message})

    reject("corrupted-proof", [lean, "--run", str(HERE / "Replay.lean"), "--corrupt", "Foundations",
                                "FindOrb.global_error_bound"], "type mismatch")
    reject("forged-allowed-axiom", [lean, "--run", str(HERE / "Replay.lean"), "--forge-axiom", "Foundations",
                                   "FindOrb.global_error_bound"], "Canonical axiom signature mismatch")
    forbidden = build / "RejectedAxiom.lean"
    forbidden.write_text("axiom untrusted : False\ntheorem forged : False := untrusted\n")
    compile_file(forbidden)
    reject("custom-axiom", [lean, "--run", str(HERE / "Replay.lean"), "RejectedAxiom", "forged"], "Forbidden axiom")
    reject("missing-theorem", [lean, "--run", str(HERE / "Replay.lean"), "Foundations", "FindOrb.absent"], "Required theorem is absent")
    try:
        require_success(0, "PANIC: recoverable runtime failure\n{\"passed\":true}")
    except RuntimeError:
        report["negativeControls"].append({"name": "panic-with-zero-exit", "rejected": True})
    else:
        raise RuntimeError("A recovered runtime panic was accepted")
    try:
        audit_axioms("'bad' depends on axioms: [sorryAx]", 1)
    except RuntimeError:
        report["negativeControls"].append({"name": "admitted-proof", "rejected": True})
    else:
        raise RuntimeError("An admitted proof was accepted")
    report["theoremCount"] = sum(len(item["axiomAudits"]) for item in report["files"])
    report["completedAtUnix"] = time.time()
    report["status"] = "passed"
    report["passed"] = True
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {report['theoremCount']} theorem audits, raw kernel closure replay, and {len(report['negativeControls'])} negative controls", flush=True)


if __name__ == "__main__":
    main()
