"""GPL-2.0-or-later. Pinned, clean proof-tool invocation for ephemeris checks."""
from __future__ import annotations
import importlib.util
import os
import re
import subprocess
from pathlib import Path
from source import ROOT


def require_success(code: int, output: str):
    if code != 0 or re.search(r'PANIC|sorryAx|declaration uses[^\n]*sorry|\berror(?:\(|:)', output, re.I):
        raise RuntimeError('Proof tool failed or logged an internal failure:\n' + output[-4000:])


def require_rejection(code: int, output: str, expected: tuple[str, ...]):
    if code == 0 or re.search(r'PANIC', output, re.I) or any(text not in output for text in expected):
        raise RuntimeError('Negative proof control failed for the wrong reason:\n' + output[-4000:])


def proof_tools(lean_root: Path, mathlib: Path, modules: Path):
    # Use the central toolchain lock, dependency checks, and environment policy.
    filename = ROOT / 'verification/kernel/bootstrap.py'
    spec = importlib.util.spec_from_file_location('_findorb_kernel_bootstrap', filename)
    if spec is None or spec.loader is None:
        raise RuntimeError('Cannot load pinned proof-tool bootstrap')
    bootstrap = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bootstrap)
    versions = bootstrap.check_pins(lean_root, mathlib)
    env = bootstrap.proof_environment(lean_root)
    lean, lake = lean_root / 'bin/lean', lean_root / 'bin/lake'
    result = subprocess.run([str(lean), '--version'], env=env, text=True,
      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    require_success(result.returncode, result.stdout)
    versions['leanVersion'] = result.stdout.strip()
    result = subprocess.run([str(lake), '-d', str(mathlib), 'env', 'printenv', 'LEAN_PATH'],
      env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    require_success(result.returncode, result.stdout)
    search = result.stdout.strip()
    if not search or '\n' in search:
        raise RuntimeError('Invalid pinned Lean dependency search path')
    env['LEAN_PATH'] = str(modules) + os.pathsep + search
    return {'lean': str(lean), 'env': env, 'versions': versions}
