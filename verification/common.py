"""GPL-2.0-or-later. Source anchoring shared by proof and compiler probes."""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def function_source(text: str, name: str) -> str:
    """Extract an actual definition (never a forward declaration), fail closed."""
    pattern = rf"(?:^|\n)(?:double DLL_FUNC |int DLL_FUNC |void DLL_FUNC |void \*){re.escape(name)}\s*\([^;{{}}]*\)\s*\{{"
    matches = list(re.finditer(pattern, text))
    if len(matches) != 1:
        raise ValueError(f"Expected one definition of {name}, found {len(matches)}")
    start = matches[0].start()
    brace = matches[0].end() - 1
    depth = 1
    end = brace + 1
    while depth and end < len(text):
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    if depth:
        raise ValueError(f"Unterminated {name}")
    return text[start:end].strip()


def checked_sources(source_root: Path) -> tuple[dict[str, str], dict]:
    contracts = json.loads((ROOT / "verification/source-contracts.json").read_text())
    functions = {}
    for name, contract in contracts.items():
        repo = source_root / contract["repository"]
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        if commit != contract["commit"]:
            raise ValueError(f"Unreviewed upstream revision for {name}: {commit}")
        actual = function_source((repo / contract["file"]).read_text(), name)
        digest = hashlib.sha256(actual.encode()).hexdigest()
        if digest != contract["sha256"]:
            raise ValueError(f"Unreviewed source change for {name}; update proofs before contract")
        functions[name] = actual
    return functions, contracts
