"""GPL-2.0-or-later. Fail-closed frontend for the pinned interp implementation.

This is a deliberately narrow frontend, not a C++ parser. Whole-function hashes
freeze control flow; the listed arithmetic expressions are parsed, retaining
C++ left associativity. Any source or syntax change requires a new review.
"""
from __future__ import annotations
import ast
import hashlib
import json
import re
import sys
from pathlib import Path

if sys.flags.optimize:
    raise RuntimeError('Optimized Python is forbidden for ephemeris verification')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / '.wasm-engine/sources/jpl_eph'


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def function(text: str, name: str) -> str:
    pattern = rf'(?:static void |int DLL_FUNC |void \* DLL_FUNC ){name}\s*\([^;{{}}]*\)\s*\{{'
    found = list(re.finditer(pattern, text))
    if len(found) != 1:
        raise ValueError('Ambiguous function definition: ' + name)
    begin, end = found[0].start(), found[0].end()
    depth = 1
    while depth and end < len(text):
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    if depth:
        raise ValueError('Unterminated function: ' + name)
    return text[begin:end]


def arithmetic(text: str, replacements: dict[str, str]) -> list | str:
    for old, new in sorted(replacements.items(), key=lambda item: -len(item[0])):
        text = text.replace(old, new)
    def visit(node):
        if isinstance(node, ast.Name) and node.id in set(replacements.values()):
            return node.id
        if isinstance(node, ast.Constant) and node.value in (0, 1, 2, 4):
            return ['constant', int(node.value)]
        if isinstance(node, ast.BinOp) and type(node.op) in (ast.Add, ast.Sub, ast.Mult, ast.Div):
            return [{ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul', ast.Div: 'div'}[type(node.op)], visit(node.left), visit(node.right)]
        raise ValueError('Unsupported C arithmetic syntax: ' + ast.dump(node))
    return visit(ast.parse(text.strip(), mode='eval').body)


def checked(source: Path = SOURCE) -> tuple[dict, dict]:
    contract = json.loads((HERE / 'source-contract.json').read_text())
    cpp = (source / 'jpleph.cpp').read_text()
    for name, expected in contract['functions'].items():
        if digest(function(cpp, name).encode()) != expected:
            raise ValueError('Source contract changed: ' + name)
    if digest((source / 'jpl_int.h').read_bytes()) != contract['headerSHA256']:
        raise ValueError('Interpolation memory layout changed')
    body = function(cpp, 'interp')
    expressions = {}
    for name, entry in contract['expressions'].items():
        # Whitespace is flexible inside the reviewed expression; statement
        # count and whole-function hashes still reject all control-flow edits.
        compact = re.sub(r'\s+', ' ', body)
        if compact.count(entry['source']) != 1:
            raise ValueError('Source arithmetic statement missing: ' + name)
        expressions[name] = arithmetic(entry['source'], entry['replace'])
    return expressions, contract
