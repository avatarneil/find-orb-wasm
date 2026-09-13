"""GPL-2.0-or-later. Fail-closed extraction and exact C coefficient semantics."""
from __future__ import annotations

import ast
import hashlib
import re
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

if sys.flags.optimize:
    raise RuntimeError("Integrator verification requires Python assertions; -O/-OO and PYTHONOPTIMIZE are unsupported")

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PIN = "9cc932997837c5ab994fbf015db59f5d0da852e5"
ORIGINAL_SHA256 = "bdb2104b973a575ccdfbc707232644db7ddca9ddde793c780ffc3ea3881bbb2c"
OLD_TIMES = """   const ldouble avals[N_EVALS_PLUS_ONE] = { 0, A_1, A_2, A_3, A_4, A_5,
             A_6, A_7, A_8, A_9, A_10, A_11, A_12, A_13 };"""
NEW_TIMES = """   const ldouble avals[N_EVALS_PLUS_ONE] = { A_1, A_2, A_3, A_4, A_5,
             A_6, A_7, A_8, A_9, A_10, A_11, A_12, A_13, 1. };"""


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def definition(text: str, name: str) -> str:
    matches = list(re.finditer(r"^ldouble " + re.escape(name) + r"\([^;{]*\)\s*\{", text, re.M))
    if len(matches) != 1:
        raise ValueError("Expected exactly one definition: " + name)
    start, end = matches[0].start(), matches[0].end()
    depth = 1
    while depth:
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    return text[start:end]


def corrected_source(original: str) -> str:
    if sha(original) != ORIGINAL_SHA256:
        raise ValueError("Unreviewed original runge.cpp")
    pd = definition(original, "take_pd89_step")
    assert pd.count(OLD_TIMES) == 1
    ret = "   return( sqrtl( rval * step * step));"
    assert pd.count(ret) == 1
    fixed = pd.replace(OLD_TIMES, NEW_TIMES).replace(ret, "   free( ivals[0]);\n" + ret)
    return original.replace(pd, fixed)


def sources(source_root: Path) -> tuple[str, str, dict]:
    repo = source_root / "find_orb"
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if head != PIN:
        raise ValueError("Unreviewed Find_Orb revision: " + head)
    original = subprocess.check_output(["git", "show", PIN + ":runge.cpp"], cwd=repo).decode()
    if sha(original) != ORIGINAL_SHA256:
        raise ValueError("Pinned original runge.cpp hash mismatch")
    corrected = corrected_source(original)
    current = (repo / "runge.cpp").read_text()
    if sha(current) not in {sha(original), sha(corrected)}:
        raise ValueError("Current runge.cpp has unreviewed changes: " + sha(current))
    return original, corrected, {"repository": "https://github.com/Bill-Gray/find_orb",
        "commit": PIN, "originalSha256": sha(original), "correctedSha256": sha(corrected),
        "currentSha256": sha(current), "currentVariant": "original" if current == original else "corrected"}


def coefficient_block(text: str) -> str:
    return text[text.index("#define B_2_1"):text.index("#define W1  ")]


def active_macros(text: str) -> dict[str, str]:
    block = coefficient_block(text)
    marker = "#ifdef ORIGINAL_FEHLBERG_CONSTANTS"
    assert "#define ORIGINAL_FEHLBERG_CONSTANTS\n" in block
    before, conditional = block.split(marker)
    active, rest = conditional.split("#else", 1)
    _, after = rest.split("#endif", 1)
    block = before + active + after
    macros = dict(re.findall(r"^#define\s+((?:B_|CHAT_|C_|A_|RKF_)\w+)\s+([^\n]+)", block, re.M))
    if len(macros) != 150:
        # Deliberately a fixed contract, not silently tolerant of source changes.
        raise ValueError("Unexpected coefficient macro count: " + str(len(macros)))
    return macros


def round_binary(value: Q, precision: int) -> Q:
    """Exact IEEE round-to-nearest, ties-to-even for finite normal results.

    Coefficients are bounded away from overflow/underflow. This routine does not
    claim to model subnormal rounding, NaNs, infinities or dynamic rounding modes.
    """
    if not value:
        return Q(0)
    sign = -1 if value < 0 else 1
    value = abs(value)
    exponent = value.numerator.bit_length() - value.denominator.bit_length()
    if value < Q(2) ** exponent:
        exponent -= 1
    minimum, maximum = (-1022, 1023) if precision == 53 else (-16382, 16383)
    if not minimum <= exponent <= maximum:
        raise ValueError("Normal-only rounding interpreter used outside its supported range")
    scale = Q(2) ** (exponent - precision + 1)
    ratio = value / scale
    integer, remainder = divmod(ratio.numerator, ratio.denominator)
    if 2 * remainder > ratio.denominator or (2 * remainder == ratio.denominator and integer % 2):
        integer += 1
    result = sign * integer * scale
    if abs(result) >= Q(2) ** (maximum + 1):
        raise ValueError("Rounding interpreter overflow")
    return result


def expand(expression: str, macros: dict[str, str]) -> str:
    for _ in range(10):
        identifiers = re.findall(r"\b[A-Za-z_]\w*\b", expression)
        if not identifiers:
            return expression
        if any(name not in macros for name in identifiers):
            raise ValueError("Unsupported C expression: " + expression)
        # C macros are textual substitutions: do NOT add parentheses here.
        expression = re.sub(r"\b[A-Za-z_]\w*\b", lambda m: macros[m.group()], expression)
    raise ValueError("Macro recursion")


def evaluate(expression: str, macros: dict[str, str], stored: bool) -> Q:
    expanded = expand(expression, macros).strip()
    syntax = ast.parse(expanded, mode="eval")

    def visit(node: ast.AST) -> tuple[Q, bool]:
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            spelling = ast.get_source_segment(expanded, node)
            assert spelling is not None
            floating = any(x in spelling for x in ".eE")
            value = Q(spelling)
            return (round_binary(value, 53) if stored and floating else value), floating
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value, floating = visit(node.operand)
            return (-value if isinstance(node.op, ast.USub) else value), floating
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div)):
            left, lf = visit(node.left)
            right, rf = visit(node.right)
            floating = lf or rf
            if isinstance(node.op, ast.Add):
                value = left + right
            elif isinstance(node.op, ast.Sub):
                value = left - right
            elif isinstance(node.op, ast.Mult):
                value = left * right
            else:
                value = left / right
                if not floating:
                    value = Q(int(value))  # C integer division truncates toward zero.
            return (round_binary(value, 53) if stored and floating else value), floating
        raise ValueError("Unsupported C syntax: " + ast.dump(node))

    return visit(syntax.body)[0]


def initializer(function: str, name: str) -> list[str]:
    matches = re.findall(r"\b" + name + r"\[[^]]+\]\s*=\s*\{([^}]+)\}", function)
    if len(matches) != 1:
        raise ValueError("Expected initializer: " + name)
    return [item.strip() for item in matches[0].split(",")]


def tableau(text: str, method: str, stored: bool) -> dict:
    macros = active_macros(text)
    name, n = ("take_rk_stepl", 6) if method == "rkf" else ("take_pd89_step", 13)
    function = definition(text, name)
    bexprs = initializer(function, "bvals")
    cexprs = initializer(function, "avals")
    eexprs = initializer(function, "err_coeffs" if method == "rkf" else "err_coeff")
    assert len(bexprs) == n * (n + 1) // 2 and len(cexprs) == n + 1 and len(eexprs) == n
    ev = lambda x: evaluate(x, macros, stored)
    values = list(map(ev, bexprs))
    A, index = [], 0
    for i in range(n):
        A.append(values[index:index + i] + [Q(0)] * (n - i))
        index += i
    b = values[index:]
    low_names = [("RKF_C" if method == "rkf" else "C_") + str(i + 1) for i in range(n)]
    return {"method": method, "arithmetic": "binary64-constant-expressions" if stored else "exact-decimal-rational",
        "A": A, "b": b, "bEmbedded": list(map(ev, low_names)),
        "c": list(map(ev, cexprs[:-1])), "outputTime": ev(cexprs[-1]), "e": list(map(ev, eexprs)),
        "expressions": {"AandB": bexprs, "cIncludingOutput": cexprs, "embedded": low_names, "error": eexprs},
        "functionSha256": sha(function)}


def qjson(value: Q) -> dict:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator), "approx": float(value)}
