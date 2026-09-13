#!/usr/bin/env python3
"""GPL-2.0-or-later. Exact rooted-tree, time, estimator and rounding analysis."""
from __future__ import annotations

import argparse
import copy
import json
import math
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

from core import ROOT, HERE, qjson, round_binary, sha, sources, tableau


@lru_cache(None)
def size(tree: tuple) -> int:
    return 1 + sum(map(size, tree))


@lru_cache(None)
def gamma(tree: tuple) -> int:
    return size(tree) * math.prod(gamma(child) for child in tree)


@lru_cache(None)
def symmetry(tree: tuple) -> int:
    return math.prod(symmetry(child) for child in tree) * math.prod(
        math.factorial(tree.count(child)) for child in set(tree))


@lru_cache(None)
def trees(order: int) -> tuple[tuple, ...]:
    if order == 1:
        return ((),)
    candidates = tuple(tree for n in range(1, order) for tree in trees(n))
    result = []

    def multisets(remaining: int, start: int, children: tuple) -> None:
        if not remaining:
            result.append(children)
            return
        for index in range(start, len(candidates)):
            tree = candidates[index]
            if size(tree) > remaining:
                break
            multisets(remaining - size(tree), index, children + (tree,))

    multisets(order - 1, 0, ())
    return tuple(result)


def notation(tree: tuple) -> str:
    return "[" + "".join(map(notation, tree)) + "]"


def conditions(tab: dict, maximum: int) -> tuple[list[dict], dict]:
    A, n = tab["A"], len(tab["b"])

    @lru_cache(None)
    def stage(tree: tuple) -> tuple[Q, ...]:
        if not tree:
            return (Q(1),) * n
        return tuple(math.prod(sum(A[i][j] * stage(child)[j] for j in range(i))
                               for child in tree) for i in range(n))

    records, summary = [], {}
    for order in range(1, maximum + 1):
        entries = []
        for tree in trees(order):
            phi = stage(tree)
            residuals = {label: sum(weight * value for weight, value in zip(tab[key], phi))
                          - (Q(0) if label == "estimator" else Q(1, gamma(tree)))
                         for label, key in [("advance", "b"), ("embedded", "bEmbedded"), ("estimator", "e")]}
            entry = {"tree": notation(tree), "order": order, "gamma": gamma(tree), "symmetry": symmetry(tree),
                     "residuals": {key: qjson(value) for key, value in residuals.items()}}
            if tab["method"] == "rkf" and tab["arithmetic"] == "exact-decimal-rational" and order <= 6:
                entry["stageElementaryWeights"] = [qjson(value) for value in phi]
            entries.append(entry)
        summary[str(order)] = {"trees": len(entries)}
        for label in ("advance", "embedded", "estimator"):
            values = [Q(int(item["residuals"][label]["numerator"]), int(item["residuals"][label]["denominator"])) for item in entries]
            largest = max(range(len(values)), key=lambda index: abs(values[index]))
            summary[str(order)][label] = {"exactZeros": values.count(Q(0)), "maxAbsoluteResidual": qjson(abs(values[largest])),
                "worstTree": entries[largest]["tree"]}
        records.extend(entries)
    return records, summary


def polynomial_multiply(left: list[Q], right: list[Q]) -> list[Q]:
    result = [Q(0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return result


def invisible_rhs(tab: dict) -> dict:
    """Polynomial vanishes at every actual stored derivative evaluation time."""
    coefficients = [Q(1)]
    for c in tab["c"]:
        assert 0 <= c <= 1
        coefficients = polynomial_multiply(coefficients, [c * c, -2 * c, Q(1)])
    integral = sum(value / (i + 1) for i, value in enumerate(coefficients))
    assert integral > 0
    for c in tab["c"]:
        assert sum(value * c ** i for i, value in enumerate(coefficients)) == 0
    return {"definition": "q(t)=product_i (t-c_i)^2, with actual stored binary64 stage abscissae",
            "degree": len(coefficients) - 1, "roots": [qjson(c) for c in tab["c"]],
            "ascendingPowerCoefficients": [qjson(value) for value in coefficients],
            "integralZeroToOne": qjson(integral), "computedStateAndEstimator": 0,
            "rhsSupBoundOnUnitInterval": 1, "rhsTimeLipschitzBoundOnUnitInterval": 2 * len(tab["c"]),
            "scope": "Scalar smooth nonautonomous ODE y'=q(t), y(0)=0, h=1, zero reference. All sampled RHS values vanish exactly, including binary128 compiled multiplication form, but integral is strictly positive. Thus no finite multiple of embedded estimate universally bounds true local error."}


def linear_ode_envelope(tab: dict) -> dict:
    """One-step bound versus the exact ODE solution, for y'=y, |y0|<=1/2.

    The exact stored-tableau stability polynomial is computed by nilpotent
    powers of A. Its difference from exp(h) is bounded using exact Taylor
    coefficients and exp(H)<=1/(1-H). Roundoff uses the actual sequential sums.
    """
    A, b, n = tab["A"], tab["b"], len(tab["b"])
    H, Y, u, beta = Q(1, 16), Q(1, 2), Q(1, 2 ** 113), Q(1, 2 ** 200)
    rb = lambda x: u * x + beta
    power, polynomial = [Q(1)] * n, [Q(1)]
    for _ in range(n):
        polynomial.append(sum(x * y for x, y in zip(b, power)))
        power = [sum(A[i][j] * power[j] for j in range(i)) for i in range(n)]
    assert power == [0] * n  # Strictly triangular A is nilpotent.
    coefficient_bound = Y * sum(abs(value - Q(1, math.factorial(k))) * H ** k
                                for k, value in enumerate(polynomial))
    taylor_tail = Y * H ** (n + 1) / math.factorial(n + 1) / (1 - H)
    magnitudes, errors = [Y], [Q(0)]

    def stage(weights: list[Q]) -> tuple[Q, Q]:
        magnitude, rounding, propagated = Q(0), Q(0), Q(0)
        for weight, bound, error in zip(weights, magnitudes, errors):
            product = abs(weight) * bound
            multiply_error = rb(product)
            add_error = rb(magnitude + product + multiply_error)
            magnitude += product + multiply_error + add_error
            rounding += multiply_error + add_error
            propagated += abs(weight) * error
        multiply_error = rb(H * magnitude)
        add_error = rb(Y + H * magnitude + multiply_error)
        return Y + H * magnitude + multiply_error + add_error, H * (rounding + propagated) + multiply_error + add_error

    for i in range(1, n):
        magnitude, error = stage(A[i][:i])
        magnitudes.append(magnitude)
        errors.append(error)
    output_magnitude, rounding = stage(b)
    total = coefficient_bound + taylor_tail + rounding
    assert max(magnitudes + [output_magnitude]) < 100
    return {"rhs": "y'=y", "reference": "zero", "domain": "t0=0; any exactly represented |h|<=1/16 and |y0|<=1/2, six-component state with only first component active",
        "stabilityPolynomialAscendingCoefficients": [qjson(x) for x in polynomial],
        "maxAbsStageBounds": [qjson(x) for x in magnitudes],
        "maxAbsStageRoundingDiscrepancy": [qjson(x) for x in errors],
        "finiteTaylorCoefficientDiscrepancyBound": qjson(coefficient_bound),
        "exponentialTaylorTailBound": qjson(taylor_tail), "arithmeticRoundingBound": qjson(rounding),
        "oneStepErrorAgainstExactOdeSolutionBound": qjson(total),
        "assumptions": "Binary128 RN, gradual underflow, no fast-math/contraction; prescribed linear RHS is exact copying of stage coordinate; zero reference; common exactly represented inputs. Source expression order preserved.",
        "proofStatus": "Exact rational certificate from triangle inequalities and exponential Taylor remainder, with Python/Fraction trusted; does not validate the astronomical RHS, nonzero Encke reference, multi-step global error or adaptive tolerance."}


def envelope(actual: dict, target: dict) -> dict:
    """Exact rational propagation of a conservative componentwise error theorem.

    Reference=0. Same exactly represented t0,y0,h are used by both methods.
    Actual RHS values have norm <= M+eta, and absolute evaluation error <= eta.
    Exact RHS is (Lt,Ly)-Lipschitz throughout a common domain containing stages.
    Every arithmetic operation uses binary128 RN with gradual underflow.
    fl(z) differs by <= u*abs(z)+alpha, assuming finite intermediates.
    """
    u, alpha = Q(1, 2 ** 113), Q(1, 2 ** 16495)
    H, T, Y, M, Lt, Ly, eta = Q(1, 16), Q(1), Q(1), Q(1), Q(1), Q(1), Q(1, 2 ** 100)
    F = M + eta
    # Extremely large subnormal denominators obscure review. Use a coarser exact
    # upper bound beta >= half-min-subnormal at every rounding; still rigorous.
    beta = Q(1, 2 ** 200)
    assert alpha <= beta
    rb = lambda bound: u * bound + beta

    def rounded_sum_error(weights: list[Q]) -> tuple[Q, Q]:
        magnitude, error = Q(0), Q(0)
        for weight in weights:
            product = abs(weight) * F
            product_error = rb(product)
            addition_error = rb(magnitude + product + product_error)
            error += product_error + addition_error
            magnitude += product + product_error + addition_error
        return magnitude, error

    stage_errors, derivative_errors, certificates = [], [], []
    for i, weights in enumerate(actual["A"]):
        time_multiply_error = rb(H * abs(actual["c"][i]))
        time_error = H * abs(actual["c"][i] - target["c"][i]) + time_multiply_error + rb(T + H * abs(actual["c"][i]) + time_multiply_error)
        if not i:
            state_error, magnitude = Q(0), Y
        else:
            sum_magnitude, sum_rounding = rounded_sum_error(weights[:i])
            multiply_rounding = rb(H * sum_magnitude)
            add_rounding = rb(Y + H * sum_magnitude + multiply_rounding)
            coefficient = M * sum(abs(weights[j] - target["A"][i][j]) for j in range(i))
            propagated = sum(abs(weights[j]) * derivative_errors[j] for j in range(i))
            state_error = H * (coefficient + propagated + sum_rounding) + multiply_rounding + add_rounding
            magnitude = Y + H * sum_magnitude + multiply_rounding + add_rounding
        derivative_error = Lt * time_error + Ly * state_error + eta
        stage_errors.append(state_error)
        derivative_errors.append(derivative_error)
        certificates.append({"stage": i, "timeError": qjson(time_error), "stateError": qjson(state_error),
                             "derivativeError": qjson(derivative_error), "stateMagnitude": qjson(magnitude)})
    sum_magnitude, sum_rounding = rounded_sum_error(actual["b"])
    multiply_rounding = rb(H * sum_magnitude)
    add_rounding = rb(Y + H * sum_magnitude + multiply_rounding)
    coefficient = M * sum(abs(x - y) for x, y in zip(actual["b"], target["b"]))
    propagated = sum(abs(b) * error for b, error in zip(actual["b"], derivative_errors))
    result = H * (coefficient + propagated + sum_rounding) + multiply_rounding + add_rounding
    return {"unitRoundoff": qjson(u), "roundoffAbsoluteSlack": qjson(beta),
        "domain": {"maxAbsStep": "1/16", "maxAbsInitialTime": 1, "maxNormInitialState": 1,
                   "maxNormExactRhs": 1, "timeLipschitzConstant": 1, "stateLipschitzConstant": 1,
                   "maxNormRhsEvaluationError": "2^-100", "reference": "identically zero"},
        "target": "One exact-arithmetic step using the corrected exact decimal/rational tableau; not the exact ODE solution",
        "assumptions": ["Exactly represented common h,t0,y0; dimension-independent infinity norm",
                        "All actual and ideal stages lie in a common domain where stated RHS bounds hold",
                        "Binary128 round-to-nearest ties-to-even, no contraction/fast-math/flush-to-zero",
                        "No overflow; certified stage magnitude bounds are tiny relative to binary128 range",
                        "The RHS evaluation-error hypothesis is external, not proved for Find_Orb force calculations",
                        "No nonzero Encke/reference subtraction, no accepted-step controller or global accumulation model"],
        "stageCertificates": certificates, "oneStepImplementationDiscrepancyBound": qjson(result),
        "proofStatus": "Exact rational implementation of a triangle-inequality/Lipschitz induction; Python and Fraction are trusted here. This is not a Lean kernel theorem or a formal proof of the whole solver."}


def summarize_tableau(tab: dict, maximum: int) -> dict:
    records, summary = conditions(tab, maximum)
    row_residuals = [c - sum(row) for c, row in zip(tab["c"], tab["A"])]
    error_storage = [e - (b - lo) for e, b, lo in zip(tab["e"], tab["b"], tab["bEmbedded"])]
    moments = {str(k): qjson(sum(b * c ** k for b, c in zip(tab["b"], tab["c"])) - Q(1, k + 1))
               for k in range(maximum)}
    return {"functionSha256": tab["functionSha256"], "coefficientSemantics": tab["arithmetic"],
        "tableau": {key: [[qjson(x) for x in row] for row in value] if key == "A" else [qjson(x) for x in value]
                    for key, value in tab.items() if key in {"A", "b", "bEmbedded", "c", "e"}},
        "expressions": tab["expressions"], "outputTime": qjson(tab["outputTime"]),
        "stageTimeMinusRowSum": [qjson(x) for x in row_residuals],
        "storedErrorMinusDifferenceOfStoredWeights": [qjson(x) for x in error_storage],
        "nonautonomousPolynomialMomentResiduals": moments, "autonomousRootedTreeSummary": summary,
        "autonomousRootedTreeConditions": records}


def mutations(original: str, corrected: str) -> list[dict]:
    # These check distinct gates, not merely the source hash gate.
    good = tableau(corrected, "rkf", False)
    mutated = copy.deepcopy(good)
    mutated["b"][0] += Q(1, 10 ** 8)
    assert sum(mutated["b"]) != 1
    bad_time = copy.deepcopy(good)
    bad_time["c"][1] = 0
    assert any(c != sum(row) for c, row in zip(bad_time["c"], bad_time["A"]))
    bad_stage = copy.deepcopy(good)
    bad_stage["A"][4][2] += Q(1, 1000)
    _, bad_conditions = conditions(bad_stage, 5)
    assert bad_conditions["2"]["advance"]["maxAbsoluteResidual"]["numerator"] != "0"
    stored = tableau(corrected, "pd", True)
    assert any(e != b - lo for e, b, lo in zip(stored["e"], stored["b"], stored["bEmbedded"]))
    original_pd = tableau(original, "pd", True)
    assert abs(sum(b * c for b, c in zip(original_pd["b"], original_pd["c"])) - Q(1, 2)) > Q(1, 10)
    try:
        from core import corrected_source
        corrected_source(original.replace("#define B_2_1", "#define X_2_1", 1))
    except ValueError:
        pass
    else:
        raise AssertionError("Source mutation passed")
    # Rational RN tie tests catch accidental host-float or ties-away semantics.
    assert round_binary(Q(1) + Q(1, 2 ** 53), 53) == 1
    assert round_binary(Q(1) + Q(3, 2 ** 53), 53) == 1 + Q(1, 2 ** 51)
    return [{"mutation": label, "rejected": True} for label in (
        "weight perturbation fails consistency", "stage-time shift fails c=A1", "A perturbation fails rooted-tree order2",
        "treating stored estimator as exact difference fails binary64 expression contract", "original PD abscissa index fails time moment",
        "unreviewed source macro fails hash contract", "ties-away/host-float RN interpretation fails exact tie cases")]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, default=ROOT / ".wasm-engine/sources")
    parser.add_argument("--output", type=Path, default=HERE / "evidence/analysis.json")
    args = parser.parse_args()
    original, corrected, contract = sources(args.sources)
    counts = [len(trees(order)) for order in range(1, 10)]
    assert counts == [1, 1, 2, 4, 9, 20, 48, 115, 286]
    results = {}
    for method in ("rkf", "pd"):
        for stored in (False, True):
            label = method + ("Stored" if stored else "Ideal")
            results[label] = summarize_tableau(tableau(corrected, method, stored), 6 if method == "rkf" else 9)
            print(label + ": exact rational rooted-tree analysis complete", flush=True)
    for label, weight, order in [("rkfIdeal", "advance", 5), ("rkfIdeal", "embedded", 4), ("rkfIdeal", "estimator", 4)]:
        for n in range(1, order + 1):
            item = results[label]["autonomousRootedTreeSummary"][str(n)]
            assert item[weight]["exactZeros"] == item["trees"]
    assert results["rkfIdeal"]["autonomousRootedTreeSummary"]["6"]["advance"]["exactZeros"] < 20
    assert results["rkfIdeal"]["autonomousRootedTreeSummary"]["5"]["estimator"]["exactZeros"] < 9
    original_pd = tableau(original, "pd", True)
    original_moment = sum(b * c for b, c in zip(original_pd["b"], original_pd["c"]))
    invisible = {method + variant: invisible_rhs(tableau(source, method, True))
                 for method in ("rkf", "pd") for variant, source in [("Original", original), ("Corrected", corrected)]}
    envelopes = {method + variant: envelope(tableau(source, method, True), tableau(corrected, method, False))
                 for method in ("rkf", "pd") for variant, source in [("Original", original), ("Corrected", corrected)]}
    report = {"schema": 1, "source": contract, "analyzerSha256": sha(Path(__file__).read_text()),
        "extractorSha256": sha((HERE / "core.py").read_text()), "treeCountsByOrder": counts, "analyses": results,
        "sourceCorrespondencePreconditions": "n_vals=n_orbit_params=6, initialized valid disjoint input/output buffers, successful allocation, and zero reference. Dimension-independent mathematical envelope inductions remain conditional abstractions, not verification of the general C interface. General estimator/norm arithmetic is unverified beyond compiled exact-zero controls.",
        "originalPdTimeCounterexample": {"rhs": "y'=t", "reference": "zero", "t0": 0, "y0": 0, "h": 1,
            "exactStoredTableauOutput": qjson(original_moment), "exactSolution": "1/2", "defect": qjson(original_moment - Q(1, 2))},
        "invisibleRhsCounterexamples": invisible, "roundingEnvelopes": envelopes,
        "linearOdeEnvelopes": {method: linear_ode_envelope(tableau(corrected, method, True)) for method in ("rkf", "pd")},
        "negativeMutations": mutations(original, corrected),
        "limits": "Autonomous rooted-tree equations refer to formal exact-arithmetic methods. Only active RKF ideal rational advance5/embedded4 is exact through claimed orders. PD decimal/stored coefficients have nonzero residuals, never exact-zero order proofs; stage-time consistency is checked separately. Actual compiler comparison and its limits are recorded in compiled.json."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
