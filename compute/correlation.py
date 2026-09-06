#!/usr/bin/env python3
"""Finite diagnostics for PLAN.md (V), (D), and its complete bilinear factor boxes.

All arithmetic identities are checked as exact integer coefficients of formal
products log(p)log(q), with primes p and q. Numerical displays use binary64 and
math.fsum; they are observations, not interval certificates or asymptotic proofs.
The independently enumerated expressions use the interval X < n <= 2X and shift 2.
Only local files are written, and existing output files are never overwritten.

Example:
    python compute/correlation.py --X 1000 10000 100000 --output-dir compute/correlation_results
    python -m unittest discover -s compute -p test_correlation.py
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
from typing import Iterable

Linear = dict[int, int]
Quadratic = dict[tuple[int, int], int]
TWO_C2 = 2.0 * 0.66016181584686957392781211001455577843


def add_linear(target: Linear, source: Linear, scale: int = 1) -> None:
    for prime, coefficient in source.items():
        value = target.get(prime, 0) + scale * coefficient
        if value:
            target[prime] = value
        else:
            target.pop(prime, None)


def add_quadratic(target: Quadratic, source: Quadratic, scale: int = 1) -> None:
    for primes, coefficient in source.items():
        value = target.get(primes, 0) + scale * coefficient
        if value:
            target[primes] = value
        else:
            target.pop(primes, None)


def add_product(target: Quadratic, left: Linear, right: Linear, scale: int = 1) -> None:
    for p, a in left.items():
        for q, b in right.items():
            key = (min(p, q), max(p, q))
            value = target.get(key, 0) + scale * a * b
            if value:
                target[key] = value
            else:
                target.pop(key, None)


def evaluate(poly: Quadratic) -> float:
    return math.fsum(c * math.log(p) * math.log(q) for (p, q), c in poly.items())


def poly_hash(poly: Quadratic) -> str:
    encoded = json.dumps([[p, q, c] for (p, q), c in sorted(poly.items())], separators=(",", ":"))
    return hashlib.sha256(encoded.encode()).hexdigest()


class Arithmetic:
    """Ordinary smallest-prime-factor sieve and exact finite arithmetic functions."""

    def __init__(self, limit: int):
        self.limit = limit
        self.spf = [0] * (limit + 1)
        for p in range(2, limit + 1):
            if self.spf[p] == 0:
                self.spf[p] = p
                if p * p <= limit:
                    for n in range(p * p, limit + 1, p):
                        if self.spf[n] == 0:
                            self.spf[n] = p
        self.mu = [0] * (limit + 1)
        self.mu[1] = 1
        self.vm_base = [0] * (limit + 1)
        for n in range(2, limit + 1):
            p = self.spf[n]
            rest = n // p
            self.mu[n] = 0 if rest % p == 0 else -self.mu[rest]
            if rest == 1 or self.vm_base[rest] == p:
                self.vm_base[n] = p

    def prime(self, n: int) -> bool:
        return n >= 2 and self.spf[n] == n

    def log(self, n: int) -> Linear:
        result: Linear = {}
        while n > 1:
            p = self.spf[n]
            result[p] = result.get(p, 0) + 1
            n //= p
        return result

    def mangoldt(self, n: int) -> Linear:
        p = self.vm_base[n]
        return {p: 1} if p else {}

    def divisors(self, n: int) -> list[int]:
        divisors = [1]
        for p, exponent in self.log(n).items():
            old = divisors[:]
            power = 1
            for _ in range(exponent):
                power *= p
                divisors.extend(d * power for d in old)
        return divisors


def fifth_root(x: int) -> int:
    """Exact floor(x^(1/5)); no rounded floating-point cutoff."""
    lo, hi = 0, 1
    while hi**5 <= x:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**5 <= x:
            lo = mid
        else:
            hi = mid
    return lo


def dyadic_lower(n: int) -> int:
    """The unique power of two M with M < n <= 2M, for n >= 2."""
    if n < 2:
        raise ValueError("dyadic boxes require n >= 2")
    return 1 << ((n - 1).bit_length() - 1)


def beta_direct(arithmetic: Arithmetic, r: int, v: int) -> Linear:
    result: Linear = {}
    for b in arithmetic.divisors(r):
        if b > v:
            add_linear(result, arithmetic.mangoldt(b))
    return result


def beta_subtracted(arithmetic: Arithmetic, r: int, v: int) -> Linear:
    result = arithmetic.log(r)
    for b in arithmetic.divisors(r):
        if b <= v:
            add_linear(result, arithmetic.mangoldt(b), -1)
    return result


def vaughan_rhs(arithmetic: Arithmetic, n: int, u: int, v: int) -> Linear:
    result = arithmetic.mangoldt(n) if n <= v else {}
    for d in arithmetic.divisors(n):
        if not arithmetic.mu[d]:
            continue
        quotient = n // d
        if d <= u:
            add_linear(result, arithmetic.log(quotient), arithmetic.mu[d])
        for b in arithmetic.divisors(quotient):
            if d <= u and b <= v:
                add_linear(result, arithmetic.mangoldt(b), -arithmetic.mu[d])
            elif d > u and b > v:
                add_linear(result, arithmetic.mangoldt(b), arithmetic.mu[d])
    return result


def verify_vaughan(limit: int, cutoffs: Iterable[tuple[int, int]]) -> dict:
    arithmetic = Arithmetic(max(2, limit))
    checks = 0
    cutoff_list = list(cutoffs)
    for u, v in cutoff_list:
        for n in range(1, limit + 1):
            actual = vaughan_rhs(arithmetic, n, u, v)
            expected = arithmetic.mangoldt(n)
            if actual != expected:
                raise AssertionError(f"Vaughan identity failed at n={n}, U={u}, V={v}")
            checks += 1
    return {"limit": limit, "cutoffs": cutoff_list, "checks": checks, "exact_identity": True}


def coefficient_table(arithmetic: Arithmetic, u: int, v: int, top: int) -> dict[int, Linear]:
    """c(q) from its original d*b=q definition, ignoring q > 2X (empty intervals)."""
    coefficients: dict[int, Linear] = {}
    for d in range(1, u + 1):
        if arithmetic.mu[d]:
            for b in range(2, min(v, top // d) + 1):
                if arithmetic.vm_base[b]:
                    add_linear(coefficients.setdefault(d * b, {}), arithmetic.mangoldt(b), arithmetic.mu[d])
    return {q: c for q, c in coefficients.items() if c}


class Box:
    def __init__(self, m: int, n: int):
        self.m, self.n = m, n
        self.factor_pairs = 0
        self.positive_terms = 0
        self.negative_terms = 0
        self.positive: Quadratic = {}
        self.negative: Quadratic = {}
        self.shifted_power_positive: Quadratic = {}
        self.shifted_power_negative: Quadratic = {}
        self.non_squarefree_r_terms = 0
        self.distinct_d: set[int] = set()
        self.distinct_r: set[int] = set()

    def include(self, d: int, r: int, sign: int, beta: Linear, shifted: Linear, proper_power: bool,
                r_squarefree: bool) -> None:
        self.distinct_d.add(d)
        self.distinct_r.add(r)
        if sign > 0:
            self.positive_terms += 1
            target = self.positive
            power_target = self.shifted_power_positive
        else:
            self.negative_terms += 1
            target = self.negative
            power_target = self.shifted_power_negative
        add_product(target, beta, shifted)
        if proper_power:
            add_product(power_target, beta, shifted)
        if not r_squarefree:
            self.non_squarefree_r_terms += 1

    def signed(self) -> Quadratic:
        result = self.positive.copy()
        add_quadratic(result, self.negative, -1)
        return result

    def row(self, x: int, u: int, v: int) -> dict:
        positive, negative = evaluate(self.positive), evaluate(self.negative)
        pp_positive = evaluate(self.shifted_power_positive)
        pp_negative = evaluate(self.shifted_power_negative)
        return {
            "X": x, "U": u, "V": v, "M": self.m, "N": self.n,
            "d_min": max(u + 1, self.m + 1), "d_max": min(2 * self.m, 2 * x // (v + 1)),
            "r_min": max(v + 1, self.n + 1), "r_max": min(2 * self.n, 2 * x // (u + 1)),
            "interval_convention": "M < d <= 2M; N < r <= 2N; d > U; r > V; X < dr <= 2X",
            "log_M_over_log_X": math.log(self.m) / math.log(x),
            "log_N_over_log_X": math.log(self.n) / math.log(x),
            "factor_pairs": self.factor_pairs,
            "nonzero_terms": self.positive_terms + self.negative_terms,
            "positive_terms": self.positive_terms, "negative_terms": self.negative_terms,
            "positive_sum": positive, "negative_sum": -negative,
            "signed_sum": evaluate(self.signed()), "absolute_sum": positive + negative,
            "shifted_proper_prime_power_signed": pp_positive - pp_negative,
            "shifted_proper_prime_power_absolute": pp_positive + pp_negative,
            "non_squarefree_r_nonzero_terms": self.non_squarefree_r_terms,
            "distinct_d_nonzero_terms": len(self.distinct_d),
            "distinct_r_nonzero_terms": len(self.distinct_r),
            "signed_sum_over_CX": evaluate(self.signed()) / (TWO_C2 * x),
            "applicable_proved_lower_bound": None,
            "exact_coefficient_sha256": poly_hash(self.signed()),
        }


def compute(x: int, u: int | None = None, v: int | None = None) -> tuple[dict, list[dict]]:
    if x < 2:
        raise ValueError("X must be at least 2")
    u = fifth_root(x) if u is None else u
    v = fifth_root(x) if v is None else v
    if not (1 <= u <= 2 * x and 1 <= v < x):
        raise ValueError("require 1 <= U <= 2X and 1 <= V < X")
    arithmetic = Arithmetic(2 * x + 2)
    polys: dict[str, Quadratic] = {name: {} for name in ["A_U", "H_U", "I_UV", "B_UV", "W_2", "E_pp"]}
    i_direct: Quadratic = {}
    b_direct: Quadratic = {}
    log_u = arithmetic.log(u)
    direct_twins = 0
    direct_factor_pairs = 0
    max_r = 2 * x // (u + 1)
    beta = {r: beta_direct(arithmetic, r, v) for r in range(v + 1, max_r + 1)}
    for r, coefficients in beta.items():
        if coefficients != beta_subtracted(arithmetic, r, v):
            raise AssertionError(f"beta divisor identity failed at r={r}")
        if any(c < 0 or c > arithmetic.log(r).get(p, 0) for p, c in coefficients.items()):
            raise AssertionError(f"beta coefficient bound failed at r={r}")

    # Direct n/divisor enumeration, separate from the q and d,r enumerations below.
    for n in range(x + 1, 2 * x + 1):
        divisors = arithmetic.divisors(n)
        direct_factor_pairs += sum(d > u and n // d > v for d in divisors)
        shifted = arithmetic.mangoldt(n + 2)
        if not shifted:
            continue
        mangoldt = arithmetic.mangoldt(n)
        add_product(polys["W_2"], mangoldt, shifted)
        twins = arithmetic.prime(n) and arithmetic.prime(n + 2)
        direct_twins += twins
        if not twins:
            add_product(polys["E_pp"], mangoldt, shifted)
        lambda_u: Linear = {}
        m_u = 0
        for d in divisors:
            if d <= u and arithmetic.mu[d]:
                m_u += arithmetic.mu[d]
                log_ratio = log_u.copy()
                add_linear(log_ratio, arithmetic.log(d), -1)
                add_linear(lambda_u, log_ratio, arithmetic.mu[d])
                for b in arithmetic.divisors(n // d):
                    if b <= v:
                        add_product(i_direct, arithmetic.mangoldt(b), shifted, arithmetic.mu[d])
            elif d > u and arithmetic.mu[d] and n // d > v:
                add_product(b_direct, beta_subtracted(arithmetic, n // d, v), shifted, arithmetic.mu[d])
        add_product(polys["A_U"], lambda_u, shifted)
        log_ratio = arithmetic.log(n)
        add_linear(log_ratio, log_u, -1)
        add_product(polys["H_U"], log_ratio, shifted, m_u)

    # Type I sum in its original progression ordering.
    coefficients = coefficient_table(arithmetic, u, v, 2 * x)
    for q, coefficient in coefficients.items():
        log_q = arithmetic.log(q)
        if any(abs(c) > log_q.get(p, 0) for p, c in coefficient.items()):
            raise AssertionError(f"c(q) coefficient bound failed at q={q}")
        for n in range((x // q + 1) * q, 2 * x + 1, q):
            add_product(polys["I_UV"], coefficient, arithmetic.mangoldt(n + 2))

    # Full hyperbolic range, including zero terms for an exact partition count.
    boxes: dict[tuple[int, int], Box] = {}
    for d in range(u + 1, 2 * x // (v + 1) + 1):
        m = dyadic_lower(d)
        for r in range(max(v + 1, x // d + 1), 2 * x // d + 1):
            key = (m, dyadic_lower(r))
            if key not in boxes:
                boxes[key] = Box(*key)
            box = boxes[key]
            box.factor_pairs += 1
            sign = arithmetic.mu[d]
            shifted = arithmetic.mangoldt(d * r + 2)
            if sign and beta[r] and shifted:
                add_product(polys["B_UV"], beta[r], shifted, sign)
                box.include(d, r, sign, beta[r], shifted, not arithmetic.prime(d * r + 2), arithmetic.mu[r] != 0)
    b_boxes: Quadratic = {}
    for box in boxes.values():
        add_quadratic(b_boxes, box.signed())
    residual = polys["A_U"].copy()
    add_quadratic(residual, polys["H_U"])
    add_quadratic(residual, polys["I_UV"], -1)
    add_quadratic(residual, polys["B_UV"])
    add_quadratic(residual, polys["W_2"], -1)
    checks = {
        "D_exact_coefficient_identity": not residual,
        "I_direct_equals_progressions": i_direct == polys["I_UV"],
        "B_divisors_equals_factor_pairs": b_direct == polys["B_UV"],
        "B_equals_sum_of_boxes": b_boxes == polys["B_UV"],
        "box_factor_count_equals_divisor_count": sum(b.factor_pairs for b in boxes.values()) == direct_factor_pairs,
        "coefficient_bounds": True,
        "beta_exact_divisor_identity": True,
    }
    if not all(checks.values()):
        raise AssertionError(f"finite identity check failed: {checks}")
    values = {name: evaluate(poly) for name, poly in polys.items()}
    k_poly = polys["H_U"].copy()
    add_quadratic(k_poly, polys["I_UV"], -1)
    values["K_UV"] = evaluate(k_poly)
    floating_residual = math.fsum([values["A_U"], values["H_U"], -values["I_UV"], values["B_UV"], -values["W_2"]])
    rows = [box.row(x, u, v) for _, box in sorted(boxes.items())]
    return {
        "X": x, "U": u, "V": v,
        "interval_convention": "positive integers n with X < n <= 2X; shifted member n+2",
        "cutoff_rule": "floor(X^(1/5)) via integer arithmetic unless explicitly overridden",
        "values": values,
        "values_over_CX": {name: value / (TWO_C2 * x) for name, value in values.items()},
        "C_approximation": TWO_C2,
        "direct_twin_count": direct_twins,
        "twin_weighted_mass": values["W_2"] - values["E_pp"],
        "PP_upper_bound_log_squared_times_twin_count": math.log(2 * x + 2)**2 * direct_twins,
        "identity_residual_exact_coefficients": [],
        "identity_residual_binary64": floating_residual,
        "checks": checks,
        "factor_pair_count": direct_factor_pairs,
        "factor_box_count": len(rows),
        "B_absolute_sum": math.fsum(row["absolute_sum"] for row in rows),
        "B_shifted_proper_prime_power_signed": math.fsum(row["shifted_proper_prime_power_signed"] for row in rows),
        "B_shifted_proper_prime_power_absolute": math.fsum(row["shifted_proper_prime_power_absolute"] for row in rows),
        "exact_coefficient_sha256": {name: poly_hash(poly) for name, poly in polys.items()},
        "exact_coefficient_nonzero_counts": {name: len(poly) for name, poly in polys.items()},
        "remaining_analytic_obligation": "No estimate is proved for (B*) or for any individual box as X tends to infinity.",
    }, rows


def provenance(arguments: list[str]) -> dict:
    script = Path(__file__).resolve()
    root = script.parent.parent
    # A source archive is still runnable without Git or a .git directory.
    try:
        if not (root / ".git").exists():
            # Do not accidentally attribute an archive to an enclosing checkout.
            raise FileNotFoundError("no Git metadata at the source root")
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True, check=True).stdout.strip()
        status = subprocess.run(["git", "status", "--porcelain"], cwd=root, capture_output=True, text=True, check=True).stdout.splitlines()
        git_provenance = "available"
    except (OSError, subprocess.CalledProcessError):
        commit, status = None, None
        git_provenance = "unavailable: Git is missing or this is a source archive"
    return {
        "source_commit": commit,
        "working_tree_changes": status,
        "git_provenance": git_provenance,
        "script_path": script.relative_to(root).as_posix(),
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "binary_path": Path(sys.executable).name,
        "binary_hash_sha256": hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest(),
        "path_convention": "script_path is repository-relative; binary_path is the interpreter basename",
        "python_version": sys.version,
        "platform": platform.platform(),
        "arguments": arguments,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "arithmetic_precision": {
            "finite_identities": "Exact arbitrary-precision integer coefficients in formal log-prime products",
            "displayed_real_values": "IEEE 754 binary64 math.log and math.fsum; no rigorous rounding interval",
        },
        "purpose": "Reproducible finite diagnostics; neither an asymptotic estimate nor a proof of twin primes",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--X", type=int, nargs="+", default=[1000, 10000, 100000])
    parser.add_argument("--U", type=int)
    parser.add_argument("--V", type=int)
    parser.add_argument("--verify-vaughan-through", type=int, default=2000)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    if args.verify_vaughan_through < 1:
        parser.error("--verify-vaughan-through must be positive")
    if len(set(args.X)) != len(args.X):
        parser.error("X values must be distinct")
    # Prepare output filenames before calculation and refuse accidental replacement.
    output = args.output_dir.resolve()
    files = [output / "summary.json", output / "boxes.csv"]
    if any(path.exists() for path in files):
        parser.error("output already exists; choose a new directory to preserve numerical provenance")
    try:
        vaughan = verify_vaughan(args.verify_vaughan_through, [(1, 1), (3, 5), (7, 11), (13, 17)])
        results, all_boxes = [], []
        for x in args.X:
            result, boxes = compute(x, args.U, args.V)
            results.append(result)
            all_boxes.extend(boxes)
            print(f"X={x} U={result['U']} V={result['V']} twins={result['direct_twin_count']} "
                  f"boxes={len(boxes)} exact_D=passed floating_residual={result['identity_residual_binary64']:.3g}", flush=True)
    except ValueError as error:
        parser.error(str(error))
    record = {"provenance": provenance(sys.argv[1:]), "vaughan_verification": vaughan, "scales": results}
    for row in all_boxes:
        row["source_commit"] = record["provenance"]["source_commit"]
        row["script_sha256"] = record["provenance"]["script_sha256"]
        row["binary_hash_sha256"] = record["provenance"]["binary_hash_sha256"]
        row["arithmetic_precision"] = "exact integer coefficients; displayed numbers binary64, not certified intervals"
    output.mkdir(parents=True, exist_ok=True)
    with files[0].open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(record, stream, indent=2, allow_nan=False)
        stream.write("\n")
    # Box rows carry core provenance; summary.json also records the complete run environment.
    with files[1].open("x", encoding="utf-8", newline="") as stream:
        fieldnames = list(all_boxes[0]) if all_boxes else ["X", "U", "V", "M", "N"]
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(all_boxes)
    print(f"Saved local diagnostics: {files[0]} and {files[1]}")


if __name__ == "__main__":
    main()
