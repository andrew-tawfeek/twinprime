#!/usr/bin/env python3
"""Exact checks of finite bilinear sign facts and specified counterexamples.

The large witness is verified individually by trial division; no large range is
enumerated. Logarithmic signs are decided by comparing exact integer products.
These checks falsify proposed pointwise shortcuts, not asymptotic statements.
"""

from __future__ import annotations

import json
from math import isqrt

from correlation import add_linear


def factor(n: int) -> dict[int, int]:
    if n < 1:
        raise ValueError("n must be positive")
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def prime_by_trial_division(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def squarefree_divisors(factors: dict[int, int]) -> list[tuple[int, int, tuple[int, ...]]]:
    result = [(1, 1, ())]
    for p in factors:
        result += [(d * p, -mu, included + (p,)) for d, mu, included in result[:]]
    return result


def beta_from_factors(factors: dict[int, int], v: int) -> dict[int, int]:
    result = {}
    for p, exponent in factors.items():
        count = sum(p**k > v for k in range(1, exponent + 1))
        if count:
            result[p] = count
    return result


def coefficient(factors: dict[int, int], u: int, v: int) -> tuple[dict, dict, dict]:
    """b, positive factorwise mass, absolute negative factorwise mass, in log(p)."""
    if u < 1 or v < 1:
        raise ValueError("cutoffs must be positive")
    positive, negative = {}, {}
    for d, mu, included in squarefree_divisors(factors):
        if d <= u:
            continue
        quotient = factors.copy()
        for p in included:
            quotient[p] -= 1
        beta = beta_from_factors(quotient, v)
        add_linear(positive if mu > 0 else negative, beta)
    result = positive.copy()
    add_linear(result, negative, -1)
    return result, positive, negative


def log_sign(coefficients: dict[int, int]) -> int:
    """Sign of sum c_p log(p), using exact integer arithmetic, without logarithms."""
    numerator = denominator = 1
    for p, exponent in coefficients.items():
        if exponent > 0:
            numerator *= p**exponent
        else:
            denominator *= p**(-exponent)
    return (numerator > denominator) - (numerator < denominator)


def truncated_mobius(factors: dict[int, int], u: int) -> int:
    return sum(mu for d, mu, _ in squarefree_divisors(factors) if d <= u)


def witnesses() -> list[dict]:
    cases = [
        (1000, 3, 1085, "dropping rough composites with at least three prime factors"),
        (1000, 3, 1127, "dropping rough composites with a repeated prime factor"),
        (10000, 6, 10245, "assuming every composite coefficient is nonpositive"),
        (55**5, 55, 577533495, "assuming b(n) >= -log(n), or nonrough b(n) >= 0"),
    ]
    result = []
    for x, cutoff, n, rejected in cases:
        assert x < n <= 2 * x
        assert cutoff**5 <= x < (cutoff + 1)**5
        assert prime_by_trial_division(n + 2)
        factors = factor(n)
        b, _, _ = coefficient(factors, cutoff, cutoff)
        relative = b.copy()
        add_linear(relative, factors)
        result.append({
            "X": x, "U": cutoff, "V": cutoff, "n": n, "shifted_prime": n + 2,
            "n_factorization": factors, "b_exact_log_prime_coefficients": b,
            "b_sign_exact": log_sign(b), "b_plus_log_n_sign_exact": log_sign(relative),
            "rejected_pointwise_shortcut": rejected,
            "primality_check": "division by every integer 2 <= d <= floor(sqrt(n+2))",
        })
    return result


if __name__ == "__main__":
    print(json.dumps(witnesses(), indent=2))
