#!/usr/bin/env python3
"""Exact diagnostics for logarithmic cutoff averaging, not asymptotic proofs.

The positive logarithmic denominator is cleared. All identities are checked
as integer coefficients of log(prime) or log(prime)*log(prime), using direct
divisor enumeration on one side and telescoped weights on the other.
"""

import json

from correlation import Arithmetic, add_linear, add_product, add_quadratic
from sign_diagnostics import log_sign
from type_i_switch_check import finite_terms


def log_ratio(arithmetic, numerator, denominator):
    result = arithmetic.log(numerator)
    add_linear(result, arithmetic.log(denominator), -1)
    return result


def truncated_mangoldt(arithmetic, n, cutoff):
    result = {}
    for d in arithmetic.divisors(n):
        if d <= cutoff:
            add_linear(result, log_ratio(arithmetic, cutoff, d), arithmetic.mu[d])
    return result


def prime_beta(arithmetic, n, cutoff):
    return {p: 1 for p in arithmetic.log(n) if p > cutoff}


def prime_beta_convolution(arithmetic, n, left, right):
    result = {}
    for d in arithmetic.divisors(n):
        if d > left:
            add_linear(result, prime_beta(arithmetic, n // d, right), arithmetic.mu[d])
    return result


def averaged_moebius_numerator(arithmetic, n, lower, upper):
    result = {}
    for t in range(lower, upper):
        mu_sum = sum(arithmetic.mu[d] for d in arithmetic.divisors(n) if d <= t)
        add_linear(result, log_ratio(arithmetic, t + 1, t), mu_sum)
    return result


def averaged_bilinear_numerator(arithmetic, n, lower, upper, right):
    result = {}
    for t in range(lower, upper):
        add_product(result, log_ratio(arithmetic, t + 1, t),
                    prime_beta_convolution(arithmetic, n, t, right))
    return result


def check_identities():
    arithmetic = Arithmetic(602)
    averaging_checks = convolution_checks = 0
    for upper in range(2, 13):
        for lower in sorted({1, max(1, upper // 2)}):
            denominator = log_ratio(arithmetic, upper, lower)
            assert log_sign(denominator) == 1
            mass = {}
            for t in range(lower, upper):
                add_linear(mass, log_ratio(arithmetic, t + 1, t))
            assert mass == denominator
            for n in range(1, 241):
                smooth = truncated_mangoldt(arithmetic, n, upper)
                add_linear(smooth, truncated_mangoldt(arithmetic, n, lower), -1)
                assert averaged_moebius_numerator(arithmetic, n, lower, upper) == smooth
                averaging_checks += 1
                for right in [upper, upper + 3]:
                    expected = {}
                    if arithmetic.prime(n) and n > right:
                        add_product(expected, denominator, arithmetic.log(n))
                    add_product(expected, smooth, prime_beta(arithmetic, n, right), -1)
                    assert averaged_bilinear_numerator(
                        arithmetic, n, lower, upper, right) == expected
                    convolution_checks += 1
    return {"averaging_identities": averaging_checks,
            "prime_beta_convolution_identities": convolution_checks,
            "scope": "finite exact coefficient checks; no asymptotic estimate"}


def check_negative_change(x=300, upper=10, right=10, small=3, large=127):
    n = small * large
    arithmetic = Arithmetic(2 * x + 2)
    assert arithmetic.prime(small) and arithmetic.prime(large) and arithmetic.prime(n + 2)
    assert small <= upper <= right < large
    assert x < n <= 2 * x and upper * right <= x
    assert prime_beta_convolution(arithmetic, n, upper, right) == {}
    averaged = averaged_bilinear_numerator(arithmetic, n, 1, upper, right)
    assert averaged == {(small, large): -1}
    assert averaged_moebius_numerator(arithmetic, small, 1, upper) == {small: 1}
    # Check the compensating A+H-I change independently in the original
    # finite Vaughan decomposition. On this squarefree input beta=beta'.
    averaged_classical = {}
    for t in range(1, upper):
        terms = finite_terms(arithmetic, n, t, right)
        classical = terms["A"].copy()
        add_linear(classical, terms["H"])
        add_linear(classical, terms["I"], -1)
        add_product(averaged_classical, log_ratio(arithmetic, t + 1, t), classical)
    assert averaged_classical == {(small, large): 1}
    total = averaged.copy()
    add_quadratic(total, averaged_classical)
    assert total == {}
    return {"X": x, "R": upper, "W": right, "n": n, "shifted_prime": n + 2,
            "sharp_bilinear_coefficient": "0",
            "averaged_bilinear_coefficient": f"-log({small})*log({large})/log({upper})",
            "averaged_A_plus_H_minus_I": f"log({small})*log({large})/log({upper})",
            "actual_shift_weight": f"log({n + 2})>0",
            "rejected_shortcut": "logarithmic smoothing always improves each signed bilinear contribution"}


def check_primary_quarter_change():
    x, upper, right = 1000, 3, 5
    assert upper**5 <= x < (upper + 1)**5
    assert right**4 <= x < (right + 1)**4
    assert (upper * right)**2 < x
    result = check_negative_change(x, upper, right, 3, 337)
    result["cutoffs"] = "exact primary and quarter floors"
    return result


def check_window_square_defect():
    """The square does not majorize the positive part on actual prime shifts."""
    x, lower, upper, right = 100000, 3, 10, 17
    n, small, large = 100055, 5, 20011
    assert lower**10 <= x < (lower + 1)**10
    assert upper**5 <= x < (upper + 1)**5
    assert right**4 <= x < (right + 1)**4
    assert (upper * right)**2 < x and x < n <= 2 * x
    assert n == small * large and lower < small < upper <= right < large
    arithmetic = Arithmetic(2 * x + 2)
    assert all(arithmetic.prime(p) for p in [small, large, n + 2])
    numerator = averaged_moebius_numerator(arithmetic, n, lower, upper)
    denominator = log_ratio(arithmetic, upper, lower)
    complement = denominator.copy()
    add_linear(complement, numerator, -1)
    assert numerator == {3: -1, 5: 1}
    assert complement == {2: 1}
    assert all(log_sign(poly) == 1 for poly in [numerator, denominator, complement])
    assert prime_beta(arithmetic, n, right) == {20011: 1}
    # m and 1-m are both positive. After clearing the positive denominator
    # squared, the weighted defect is the product of four positive logs.
    return {"X": x, "S": lower, "R": upper, "W": right, "n": n,
            "shifted_prime": n + 2,
            "window_value": "log(5/3)/log(10/3), strictly between 0 and 1",
            "weighted_positive_part_minus_square":
                "log(5/3)*log(2)*log(20011)*log(100057)/log(10/3)^2 > 0",
            "scope": "exact finite failure of the square majorant; no asymptotic claim"}


if __name__ == "__main__":
    print(json.dumps({"identities": check_identities(),
                      "negative_change": check_negative_change(),
                      "primary_quarter_negative_change": check_primary_quarter_change(),
                      "window_square_defect": check_window_square_defect()}, indent=2))
