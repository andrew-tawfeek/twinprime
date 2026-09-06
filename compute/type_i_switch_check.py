#!/usr/bin/env python3
"""Exact finite counterexamples to Type I moment and dispersion shortcuts.

All identities are checked in integer log-prime coefficients, after clearing
the positive logarithmic denominator of the interpolated weights. No decimal
evaluation or large search is used, and no asymptotic claim is made.
"""

import json

from correlation import Arithmetic, add_linear, add_product, add_quadratic, beta_direct
from sign_diagnostics import log_sign


def finite_terms(arithmetic, n, u, v):
    mixed, correction, type_i, bilinear = {}, {}, {}, {}
    mu_sum = 0
    for d in arithmetic.divisors(n):
        if d <= u:
            mu_sum += arithmetic.mu[d]
            log_ratio = arithmetic.log(u)
            add_linear(log_ratio, arithmetic.log(d), -1)
            add_linear(mixed, log_ratio, arithmetic.mu[d])
            for b in arithmetic.divisors(n // d):
                if b <= v:
                    add_linear(type_i, arithmetic.mangoldt(b), arithmetic.mu[d])
        else:
            add_linear(bilinear, beta_direct(arithmetic, n // d, v), arithmetic.mu[d])
    add_linear(correction, arithmetic.log(n), mu_sum)
    add_linear(correction, arithmetic.log(u), -mu_sum)
    return {"A": mixed, "H": correction, "I": type_i,
            "B": bilinear, "W": arithmetic.mangoldt(n)}


def check_switch():
    x, u, v = 1000, 3, 3
    left, middle, right = 1007, 1019, 1037
    arithmetic = Arithmetic(2 * x + 2)
    for n in [left, middle, right]:
        assert x < n <= 2 * x
        assert arithmetic.prime(n + 2)
        assert all(n % q != 0 for q in range(2, u * v + 1))
    assert arithmetic.prime(middle)
    assert len(arithmetic.log(left)) == len(arithmetic.log(right)) == 2
    assert all(k == 1 for n in [left, right] for k in arithmetic.log(n).values())
    log_left, log_middle, log_right = [arithmetic.log(n) for n in [left, middle, right]]
    alpha_num = log_right.copy()
    add_linear(alpha_num, log_middle, -1)
    beta_num = log_middle.copy()
    add_linear(beta_num, log_left, -1)
    denominator = log_right.copy()
    add_linear(denominator, log_left, -1)
    assert all(log_sign(poly) == 1 for poly in [alpha_num, beta_num, denominator])
    mass_identity = alpha_num.copy()
    add_linear(mass_identity, beta_num)
    assert mass_identity == denominator
    terms = {n: finite_terms(arithmetic, n, u, v) for n in [left, middle, right]}
    original, switched = {}, {}
    for name in ["A", "H", "I", "B", "W"]:
        original[name], switched[name] = {}, {}
        add_product(original[name], denominator, terms[middle][name])
        add_product(switched[name], alpha_num, terms[left][name])
        add_product(switched[name], beta_num, terms[right][name])
    for name in ["A", "H", "I"]:
        assert original[name] == switched[name], name
    assert switched["W"] == original["B"] == {}
    cancellation = switched["B"].copy()
    add_quadratic(cancellation, original["W"])
    assert cancellation == {}
    return {"X": x, "U": u, "V": v, "moduli_through": u * v,
            "left": left, "middle": middle, "right": right,
            "shifted_primes": [left + 2, middle + 2, right + 2],
            "weights": {"alpha": "(log(1037)-log(1019))/(log(1037)-log(1007))",
                        "beta": "1-alpha"},
            "mass_preserved_exactly": True, "A_H_I_preserved_exactly": True,
            "original_W": "log(1019)", "switched_W": "0",
            "original_B": "0", "switched_B": "-log(1019)",
            "scope": "finite moment counterexample; full BV and original von Mangoldt weights are not asserted"}


def check_dispersion():
    x, cutoff, m, r = 200, 2, 16, 13
    arithmetic = Arithmetic(2 * x + 2)
    total, diagonal = {}, {}
    nonzero = []
    for d in range(m + 1, 2 * m + 1):
        if not (cutoff < d and cutoff < r and x < d * r <= 2 * x):
            continue
        term = {}
        add_linear(term, arithmetic.mangoldt(d * r + 2), arithmetic.mu[d])
        if term:
            nonzero.append(d)
        add_linear(total, term)
        add_product(diagonal, term, term)
    off_diagonal = {}
    add_product(off_diagonal, total, total)
    add_quadratic(off_diagonal, diagonal, -1)
    assert nonzero == [17, 29]
    assert total == {223: -1, 379: -1}
    assert off_diagonal == {(223, 379): 2}
    assert arithmetic.prime(223) and arithmetic.prime(379)
    return {"X": x, "U": cutoff, "V": cutoff, "M": m, "N": 8, "r": r,
            "nonzero_d": nonzero, "inner_sum": "-log(223)-log(379)",
            "off_diagonal_at_r": "2*log(13)*log(223)*log(379)>0",
            "rejected_shortcut": "discarding the signed off-diagonal as nonpositive or bounding the square by the diagonal alone"}


if __name__ == "__main__":
    print(json.dumps({"type_i_switch": check_switch(), "dispersion": check_dispersion()}, indent=2))
