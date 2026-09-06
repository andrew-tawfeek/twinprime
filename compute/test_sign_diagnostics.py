import unittest

from correlation import Arithmetic, add_linear, beta_direct
from sign_diagnostics import coefficient, factor, log_sign, truncated_mobius, witnesses


class BilinearSignTests(unittest.TestCase):
    def test_coefficients_against_independent_divisor_sieve(self):
        arithmetic = Arithmetic(1000)
        for u, v in [(1, 1), (3, 5), (5, 3), (10, 10)]:
            for n in range(1, 1001):
                expected = {}
                for d in arithmetic.divisors(n):
                    if d > u:
                        add_linear(expected, beta_direct(arithmetic, n // d, v), arithmetic.mu[d])
                self.assertEqual(coefficient(factor(n), u, v)[0], expected)

    def test_prime_prime_power_and_rough_formulas(self):
        for u, v in [(1, 1), (3, 5), (5, 3), (10, 10)]:
            for n in range(2, 2001):
                factors = factor(n)
                actual, positive, negative = coefficient(factors, u, v)
                if len(factors) == 1:
                    p, exponent = next(iter(factors.items()))
                    count = sum(p**k > v for k in range(1, exponent)) if p > u else 0
                    self.assertEqual(actual, {p: -count} if count else {})
                if min(factors) > max(u, v):
                    expected = {p: -a for p, a in factors.items()}
                    if len(factors) == 1:
                        add_linear(expected, {next(iter(factors)): 1})
                    self.assertEqual(actual, expected)
                    if len(factors) >= 2 and all(a == 1 for a in factors.values()):
                        k = len(factors)
                        self.assertEqual(negative, {p: 2**(k - 2) for p in factors})
                        self.assertEqual(positive, {p: 2**(k - 2) - 1 for p in factors} if k > 2 else {})

    def test_small_part_switching_multipliers(self):
        for a, q, cutoff in [(15, 683, 6), (1155, 500029, 55)]:
            small = factor(a)
            self.assertTrue(all(exponent == 1 and p <= cutoff for p, exponent in small.items()))
            factors = small.copy()
            factors[q] = 1
            self.assertEqual(coefficient(factors, cutoff, cutoff)[0], {q: -truncated_mobius(small, cutoff)})
        self.assertEqual(truncated_mobius(factor(15), 6), -1)
        self.assertEqual(truncated_mobius(factor(1155), 55), 2)

    def test_explicit_divisor_bound_base_cases_and_finite_instances(self):
        # General induction is written in docs/BILINEAR_SIGN_REVIEW.md.
        for a in range(7):
            self.assertLessEqual((a + 1)**4, 81 * 2**a)
        for n in range(1, 10001):
            divisor_count = 1
            for a in factor(n).values():
                divisor_count *= a + 1
            self.assertLessEqual(divisor_count**4, 729**4 * n)

    def test_named_counterexamples_have_exact_required_signs(self):
        cases = witnesses()
        self.assertEqual([case["b_sign_exact"] for case in cases], [-1, -1, 1, -1])
        self.assertEqual([case["b_plus_log_n_sign_exact"] for case in cases], [0, 0, 1, -1])
        self.assertEqual(cases[-1]["b_exact_log_prime_coefficients"], {500029: -2})
        self.assertEqual(log_sign({1155: 1, 500029: -1}), -1)


if __name__ == "__main__":
    unittest.main()
