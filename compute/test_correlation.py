"""Independent small-input checks for the finite correlation diagnostic."""

import math
from pathlib import Path
import subprocess
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import correlation


def git_subprocess_stub(side_effect=None):
    # Replace correlation's imported binding, not the shared subprocess module:
    # platform.platform() may independently invoke subprocess.run on Linux.
    return SimpleNamespace(
        run=Mock(side_effect=side_effect),
        CalledProcessError=subprocess.CalledProcessError,
    )


def trial_factor(n):
    result = {}
    d = 2
    while n > 1:
        while n % d == 0:
            result[d] = result.get(d, 0) + 1
            n //= d
        d += 1
    return result


def trial_mangoldt(n):
    factors = trial_factor(n)
    return math.log(next(iter(factors))) if len(factors) == 1 else 0.0


def trial_prime(n):
    return n >= 2 and trial_factor(n) == {n: 1}


class CorrelationTests(unittest.TestCase):
    def test_provenance_uses_portable_paths(self):
        git = git_subprocess_stub([
            subprocess.CompletedProcess([], 0, stdout="test-commit\n"),
            subprocess.CompletedProcess([], 0, stdout=" M compute/correlation.py\n"),
        ])
        with patch("correlation.Path.exists", return_value=True), patch("correlation.subprocess", git):
            record = correlation.provenance(["--X", "10"])
        self.assertEqual(record["source_commit"], "test-commit")
        self.assertEqual(record["working_tree_changes"], [" M compute/correlation.py"])
        self.assertEqual(record["script_path"], "compute/correlation.py")
        self.assertEqual(record["binary_path"], Path(correlation.sys.executable).name)
        for key in ["script_path", "binary_path"]:
            self.assertFalse(Path(record[key]).is_absolute())
            self.assertNotIn("\\", record[key])
        for key in ["script_sha256", "binary_hash_sha256"]:
            self.assertRegex(record[key], r"^[0-9a-f]{64}$")

    def test_provenance_supports_source_archives_and_missing_git(self):
        git = git_subprocess_stub()
        run_process = subprocess.run
        with patch("correlation.Path.exists", return_value=False), patch("correlation.subprocess", git):
            self.assertIs(subprocess.run, run_process)
            record = correlation.provenance([])
            git.run.assert_not_called()
            self.assertIsNone(record["source_commit"])
        for error in [FileNotFoundError("git"), subprocess.CalledProcessError(128, "git")]:
            with self.subTest(error=type(error).__name__):
                git = git_subprocess_stub(error)
                with patch("correlation.Path.exists", return_value=True), patch("correlation.subprocess", git):
                    record = correlation.provenance([])
                self.assertIsNone(record["source_commit"])
                self.assertIsNone(record["working_tree_changes"])
                self.assertIn("unavailable", record["git_provenance"])
                self.assertEqual(len(record["script_sha256"]), 64)

    def test_arithmetic_tables_against_trial_division(self):
        arithmetic = correlation.Arithmetic(200)
        for n in range(1, 201):
            factors = trial_factor(n)
            self.assertEqual(arithmetic.log(n), factors)
            expected_mu = 0 if any(k > 1 for k in factors.values()) else (-1) ** len(factors)
            self.assertEqual(arithmetic.mu[n], expected_mu)
            expected_vm = next(iter(factors)) if len(factors) == 1 else 0
            self.assertEqual(arithmetic.vm_base[n], expected_vm)
            self.assertEqual(sorted(arithmetic.divisors(n)), [d for d in range(1, n + 1) if n % d == 0])

    def test_cutoffs_and_dyadic_endpoints_are_exact(self):
        for root in range(1, 101):
            self.assertEqual(correlation.fifth_root(root**5 - 1), root - 1)
            self.assertEqual(correlation.fifth_root(root**5), root)
        for n in range(2, 1001):
            lower = correlation.dyadic_lower(n)
            self.assertLess(lower, n)
            self.assertLessEqual(n, 2 * lower)
            self.assertEqual(lower & (lower - 1), 0)

    def test_eight_thousand_exact_vaughan_identities(self):
        result = correlation.verify_vaughan(2000, [(1, 1), (3, 5), (7, 11), (13, 17)])
        self.assertTrue(result["exact_identity"])
        self.assertEqual(result["checks"], 8000)

    def test_decomposition_and_prime_power_removal_against_direct_trial_factorization(self):
        for x in [2, 3, 4, 5, 8, 10, 16, 27, 40, 100]:
            for u, v in [(1, 1), (2, 1), (3, min(2, x - 1)), (2 * x, x - 1)]:
                result, _ = correlation.compute(x, u, v)
                self.assertTrue(all(result["checks"].values()))
                weighted = []
                errors = []
                twins = 0
                for n in range(x + 1, 2 * x + 1):
                    mass = trial_mangoldt(n) * trial_mangoldt(n + 2)
                    weighted.append(mass)
                    twin = trial_prime(n) and trial_prime(n + 2)
                    twins += twin
                    if not twin:
                        errors.append(mass)
                self.assertAlmostEqual(result["values"]["W_2"], math.fsum(weighted), places=10)
                self.assertAlmostEqual(result["values"]["E_pp"], math.fsum(errors), places=10)
                self.assertEqual(result["direct_twin_count"], twins)
                self.assertLessEqual(result["twin_weighted_mass"], result["PP_upper_bound_log_squared_times_twin_count"] + 1e-10)

    def test_factor_boxes_partition_every_pair_and_agree_in_sign(self):
        for x, u, v in [(3, 1, 1), (16, 2, 3), (31, 3, 5), (40, 4, 7)]:
            result, rows = correlation.compute(x, u, v)
            expected_pairs = {(d, r) for d in range(u + 1, 2 * x + 1)
                              for r in range(v + 1, 2 * x + 1) if x < d * r <= 2 * x}
            seen = set()
            for row in rows:
                pairs = {(d, r) for d in range(row["d_min"], row["d_max"] + 1)
                         for r in range(row["r_min"], row["r_max"] + 1) if x < d * r <= 2 * x}
                self.assertFalse(seen & pairs)
                seen.update(pairs)
                self.assertEqual(len(pairs), row["factor_pairs"])
                self.assertGreaterEqual(row["positive_sum"], 0)
                self.assertLessEqual(row["negative_sum"], 0)
                self.assertLessEqual(abs(row["signed_sum"]), row["absolute_sum"] + 1e-10)
                self.assertLessEqual(row["shifted_proper_prime_power_absolute"], row["absolute_sum"] + 1e-10)
            self.assertEqual(seen, expected_pairs)
            self.assertEqual(len(seen), result["factor_pair_count"])
            self.assertAlmostEqual(math.fsum(row["signed_sum"] for row in rows), result["values"]["B_UV"], places=10)

    def test_invalid_domains_are_rejected(self):
        for x, u, v in [(0, 1, 1), (1, 1, 1), (10, 0, 1), (10, 21, 1), (10, 1, 0), (10, 1, 10)]:
            with self.assertRaises(ValueError):
                correlation.compute(x, u, v)


if __name__ == "__main__":
    unittest.main()
