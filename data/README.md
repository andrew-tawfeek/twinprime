# Saved computational tables

These files preserve selected historical runs. Their finite ranges and
floating-point columns do not prove a limiting density, an asymptotic bound,
or the twin prime conjecture. The cleanup did not rerun the large experiments.

| File | Contents and limits |
|---|---|
| `twin_counts_1e13.tsv` | CPU twin-prime counts with floating-point sums and comparisons. |
| `gpu_twin_counts_1e10.tsv` | A historical GPU counting run; not revalidated on GPU during cleanup. |
| `parity_1e9.tsv` | Finite parity statistics for selected sieve cutoffs. |
| `liouville_disc_1e9.tsv` | Finite Liouville discrepancy observations. |
| `maynard_mk.tsv` | Floating-point Galerkin estimates of the Maynard functional. |

The original header in `maynard_mk.tsv` says “lower bound (Galerkin).” This
is a historical label, not a certified numerical bound: the script does not
control floating-point rounding or establish a discretization error estimate.
Observed convergence and extrapolation do not certify the limiting value.
The current script describes these values as uncertified estimates.

For small, repeatable checks and tool-specific limitations, see the
[computation guide](../compute/README.md). More detailed selected correlation
results and exact finite checks are described in
[CORRELATION.md](../compute/CORRELATION.md).
