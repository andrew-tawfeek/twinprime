# What the formal parity comparisons establish

Corrected against the theorem types and [the current plan](../PLAN.md), 2026-09-04.
The original numerical tables are retained unchanged; these corrections concern their interpretation.

## The actual inequality

Write P(z) for the product of primes at most z, and define

```text
A_d(x) = #{0 ≤ n ≤ x : d divides n(n+2)}
D_d(x) = sum_{0 ≤ n ≤ x, d divides n(n+2)} λ(n).
```

Here λ is Liouville; Λ is reserved for von Mangoldt. For squarefree odd moduli,
the local root count is ρ(d) = 2^ω(d), and the count scale includes x ρ(d)/d.

The Lean theorem `TwinPrime.parity_obstruction` says that, when z ≥ 3 and
x < z², every function satisfying `IsLowerMoebius` obeys

```text
sum_{d | P(z)} μ⁻(d) A_d(x) ≤ sum_{d | P(z)} |μ⁻(d)| |D_d(x)|.
```

The proof applies the lower sieve to 1 + λ(n). Every sifted first member is
prime, and this sequence vanishes there. Identifying both members as prime
requires x + 2 < z², as in `card_sifted_eq_twin`.

The inequality supplies no estimate for its right-hand side. An o(x/log² x)
bound for that side would exclude an expected-order lower bound from the
specified weights, but would not exclude every smaller positive or unbounded
lower bound. Improving the upper comparison does not reverse its direction.

The upper comparison, `parity_obstruction_upper`, has the form
2T ≤ U + discrepancy. A factor-two asymptotic conclusion requires a separate
negligible-discrepancy estimate for the specified weights and levels.

## Distinct correlations and quantifiers

The informal model 1 ± λ(n(n+2)), on positive integers, uses λ(n)λ(n+2).
It is different from the formal comparison using λ(n). Even at modulus 1,
the product involves a two-point correlation. The
[logarithmically averaged two-point theorem](https://arxiv.org/abs/1509.05422)
does not supply the moving sifted-set estimate required here.

A fixed-modulus theorem cannot replace a bound uniform over d ≤ x^θ.
Even a uniform error ε(x) x/d incurs a harmonic-sum loss when summed absolutely.
Merely knowing ε(x) → 0 does not supply the required logarithmic rate.
Cancellation in a signed sum of discrepancies would be another estimate to prove.

These qualifications agree with the broader parity limitation discussed in
[Tao's parity essay](https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/).
They do not establish that all possible proofs must use one particular bilinear form.

## What the computations say

`data/liouville_disc_1e9.tsv` records x = 10^9 and 6083 squarefree moduli at
most 10^4. The current plan's audit found sum |D_d| = 5663877; the mean and
maximum of |D_d|/sqrt(A_d) are about 0.758384 and 3.653992. These are finite
observations, not a uniform cancellation theorem. Extrapolation must retain
root multiplicities and all losses from summing over growing moduli.

`data/parity_1e9.tsv` splits sifted pairs by parity of Ω(n)+Ω(n+2). This is a
finite statistic, not an asymptotic equidistribution theorem. A zero-denominator
ratio is infinite for a positive numerator and undefined when both counts vanish.
Historical output from `odd.max(1)` is not a valid finite ratio.
No committed table has been overwritten.

## The two-coordinate Maynard constant

[Polymath8b, Corollaries 6.3 and 6.4](https://arxiv.org/html/1407.4897) gives

```text
M₂ = 1 / (1 - W(1/e)) = 1.38593… < 2 log 2 < 2.
```

The exact value differs from the general upper bound. The standard criterion
for two coordinates needs M₂ > 2/θ, with θ ≤ 1, and cannot meet that threshold.
Bounded gaps at most 246, or at most 6 under GEH, do not give fixed shift 2.
The saved floating-point grids and Richardson extrapolations are not rigorous
variational certificates; the k = 5 extrapolation does not certify a bound above 2.

## The remaining target

Unbounded π₂(x) is equivalent to twin-prime infinitude. An eventual lower bound
π₂(x) ≥ c x/log² x, c > 0, is sufficient and stronger; its converse is not proved.
The Hardy–Littlewood asymptotic is stronger still. The existing conditional Lean
theorems prove implications, not their hypotheses.

The current plan isolates a signed bilinear lower bound and allows good dyadic
intervals on an unbounded sequence. That new estimate and the known analytic
inputs are distinct obligations. Infinitely many pairs with Ω(n)+Ω(n+2) ≤ 4001
are almost-prime pairs; there is no justified interpolation down to two primes.
