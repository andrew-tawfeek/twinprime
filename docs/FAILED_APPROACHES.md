# Approaches that do not close the current proof

These records identify the first unsupported step. They are not impossibility
theorems about all future approaches.

1. **Reverse the parity inequality.** The proved inequality gives an upper bound
   on a lower-sieve expression in terms of a Liouville discrepancy. Making this
   upper bound small does not give a positive twin-prime lower bound. It would
   not exclude every smaller unbounded lower bound either.

2. **Use the mixed correlation as a pointwise prime minorant.** The truncated
   sum Λ_U is signed on composites. The exact omitted defect is H−I+B. Omitting
   it assumes the missing sign information. Its Type I part is large even in the
   reproduced finite examples.

3. **Infer the required positive margin from W₂ ≥ 0.** With A=CX+o(X) and
   H−I=o(X), positivity gives only B≥−CX+o(X). The required bound is B≥−CX/2
   cofinally. The former permits cancellation of the entire main term. In
   particular, finitely many twins would imply W₂=o(X) by the proved prime-power
   error and would remain compatible with B=−CX+o(X).

4. **Apply one-variable prime distribution after Cauchy–Schwarz.** The exact
   dispersion expansion in [ANALYTIC_REVIEW.md](ANALYTIC_REVIEW.md) introduces
   signed correlations Λ(d₁r+2)Λ(d₂r+2) for d₁≠d₂. The diagonal is controllable,
   but replacing the off-diagonal terms by a prime-pair asymptotic introduces
   another unproved estimate. The crude bound does not fit the required budget.

5. **Promote finite numerical evidence to a cofinal theorem.** Exact identities
   and box partitions at finite X validate implementations. They do not prove
   the signed bound on an unbounded sequence. Floating-point optimization or
   Richardson extrapolation also does not certify an analytic inequality.

The remaining task is an actual signed correlation estimate with its quantifiers,
ranges, and total error accounted for. No such estimate was obtained in this work.

## An exact Type I moment-preserving switch

The following finite counterexample sharpens the limitation of a switching
argument that uses only the available Type I moments and prime-shift support.
Replace the weight `Lambda(n+2)` temporarily by an arbitrary nonnegative weight
`a(n)` on the same interval, defining `A[a],H[a],I[a],B[a],W[a]` by the same
linear sums. Their exact decomposition still holds for every such weight.

Take `X=1000`, `U=V=3`, `Q=UV=9`, and the three inputs

```text
l=1007=19*53,   t=1019 prime,   r=1037=17*61.
```

All shifted inputs `1009,1021,1039` are prime, and none of the three inputs has
a divisor between 2 and 9. Let `a` have unit mass at `t`. Define `a'` by giving
mass `alpha` to `l` and `1-alpha` to `r`, where

```text
alpha = (log r - log t)/(log r - log l).
```

The inequalities `l<t<r` imply `0<alpha<1`. Therefore both weights are bounded
by 1, are nonnegative, and are supported where the shifted value is prime.
They have identical mass and logarithmic moment:

```text
sum a = sum a' = 1,
sum a(n) log n = sum a'(n) log n = log t.
```

Consequently all divisibility masses and logarithmic moments through `Q` agree:
for `q=1` these are the displayed equalities; for `2<=q<=Q` both are zero.
In particular, `A,H,I` are identical, while the genuine prime correlation is not:

| Weight | A | H | I | W | B |
|---|---|---|---|---|---|
| `a` | `log 3` | `log(t/3)` | 0 | `log t` | 0 |
| `a'` | `log 3` | `log(t/3)` | 0 | 0 | `-log t` |

The last column follows from the proved prime/rough coefficient identities.
For every fixed `delta>0`, the proposed universal finite inequality
`B[a] >= -(1-delta)(A[a]+H[a]-I[a])` fails for `a'`: its entire positive Type I
contribution is cancelled. Adding a common background weight preserves this
exact change in `W` and `B` without changing the comparison of the Type I sums.

**First unsupported step:** inferring a positive surviving fraction from these
finite moments and prime-shift support alone. The switch supplies an explicit
direction invisible to those moments but visible to primality. It does not
preserve the original pointwise values `a(n)=Lambda(n+2)`, the full maximal BV
data for every residue and endpoint, or an asymptotic main term. Thus it is a
counterexample to the stated universal finite shortcut, not a disproof of (B*)
or an impossibility theorem about every use of distribution information.

There is also a precise limit to repeating this construction. A switch of total
mass `m` changes any cumulative progression count by at most `m`, since both
redistributions are nonnegative measures of mass `m`. Its summed maximal error
over `q<=Q` is therefore bounded by `Q*m`. Removing weighted prime mass of order
`X` this way would require transferred mass of order `X/log X`, because
`Lambda(n)<=log(2X)` in the interval. The resulting generic bound
`Q*X/log X`, with `Q` of order `X^(2/5)`, does not fit the required distribution
budget. A claim that these finite switches produce a full parity model satisfying
BV would need an additional cancellation or distribution argument; the finite
example does not supply it.

## A positive signed dispersion off-diagonal

The off-diagonal cannot be discarded by declaring its Möbius signs favorable.
Take canonical `X=200`, `U=V=2`, box `M=16,N=8`, and `r=13`. Among the allowed
`16<d<=32` with `200<13d<=400`, the only nonzero
`mu(d)Lambda(13d+2)` terms are `d=17,29`; the shifted primes are `223,379`.
The inner sum is `-log223-log379`. Its square exceeds its diagonal by
`2 log223 log379`. Multiplication by `beta_2(13)=log13` gives the strictly positive
off-diagonal contribution `2 log13 log223 log379` at this `r`.

This refutes a pointwise nonpositive-off-diagonal premise and a diagonal-only
square bound. It does not decide whether off-diagonal contributions cancel
after the complete sum over `r` and boxes; that cancellation is the unproved
estimate a dispersion approach would still need.

Both examples are checked without floating-point signs or a large search by
`python compute/type_i_switch_check.py`. The logarithmic interpolation identities
are checked after clearing their positive denominator as exact integer
coefficients of `log(p)log(q)`.

## Full cutoff smoothing as an o(X) signed replacement

The [smoothing audit](SMOOTHED_SIGNED_GAIN_REVIEW.md) now computes the actual
obstruction. Full logarithmic averaging over 1<=t<R changes B by
-C(1-v)X/r+o(X) when R=X^r,W=X^v,0<r<=v,r+v<1/2. The averaged finite
classical center increases by the opposite main amount. The first invalid
step is discarding the bounded-cutoff boundary when averaging pointwise
sharp-center limits. A fixed-power window cancels that boundary but has no
proved positive signed gain.

Pointwise monotonicity fails even at the exact planned cutoffs: X=1000,
R=3,W=5,n=1011=3*337,n+2=1013 prime. Smoothing changes the zero prime-beta
coefficient to -log337. The finite A+H-I term compensates it. Exact checks
are in `python compute/smoothing_check.py`; no asymptotic conclusion is
inferred from the witness alone.
