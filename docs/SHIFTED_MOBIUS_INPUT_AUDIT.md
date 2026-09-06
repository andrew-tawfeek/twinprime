# Fixed-shift Möbius input audit

Reviewed 2026-09-05 for PLAN Section 7.4, Experiment B, after completion
of the independent classical distribution chain. None of the results
below supplies a bound for an active B* factor box. The source statements
and the attempted transfer must be distinguished.

## The exact required coefficient class

Fixing the right factor in the repository's exact finite pair sum gives

```text
B_U,V(X) = Σ_{V<r≤2X/(U+1)} β_V(r)
  Σ_{max(U,X/r)<d≤2X/r} μ(d)Λ(rd+2).
```

The ratios specify integer indices in real intervals. On the shifted
prime support, the inner expression is

```text
Σ_{X+2<p≤2X+2, p≡2 (mod r), (p−2)/r>U} μ((p−2)/r) log p.
```

The existing prime-power removal is a bound for the complete bilinear
sum; it is not a new uniform assertion for each inner sum. The sought
cancellation concerns quotient-Möbius values on primes in a progression,
with growing r and the cutoff-dependent outer weight β_V(r).

## Inspected results

**Shift averages.** Lichtman's Theorem 1.1 gives
`Σ_{h≤H}|Σ_{p≤X}μ(p+h)|=o(Hπ(X))` when H<X and
`log H/log log X→∞`. Its higher-correlation results and flexible
coefficient theorem retain an average over the Möbius shift. Thus they
do not identify a prescribed shift at any scale. The paper is by Jared
Duker Lichtman. [Theorems 1.1, 1.3, 1.8, and 6.2](https://arxiv.org/pdf/2009.08969).

**Shorter shift averages.** Specializing Lichtman–Teräväinen's Theorem
1.2 to one Möbius factor and one prime factor gives a bound of the form
`XH log log H/log H` for the corresponding absolute shift average, with
fixed prime shift and `(log X)^(1+ε)≤H≤exp((log X)^c)` for suitable
small c=c(ε)>0. The improved range still averages the Möbius shift.
[Theorem 1.2](https://arxiv.org/pdf/2111.08912).

**A conditional fixed-shift claim.** Carella's Theorem 1.1 explicitly
assumes Hypothesis 2.1. That hypothesis bounds maximal progression
averages whose summands already contain μ(p+a). Its modulus-one term
alone supplies fixed-shift cancellation. Ordinary BV estimates
unweighted prime progression errors and does not prove that assumption.
The proof invokes the hypothesis explicitly in equation (14). This
result cannot be used here as an unconditional input.
[Theorem 1.1, Hypothesis 2.1, and §2.4](https://arxiv.org/pdf/2206.12956).

**Cofinal scales for bounded multiplicative factors.**
Klurman–Mangerel–Teräväinen prove fixed-shift two-point cancellation
along a set of scales of full upper logarithmic density for bounded
multiplicative functions under a nonpretentiousness condition. This
does provide cofinal scales, but Λ is unbounded and β_V is a
cutoff-dependent nonmultiplicative weight. Dividing β_V by a logarithm
does not supply multiplicativity or the required correlation estimate.
[Theorem 1.2](https://arxiv.org/pdf/2304.05344).

**Exceptional-zero assumptions.** Tao–Teräväinen obtain fixed-shift
prime/Liouville correlations on quantitative ranges given a Siegel zero
of specified conductor and quality. Arbitrarily high-quality zeros yield
cofinal conclusions; their paper also derives twin-prime asymptotics
under that assumption. Our proved Siegel lower bound restricts possible
zeros and does not assert their existence. This is therefore another
conditional route, not a consequence of completed M3.
[Theorem 1.6 and Corollary 1.8](https://arxiv.org/pdf/2109.06291).

## First unsupported transfers

An average over shifts cannot be specialized to shift two, even if only
cofinal scales are required. The elementary array
`E(X,h)=X` for h=2 and zero otherwise has average
`Σ_{h≤H}E(X,h)/(XH)=1/H→0`, while `E(X,2)/X=1` at every scale.
This is a counterexample to the logical specialization, not a model of
the Möbius function or primes.

Averaging r in the displayed factor sum changes the affine coefficient
and progression modulus, not the additive shift. Moreover every fixed
r eventually lies outside `r>floor(X^(1/5))`. A theorem for any one fixed
r, even if available, would not cover the active family. Uniformity and
the β weight require separate justification.

No inspected theorem gives the claimed transfer. These failures do not
exclude another use of multiplicative structure, but they rule out using
these source statements directly to discharge B*. The independently
proved [large-gcd range removal](DISPERSION_GCD_ROUTE.md) uses elementary
sparsity and makes no shifted-Möbius cancellation assumption.

## Update 2026-09-05: inspected 2025–2026 developments

This update preserves the earlier audit and checks three further primary
sources against the actual residual

```text
Σ_{d>U, r>V, X<dr≤2X, gcd(d,r)≤G(X)} μ(d)β_V(r)Λ(dr+2),
U=V=floor(X^(1/5)),   G(X)=ceil(log(4X+4)^10).
```

It is an applicability audit, not an exhaustive literature survey or an
impossibility theorem. None of the three statements below supplies a signed
estimate for an active residual box.

### Tao–Teräväinen: quantitative fixed-shift correlations

*Quantitative correlations and some problems on prime factors of consecutive
integers*, arXiv:2512.01739, submitted 2025-12-01;
[v2, 2026-04-25, Theorem 3.1 and Remark 3.2](https://arxiv.org/html/2512.01739v2#S3).
For 1-bounded multiplicative functions `g₁,g₂`, its nonpretentious branch
assumes `exp(M(g₁;X²,log^(1/125)X)) ≫ ℒ`, where `1≤ℒ≤log X` and `M` is
the paper's pretentiousness parameter. Outside a common set
`E⊂[sqrt X,X]` with `∫_E dt/t ≪ log X * ℒ^(-c)`, it gives

```text
abs((W/N) Σ_{N<n≤2N, n≡b (mod W)} g₁(n+h₁)g₂(n+h₂)) ≪ ℒ^(-c),
```

simultaneously for `W≤ℒ^c` and distinct integer shifts `h₁,h₂=O(ℒ^c)`.
This genuinely improves the earlier fixed-shift/cofinal-scale input;
it is not merely an average over shifts. However, `Λ` and `β_V` are outside
the multiplicative bounded coefficient class. The stated affine Liouville
corollary permits only polylogarithmic coefficients. Our slope `r` grows
through power ranges. Writing `d=ga,r=gb` with `g≤G(X)` leaves the prime
argument `g²ab+2`; it does not make the slope polylogarithmic.

### Ford: a fixed-shift small-prime-factor model

*Poisson approximation of prime divisors of shifted primes*, arXiv:2408.03803,
submitted 2024-08-07; [v4, 2026-01-19, Theorem 1 and §1.2](https://arxiv.org/html/2408.03803v4#S1.SS2).
The theorem allows the fixed shift `a=-2`. Under `Z(γ)`, it bounds the
total variation distance between the valuation vector below `y` of `p+a`
and its independent model by

```text
O(exp(-α*u*log u) + log^(-A)x),   u=log x/log y,   0<α<γ.
```

BV supplies `Z(1/2)`, so this specialization is unconditional. The first
transfer obstruction is measurable information: the residual coefficient
is not a function of those small-prime valuations. The existing
[prime and rough coefficient identities](../TwinPrime/Analytic/BilinearSign.lean)
give coefficient `0` on primes and `-log n` on squarefree semiprimes whose
two factors exceed `U=V`. For `y≤U`, both have the all-zero valuation vector
below `y`; both semiprime factorizations have gcd `1` and survive the cut.
This is a coefficient-level distinction, not an asserted distribution of
such semiprimes on shifted primes. Taking `y≈X^(1/5)` also leaves `u≈5`,
so the displayed error does not vanish. Taking `y=x^o(1)` improves the
model error but still omits the distinguishing large-factor information.

### Matomäki–Teräväinen: signs in arithmetic progressions

*Linnik's problem for multiplicative functions*,
[arXiv:2605.27833v1, 2026-05-27, Corollary 1.3](https://arxiv.org/html/2605.27833v1#S1),
proves `R(μ;q) ≪_ε q^(2+ε)`: both signs occur on squarefree integers in
every reduced residue class by that scale. Its sharper bound is
`R(μ;q) ≪ q²(L(q)^100+B(q))`, with `L(q),B(q)` defined in the paper.
This is a genuine improvement in the modulus range for sign occurrence.
It neither locates those occurrences in the moving interval
`max(U,X/r)<d≤2X/r`, nor requires `rd+2` to be prime, nor estimates the
weighted difference of sign masses. The first unsupported step would be
transferring those unweighted sign occurrences to the subset selected by
`β_V(r)Λ(rd+2)`. A small gcd condition does not impose that prime-shift
support or justify the transfer.
