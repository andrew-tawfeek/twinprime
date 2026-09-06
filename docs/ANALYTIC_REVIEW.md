# Analytic review of the finite reduction

Source review date: 2026-09-04. This document records the source check, an
independent calculation of the first dispersion step, and the subsequent
Lean-checked classical reductions. It does not prove the open bilinear estimate
or independent centered pointwise Siegel–Walfisz. The implication from that
pointwise input to maximal Bombieri–Vinogradov, and then to quantitative
Mertens cancellation, is now Lean-checked.

## 1. Source-to-input map

The following primary sources were read directly. The parameter substitutions
and calculations after this table are this review's deductions.

| Needed input | Verified source and exact specialization | Formal status |
|---|---|---|
| Mixed correlation (A) | [Goldston–Yıldırım, Theorem 1.4, p. 7](https://arxiv.org/pdf/math/0111212#page=7): set `k=r=2`, `j=(0,2)`, `a=(1,1)`, and `ϑ=1/2`. Its cutoff range is `N^ε ≪ R ≪ N^(1/2−ε)`, and the main term is `S(0,2)N`. | The required dyadic limit is Lean-checked from `MaximalBombieriVinogradov` and `MertensLogSix`; the source theorem itself is not formalized. |
| Odd Möbius/totient sum and smoothing | [Goldston–Yıldırım, Lemma 2.1, equations (2.11)–(2.13), p. 13](https://arxiv.org/pdf/math/0111212#page=13): set `j=1`, `k=2`. The unsmoothed sum is `O(exp(−c√log R))`; the smoothed sum has main term `S₂(2)=2C₂` with that error. Squarefree support identifies `φ₁` with Euler's totient. | The required limits and constants are Lean-checked from `MertensLogSix`. The stronger exponential error in the source is not formalized. |
| Progression error sum | [Tao, Notes 3, Theorem 17 and Exercise 20](https://terrytao.wordpress.com/2015/01/10/254a-notes-3-the-large-sieve-and-the-bombieri-vinogradov-theorem/): Theorem 17 gives arbitrary logarithmic saving for `Q ≤ x^(1/2)/log^B x`; Exercise 20 adds the maximum over initial interval endpoints. Tao's discrepancy uses the average over reduced residue classes, so conversion to `ψ(y;q,a)−y/φ(q)` also requires the prime number theorem and the contribution of prime powers dividing `q`. | The centered finite reductions, full primitive maximal mean, large-conductor tail, pointwise-to-maximal SW transfer, and exact asymptotic implication `PointwiseSiegelWalfisz → MaximalBombieriVinogradov` at `T=2X+2` are Lean-checked. Independent centered pointwise SW remains unproved; Tao's theorem is not imported. |

For (A), apply the mixed theorem at `N=X` and `N=2X` with the **same**
`R=U=⌊X^(1/5)⌋`. For example, choose fixed `ε=1/20`; both applications satisfy
the range for large `X`. Subtracting gives the dyadic main term `2C₂X`.
Changing `R` between the two applications would change the summands and would
not justify the desired subtraction. The local factor at 2 is 2; every odd
prime contributes `1−1/(p−1)²`.

## 2. Completing the paper argument for the Type I correction

Write `F(t)=∑_{d≤t, d odd} μ(d)/φ(d)`, with `F(t)=0` for `t<1`.
The mapped cancellation estimate implies both `F(t)→0` and a global bound
`|F(t)|≤M` after enlarging `M` to cover a finite initial interval.

### The shared-prime correction

For an odd prime `p` and `k≥1`, the elementary identities for Euler's totient give

```
1/φ(dp^k) = 1/(φ(d)φ(p^k))                    if p ∤ d,
1/φ(dp^k) = (1−1/p)/(φ(d)φ(p^k))              if p ∣ d.
```

Consequently, with `F_p(t)=∑_{d≤t, d odd, p∣d} μ(d)/φ(d)`, finite summation gives

```
Q(U,V) = F(U) ∑_{b≤V, b odd} Λ(b)/φ(b)
       − ∑_{p odd prime} F_p(U) ∑_{k≥1, p^k≤V} log(p)/(p φ(p^k)).
```

This verifies the sign and the factor `1/p` in PLAN.md's formula (Q).
No substitution `φ(db)=φ(d)φ(b)` is valid without the relevant coprimality.

Squarefree support of `μ` proves the exact recurrence

```
F_p(t) = −(F(t/p)−F_p(t/p))/(p−1).
```

Iteration, with terms zero once `t/p^j<1`, gives

```
F_p(t) = −∑_{j≥1} F(t/p^j)/(p−1)^j.
```

The geometric series proves `|F_p(t)|≤M/(p−2)`. For a fixed prime `p`, truncate
this series at a fixed `J`, let `t→∞` in those finitely many terms, and then let
`J→∞`; this proves `F_p(t)→0` without uniformity in a growing prime.
Also,

```
∑_{k≥1} log(p)/(p φ(p^k)) = log(p)/(p−1)^2.
```

Thus the entire shared-prime correction tends to zero by domination with
`M log(p)/((p−1)^2(p−2))`. Its sum converges even when enlarged from odd primes
to every integer at least 3.

The first term of `Q` needs only a fixed logarithmic bound on its other factor.
There is no need to import a sharp estimate here: on the support of `Λ(b)`,
`b=p^k`, so `φ(b)≥b/2`, and

```
∑_{b≤V} Λ(b)/φ(b) ≤ 2∑_{b≤V} log(b)/b = O(log²(2V)).
```

The arbitrary logarithmic saving for `F(U)` therefore proves this term tends to
zero when `U=V=⌊X^(1/5)⌋`. This simplifies one auxiliary requirement in the plan.

### Progression errors and interval endpoints

For odd moduli define

```
E(t;q)=ψ(t;q,2)−t/φ(q).
```

The modulus ranges are `q≤U` for `H` and `q≤UV` for `I`. Both lie below
`X^(2/5)`, hence strictly inside the classical range throughout
`X+2≤t≤2X+2` for large `X`.

For `I`, subtract the errors at the two endpoints and use
`|c_{U,V}(q)|≤log q`; the summed error is `O_A(X/log^(A−1) X)` after applying
the progression theorem with exponent `A`.

For `H`, partial summation uses
`w(t)=log((t−2)/U)` on `[X+2,2X+2]`. The main term is

```
F(U) ∫_X^(2X) log(t/U) dt = O(F(U) X log X)=o(X).
```

The error consists of the two endpoint terms `w(t)E(t;d)` and
`−∫ E(t;d)/(t−2) dt`. Since the divisor sum is finite, sum its absolute values
inside that integral. Applying the progression bound at each `t` gives the
same `O_A(X/log^(A−1) X)` error. This argument uses uniform constants in the
range `t≈X`, but does **not** require interchanging a modulus sum with an
endpoint supremum. The nonmaximal progression theorem suffices for this
specific application; the stronger maximal statement in the plan is usable
but unnecessary here.

For even moduli, a nonzero `Λ(n+2)` requires `n+2=2^k`. There are
`O(log X)` such values. Summing independently over all even moduli and using
`|μ|≤1`, `|c(q)|≤log q`, and `Λ(2^k)=log 2` bounds these exceptional
contributions by `O(U log² X)` for `H` and `O(UV log² X)` for `I`.
Both are `o(X)`. These deliberately generous bounds avoid treating the class
`2 mod q` as a reduced class when `q` is even.

These calculations establish a paper reduction of `(K)` to the identified
classical inputs. The subsequent Lean implementation proves the finite totient
identities, decay of the complete shared-prime correction, discrete partial
summation, and the weighted progression applications. It uses the explicitly
stated maximal integer-endpoint distribution input and the exact discrete main
mass `F(U) Σ_{X<n≤2X} log(n/U)`. This differs from the integral presentation
above but yields the same sublinear conclusion. The even-modulus formal bound
uses `ψ−θ ≤ 2√Y log Y`; its aggregate `O(X^(9/10) log² X)` is sufficient.
The required Möbius/totient limits now follow in Lean from the single ordinary
summatory hypothesis `MertensLogSix`, including their constants. The named
maximal distribution theorem is now derived conditionally from independent
centered pointwise Siegel–Walfisz. Section 5 gives both that checked reduction
and the implication from BV to `MertensLogSix`, so Mertens cancellation is no
longer a separate premise of the refined endpoint. See the
[classical reduction](CLASSICAL_REDUCTION.md), and the current
[obligation ledger](PROOF_OBLIGATIONS.md).

## 3. Exact first dispersion step for the open bound

Fix positive integer box endpoints `M,N`. Let

```
D={d: M<d≤2M, d>U},     R={r: N<r≤2N, r>V},
χ(d,r)=1_{X<dr≤2X},     b_r=β_V(r),
S=∑_{r∈R} b_r ∑_{d∈D} μ(d)Λ(dr+2)χ(d,r),
T=∑_{r∈R} b_r.
```

All quantities are finite, and `b_r≥0`. Weighted Cauchy–Schwarz gives

```
|S|² ≤ T (Dg + Off),

Dg = ∑_{d∈D} μ(d)² ∑_{r∈R} b_r Λ(dr+2)² χ(d,r),

Off = ∑_{d1,d2∈D, d1≠d2} μ(d1)μ(d2)
       ∑_{r∈R} b_r Λ(d1 r+2)Λ(d2 r+2)χ(d1,r)χ(d2,r).
```

The displayed expansion is exact, including both orientations of each distinct
pair. In the inner off-diagonal sum the boundary is exactly

```
max(N,V,X/d1,X/d2) < r ≤ min(2N,2X/d1,2X/d2).
```

The ratios are real ratios and `r` is an integer. No rectangular replacement
or omitted boundary term has been made.

The diagonal already has adequate saving. Set `L=log(4X+4)`. In a nonempty
box, `MN<2X`, so every `r∈R` is at most `2N<4X`; the elementary coefficient bounds give

```
T ≤ N L,     Dg ≤ MN L³,     T Dg ≤ (2X)² L⁴/M.
```

Thus its square-root contribution is at most `2X L²/√M`. On dyadic boxes
intersecting `d>U`, the lower endpoint can be chosen with `M≥U/2`; summing
this bound over even `O(log² X)` boxes is `o(X)` when `U≈X^(1/5)`.
The subsequent [dispersion range-removal proof](DISPERSION_GCD_ROUTE.md)
formalizes this summation over the exact right-closed factor-box partition,
including its growing cardinality. These estimates concern the diagonal
contribution only; an off-diagonal estimate is still needed.

The subsequent [Dispersion.lean](../TwinPrime/Analytic/Dispersion.lean)
checks the exact restriction of the original pair sum to a box, weighted
Cauchy–Schwarz, and the expansion into `Dg + Off`, retaining both orientations
and the signed off-diagonal. Its finite diagonal theorem proves

```text
M * (T * Dg) ≤ (2X)² log⁴(4X+4)
```

under `1≤M`, `1≤N`, and `MN≤2X`. With `1≤U`, `1≤X`, and `U≤2M`, the
checked normalized form is

```text
(T * Dg)/X² ≤ 8 log⁴(4X+4)/U.
```

[DispersionGrowth.lean](../TwinPrime/Analytic/DispersionGrowth.lean) proves
the required logarithm-over-cutoff limits. Consequently
`tendsto_primary_dispersion_diagonal_sqrt` gives, for every fixed natural
`k` and every family of individual boxes whose parameters eventually satisfy
`1≤M(X)`, `1≤N(X)`, `primaryCutoff X≤2M(X)`, and `M(X)N(X)≤2X`,

```text
sqrt(T(X) * Dg(X)) / X * logᵏ(4X+4) → 0.
```

Thus the per-box diagonal is Lean-checked to be `o(X)` even after any fixed
logarithmic loss. The newer `tendsto_primaryDispersionDiagonal_div_log_pow`
proves the same limit for the sum over every active box. Neither assertion
alone bounds the full bilinear sum.

The first unsupported step would be an estimate for the **signed total** of
the off-diagonal correlations at the scale needed to make `T Off` acceptable.
For distinct `d1,d2`, their two affine forms have determinant
`2(d2−d1)`. Indeed,

```
d2(d1r+2) − d1(d2r+2) = 2(d2−d1).
```

One-variable prime distribution does not evaluate their product.
Replacing each product by a prime-pair asymptotic would add an unproved
correlation hypothesis. Dropping the signs and using the elementary bounds
gives only `T|Off|≤M²N²L⁴≤4X²L⁴`, which provides no bound at the required
constant times `X` scale for `S`. An upper-bound sieve might improve logarithms
and local factors, but a saving sufficient for the final signed budget must
still be proved after summing over `d1,d2`.

**Current result:** the exact box restriction, finite expansion, full box
partition, and summed diagonal limit are Lean-checked. The subsequent
large-gcd removal also bounds part of the off-diagonal. The remaining
quantity is the sum over boxes of `sqrt(max(T * Off_small, 0))`, not merely
a signed sum of off-diagonals across boxes. That budget is unestimated,
so the dispersion argument does not prove `(B*)`.

## 4. Formal artifact verified in this review

`TwinPrime/Analytic/Vaughan.lean` proves the cutoff identity, its application
above `V`, the arbitrary finite weighted-sum identity, the formulas and support
of `c` and `β`, `|c(n)|≤log n`, and `0≤β(n)≤log n`.

The commands `lake env lean TwinPrime/Analytic/Vaughan.lean` and
`lake build TwinPrime.Analytic.Vaughan` passed. The six audited declarations
`vaughanIdentity`, `vaughanIdentity_sum`, `abs_vaughanCoefficient_le_log`,
`vaughanBeta_nonneg`, `vaughanBeta_le_log`, and `vaughanBilinear_apply`
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
This initial audit verifies finite algebra. The later integrated audit in
[PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) also covers the weighted interval
applications and conditional limits. It does not discharge their explicitly
stated classical hypotheses or the open signed estimate.

## 5. Checked classical reduction and remaining inputs

The integrated [MertensReduction.lean](../TwinPrime/Analytic/MertensReduction.lean)
now proves both required Möbius/totient limits from the explicitly defined
`MertensLogSix`: there exists a real `K≥0` such that, eventually for natural `t`,
`|M(t)|≤Kt/log⁶t`, where `M(t)=Σ_{0<n≤t} μ(n)`. The complete argument and its
module map are documented in [CLASSICAL_REDUCTION.md](CLASSICAL_REDUCTION.md).

The boundary constants are proved by finite identities. `MoebiusHyperbola.lean`
establishes the exact hyperbola split and derives `S(N)→0` from `M(N)/N→0`,
where `S(N)=Σ_{0<n≤N} μ(n)/n`. `MoebiusAbel.lean` then gives the checked
`O(log⁻⁵N)` tail and `S(N)log²(N+1)→0` under `MertensLogSix`.

`MoebiusBoundary.lean` starts from
`Σ_{0<d≤X} μ(d) H_floor(X/d)/d=1`. Its harmonic remainder retains the real
logarithm `log(X/d)` and has checked bounds `|R_X(d)|≤2d/X` and finite variation
at most `2log X`. A short head and an Abel-controlled tail tend to zero.
This proves the integer smoothed limit, identifies the ordinary logarithmic
moment as `−1`, and extends the smoothing limit to real endpoints:

```text
T(x) = Σ_{0<n≤floor(x)} μ(n) log(x/n)/n → 1.
```

Neither boundary constant is an additional premise in the final Mertens
wrappers. The argument uses ordered finite Möbius sums and does not assume
absolute summability of `μ(n)/n` or invoke an unproved inverse-zeta boundary step.

The correction identities and summability are unconditional. `MoebiusSmoothing.lean`
proves multiplicativity of `h`, the convolution
`1_odd(n) μ(n)/φ(n) = (h * (μ/n))(n)`, and, for positive exponents `k`,

```text
h(2^k) = 2^(-k),
h(p^k) = -1/[p^k(p-1)]     for odd primes p.
```

`SmoothingSummability.lean` proves `Σ|h(d)|<∞`, the positive power moment
`Σ√d·|h(d)|<∞`, the logarithmic moment `Σlog²(d+1)·|h(d)|<∞`, and the exact
Euler-product value `Σh(d)=2C₂`. The finite bridges retain their endpoints:

```text
F(U) = Σ_{0<d≤U} h(d) S(floor(U/d)),
smoothedTotientSum(U) = Σ_{0<d≤U} h(d) T(U/d).
```

In the second line `U/d` is real. `SmoothingLimits.lean` uses the proved moments
and uniform summable majorants to obtain `F(U)log²(U+1)→0` and
`smoothedTotientSum(U)→2C₂`. All these bridges have passed Lean checks; their
Möbius cancellation premise is only `MertensLogSix`.

The earlier theorem `TwinPrime.twinPrimeConjecture_of_bv_mertens_and_bilinear`
retains three inputs. The refined `twinPrimeConjecture_of_bv_and_bilinear`
derives Mertens from BV and has two remaining inputs: `MaximalBombieriVinogradov`
and the cofinal signed bound `(B*)` at the primary cutoff. The further theorem
`twinPrimeConjecture_of_siegel_walfisz_and_bilinear` replaces BV by independent
`PointwiseSiegelWalfisz`, using the proved asymptotic SW-to-BV reduction.
Pointwise SW remains unproved in the library, and `(B*)` requires new
mathematics. The completed classical bridges do not estimate the shifted
bilinear sum or establish twin-prime infinitude unconditionally.

### Addendum: reducing the separate Mertens premise

[PNT_MERTENS_REDUCTION.md](PNT_MERTENS_REDUCTION.md) now gives an
independently reviewed and now Lean-checked implication `MaximalBombieriVinogradov →
MertensLogSix`. It extracts `ψ(x)=x+O(x/log⁶x)`, constructs a centered
Selberg coefficient with summatory error `O(x/log⁵x)`, and uses an exact
hyperbola identity and a weighted-supremum contraction. It needs no
inverse-zeta boundary argument or identification of the centering constant
with `−γ`.

Lean now checks the modulus-one extraction, real prime error, existence of
the reciprocal center and its O(log⁻⁵) remainder, logarithmic convolution
algebra, and both real hyperbola identities. It also proves the absolute
reciprocal coefficient bound `D(2+log y)^2` from elementary Chebyshev bounds,
and a general theorem absorbing a supplied contraction into a locally finite
supremum. The [implementation map](PNT_MERTENS_REDUCTION.md#5-formalization-status-and-resulting-scope)
lists the exact modules and constants.

The quantitative centered signed error, both hyperbola remainders, real
unweighting, and the actual Möbius contraction inequality are now checked.
The parameter choice is proved after the absolute-mass constant is fixed;
only local supremum bounds are used before absorption. `PrimeToMertens.lean`
derives `MertensLogSix` from BV, and the refined endpoint removes that
separate argument. The weighted prime step uses the maximal BV error
directly; the broader ordinary prime-error implication in equation (1) of
the paper note is not the standalone formal theorem. BV is now proved from
the independent centered pointwise SW input described below; that input
remains unproved, and the signed bilinear bound `(B*)` is open.

### Addendum: finite character foundations for BV

[BV_REDUCTION.md](BV_REDUCTION.md) records the next checked stage. Orthogonality
gives the exact progression character expansion; principal centering and both
finite maxima are retained. Primitive replacement costs a noncoprime mass
bounded by `log q+2sqrt(T)log T`. Summed at `T=2X+2`, this is absorbed into
`X/log^A X` for `Q≤sqrt(X)/log^(A+2)X`. Thresholds are uniform over Q and
all endpoint choices. Exact conductor regrouping now replaces the original
character sum by primitive conductor mass with the full multiplier sum
`Σ_{k≤Q/r}1/φ(rk)`. An absolutely summable convolution proves its bound
`Cφ(1+log Q)/φ(r)`. The combined reduction retains conductor one, and
the finite Abel tail estimate includes both boundaries even for equal endpoints.

The primitive Gauss norm identity now covers composite moduli and modulus
one by finite Fourier inversion. Unit-group Parseval then gives the exact
finite large-sieve transfer with factor `q/φ(q)`. An independent review
confirmed the principal term, zero endpoint, inverse convention, and error
normalization. The additive geometric kernel, reciprocal packing estimate,
and finite Schur duality now prove a large sieve for δ-separated frequencies
with constant `N−M+H_card/δ`. Rational frequencies at distinct reduced unit
residues have spacing `1/Q²`, including modulus one.
The complete rational family and the standard-additive-character phase
bridge now give the weighted primitive-character large sieve with constant
`N−M+Q²(1+2log(Q+1))`. `CharacterBilinear` now proves primitive inversion
reindexing and the direct-character convention. Weighted Cauchy–Schwarz
gives the rectangular bilinear first moment.

`CharacterInterval` proves the primitive q>1 interval bound `√q H_q`.
Complex finite Abel summation in `CharacterLogInterval` gives logarithmic
prefix and finite Type I outer-sum bounds, including zero quotients.
`DyadicMaximal` and `DyadicIntervalCover` prove binary-tree energy bounds,
exact covers, and no reuse across disjoint intervals. Their actual
character applications give maximal prefix second moments with loss
`(k+1)²` and adaptive disjoint-interval second moments with loss `2(k+1)²`.
There is no hidden factor for the number of selected intervals.

`DyadicStaircase` preserves the exact clamped product cutoff `mn≤t`.
The [finite maximal route](BV_MAXIMAL_ROUTE.md) is now formalized through
the maximal bilinear bound. `DyadicStaircaseGeometry` proves that both
families of correction intervals are disjoint at each level; `DyadicStaircaseLevels`
accounts for every internal node exactly once. The fixed first-variable
family costs no depth factor. Combining its second moment with the adaptive
second-variable bound gives the proved factor `2(k+1)(j+1)`.
`CharacterMaximalBilinear` applies this result to the actual primitive family
and chooses finite maximizing cutoffs, including the inverse convention.
Independent review checked constants, character-dependent endpoints, cover
injection, and all final natural interval boundaries. `BilinearBoxPolynomial`
also proves the scalar Type II polynomial. The exact masked global box
assembly now checks in `CharacterVaughanDyadic`; `CharacterVaughanMean`
proves the full finite Type II maximal mean with loss `2D⁴ log(T)L_Q`.
Both strict cutoff masks, inactive-box vanishing, and the half-cutoff
polynomial are retained. The full Vaughan character identity includes
the low term `characterPsi (min t V) χ`.

The Type I assembly is now checked. `CharacterVaughanTypeI` and
`CharacterTypeIBounds` prove the exact twisted identities and actual
Pólya–Vinogradov bounds for the pointwise and maximal Type I terms.
`PrimitiveCharacterCounting` supplies the primitive count bounds, and
`CharacterTypeIMean` sums all the terms, retaining the low term and treating
modulus one separately. No mean-value estimate is assumed.

`BVInternalCutoffs` and `BVLogComparisons` prove the floor, power, depth,
and logarithmic comparisons for `W=floor(T^(1/8))`, `T≥256`, and
`1≤R≤sqrt T`. `VaughanMeanParameters` absorbs the actual raw budget, and
`VaughanMeanValue` proves

```text
Σ_{1≤q≤R} (q/φ(q)) Σ_{χ primitive mod q} max_{0≤t≤T}|ψ(t,χ)|
 ≤ C₀ [T + T^(15/16)R + sqrt(T)R²] log⁶T,
C₀ = 5 + 16(2/log 2)^4.
```

This is an uncentered primitive character mean, including modulus one and
every natural endpoint from zero to T, with a proved inverse-character
variant. The sixth logarithmic power includes the harmonic large-sieve
loss. The familiar sharper middle exponent 5/6 from a different classical
cutoff choice is not claimed by this formal theorem.

Write `P(T,r)` for the sum of the centered maxima
`max_{0≤t≤T}|ψ(t,χ)−1_(χ principal)t|` over primitive characters modulo r.
The actual centered large-conductor tail is also proved in `VaughanMeanValue`:
for `T≥256` and `1≤R₀≤Q≤sqrt T`,

```text
Σ_{R₀<r≤Q} P(T,r)/φ(r)
 ≤ C₀ log⁶T [T/R₀ + T^(15/16)(1+log(Q/R₀)) + 2sqrt(T)Q].
```

This tail excludes conductor one, so primitive characters in it are
nonprincipal and their centered and uncentered maxima agree. The finite
progression reduction now combines this actual tail with the centered
small-conductor mass and the explicit error `Q(log Q+2sqrt(T)log T)`.
The checked small-conductor counting bound turns a supplied uniform centered
bound E into R₀E. Versions with `min(R₀,Q)` and a zero tail handle `Q<R₀`
and `Q=0`; these finite statements do not prove the required bound E.

The final asymptotic assembly is now checked.
`SiegelWalfiszMaximal` proves `PointwiseSiegelWalfisz.maximal` in namespace
`TwinPrime.Analytic`. It turns
the uniform centered pointwise statement into the actual finite endpoint
maximum, including primitive conductor one. For requested exponents `A,B>0`,
it applies pointwise SW with conductor exponent `B+1`. Endpoints
`t≤T/log^(A+2)T` use the elementary bound `t log t+t`; the remaining endpoints
eventually satisfy `t≥sqrt T`, `log t≥(log T)/2`, and the pointwise threshold.
The growing conductor condition transfers from `r≤log^B T` to
`r≤log^(B+1)t`. The resulting constant is `max(2,C·2^A)`; no maximum over a
character-dependent collection of thresholds is silently taken.

`BombieriVinogradovFromSW` proves both
`MaximalSiegelWalfisz.bombieriVinogradov` and
`PointwiseSiegelWalfisz.bombieriVinogradov`. For every requested real `A>0`,
the proof chooses BV exponent `B=A+9`, the natural conductor cutoff
`R₀=ceil(log^(A+9)X)`, and the exact endpoint `T=2X+2`. Maximal SW is used
with error exponent `2A+12` and conductor exponent `A+10`. The checked
small-conductor budget, large-conductor tail, and primitive replacement error
give one threshold and a constant `K>0`, uniform over every admissible natural
`Q`, such that

```text
Σ_{1≤q≤Q} progressionMaxError (2X+2) q ≤ K X/log^A X
  whenever Q≤sqrt(X)/log^(A+9)X.
```

This is exactly the repository's `MaximalBombieriVinogradov`, including its
centering, residue maximum, natural endpoints, and cases `Q<R₀` and `Q=0`.
The asymptotic parameter and threshold choices are proved, not extra inputs.
Independent centered `PointwiseSiegelWalfisz`, including conductor one, remains
the distribution hypothesis. It must be established without the BV-derived
ordinary ψ estimate to avoid a circular argument. None of these completed
mean-value or conductor estimates proves the signed bound `(B*)` or the
conjecture.

### Addendum: analytic continuation and proved zero-free regions

[CharacterDirichletTail.lean](../TwinPrime/Analytic/CharacterDirichletTail.lean)
now supplies a concrete analytic ingredient toward independent SW. For a
primitive character modulo `q>1`, natural `1≤M≤N`, and complex `s` with
`σ=Re(s)>0`, it proves

```text
‖Σ_{M<n≤N} n^(−s)χ(n)‖
 ≤ sqrt(q)(1+log q) M^(−σ)(1+‖s‖/σ).
```

The proof bounds the variation of the complex power by
`(‖s‖/σ)(a^(−σ)−b^(−σ))` for `0<a≤b`, telescopes this in the exact finite
Abel identity, and uses the proved Pólya–Vinogradov bound for each interval
`(M,t]`. This retains the boundary term and needs no extra factor of two for
a difference of prefixes.

The continuation step is now proved in
[CharacterDirichletContinuation.lean](../TwinPrime/Analytic/CharacterDirichletContinuation.lean).
The ordered partial sums converge locally uniformly on `Re(s)>0`; holomorphy
and analytic uniqueness identify their limit with Mathlib's actual
`LFunction χ s`. The displayed truncation bound therefore holds for
`‖LFunction χ s−Σ_{1≤n≤M}n^(−s)χ(n)‖` throughout this half-plane, for
primitive `q>1`. It does not assert absolute/unconditional summability in
`0<Re(s)≤1`.

The principal pole is handled separately by
[ZetaTruncation.lean](../TwinPrime/Analytic/ZetaTruncation.lean) and
[ZetaContinuation.lean](../TwinPrime/Analytic/ZetaContinuation.lean). For
`M≥1`, `σ=Re(s)>0`, and `s≠1`, the proved actual-zeta estimate is

```text
‖ζ(s)−Σ_{1≤n≤M}n^(−s)−M^(1−s)/(s−1)‖ ≤ (‖s‖/σ) M^(−σ).
```

The regularized approximants converge locally uniformly to the entire
function `Z(s)=(s−1)ζ(s)`, with regularized value `Z(1)=1`; their error bound
includes `s=1`. Raw zeta-series convergence in the strip is not claimed.

[LFunctionGrowth.lean](../TwinPrime/Analytic/LFunctionGrowth.lean) proves
primitive `q>1` growth on `σ≥δ>0`, `‖s‖≤H` bounded by
`1+sqrt(q)(1+log q)(1+H/δ)`, and Cauchy estimates for all iterated derivatives.
[LFunctionLowerBound.lean](../TwinPrime/Analytic/LFunctionLowerBound.lean)
proves `‖Lχ(c)‖≥1/4` when `Re(c)≥2`, for every positive modulus and character.
Combining these with Jensen,
[LFunctionZeroCount.lean](../TwinPrime/Analytic/LFunctionZeroCount.lean)
proves for primitive `q>1` and `Re(c)=2` that the actual number of zeros,
with analytic multiplicities, in the closed radius-`5/4` disk satisfies

```text
Nχ(c) ≤ [log 16 + 2 log q + log(‖c‖+2)] / log(6/5).
```

The outer radius is `3/2`; this is a zero count, not zero exclusion.
[LFunctionLogDerivative.lean](../TwinPrime/Analytic/LFunctionLogDerivative.lean)
also proves the actual twisted-von-Mangoldt formula for `−Lχ′/Lχ`, its norm
majorant `Re(−ζ′/ζ(σ))`, and the `3-4-1` nonnegative combination of the
negative log derivatives of `ζ(σ)`, `Lχ(σ+it)`, and `Lχ²(σ+2it)`.
These results hold for `σ>1`, every positive modulus, and every character;
they do not assume `χ²` primitive.

The quantitative local expansion is now proved.
[HolomorphicLog.lean](../TwinPrime/Analytic/HolomorphicLog.lean) constructs
the normalized holomorphic logarithm of a nonvanishing function on a ball.
[AnalyticLogDerivativeBound.lean](../TwinPrime/Analytic/AnalyticLogDerivativeBound.lean)
uses Borel–Carathéodory and Cauchy to prove
`‖g′/g(z)‖≤144[1+log(M/‖g(c)‖)]` on the closed unit disk when `g` is
holomorphic, nonvanishing, and bounded by `M` on the radius-`5/4` ball.

[HolomorphicZeroRemoval.lean](../TwinPrime/Analytic/HolomorphicZeroRemoval.lean)
constructs the quotient after removing the actual zeros, with exact
factorization even at the removed zeros.
[ZeroFactorBounds.lean](../TwinPrime/Analytic/ZeroFactorBounds.lean) controls
that same quotient on the outer closed disk and at its center.
[ZeroFactorLogDerivative.lean](../TwinPrime/Analytic/ZeroFactorLogDerivative.lean)
proves the finite-product logarithmic derivative with actual divisor
multiplicities. Combining these results with Jensen,
[LocalLogDerivativeExpansion.lean](../TwinPrime/Analytic/LocalLogDerivativeExpansion.lean)
proves, for `f` holomorphic near `B̄(c,3/2)`, `f(c)≠0`, `M≥1` bounding
`‖f‖` on the outer circle, and `‖z−c‖≤1` with `f(z)≠0`,

```text
‖f′(z)/f(z)−Σρ D(ρ)/(z−ρ)‖ ≤ C[1+log(M/‖f(c)‖)],
C = 144(1+log 5/log(6/5)).
```

Here `D` is the actual analytic divisor on `B̄(c,5/4)`, and the sum has
finite support. The factor `log 5` retains both the outer-circle lower
bound `(1/4)^N` for the zero polynomial and its center upper bound `(5/4)^N`.
No zero expansion or separately bounded quotient is postulated.

[LFunctionLocalExpansion.lean](../TwinPrime/Analytic/LFunctionLocalExpansion.lean)
applies this to primitive `q>1`, replacing the right side by
`C[1+log 16+2log q+log(‖c‖+2)]` for `Re(c)=2`. On the closed unit disk,
the evaluation-point nonvanishing condition is discharged whenever
`Re(z)≥1` by the existing qualitative theorem.
[LFunctionZeroSigns.lean](../TwinPrime/Analytic/LFunctionZeroSigns.lean)
proves actual divisor support lies strictly left of one, actual zeros have
multiplicity at least one, and the real part of the local reciprocal zero
sum is nonnegative for `Re(z)>1`. A zero `β+iγ` with `β≥3/4` contributes at
least `1/(σ−β)` when evaluated at `σ+iγ`, `σ>1`, using the disk centered
at `2+iγ`. These statements retain the actual zeros and their multiplicities.

[LFunctionZeroInequality.lean](../TwinPrime/Analytic/LFunctionZeroInequality.lean)
now combines them: with
`K(q,t)=C[1+log 16+2log q+log(‖2+it‖+2)]`, for primitive `q>1` and
`1<σ≤9/8`, it proves `Re(−Lχ′/Lχ(σ+it))≤K(q,t)`. If `β+it` is an
actual zero with `β≥3/4`, the bound improves to
`K(q,t)−1/(σ−β)`. The proof retains the entire actual zero sum before
dropping its nonnegative remaining terms. The budget is also proved
nonnegative and monotone in positive conductor.

[LFunctionEulerCorrection.lean](../TwinPrime/Analytic/LFunctionEulerCorrection.lean)
proves the exact inducing logarithmic derivative and the finite correction
norm `≤log q`. It includes nonprimitive squares and principal inducing
characters; the correction sign reverses for the negative logarithmic
derivative. [ZetaLogDerivative.lean](../TwinPrime/Analytic/ZetaLogDerivative.lean)
retains `−ζ′/ζ=1/(s−1)−Z′/Z` and proves
`‖−ζ′/ζ−1/(s−1)‖≤40` on `0<‖s−1‖≤1/8`, using an actual nonzero
regularization bound on the larger radius-`1/4` disk.

The primitive-character zero-exclusion assembly is now proved.
[LFunctionInducedBound.lean](../TwinPrime/Analytic/LFunctionInducedBound.lean)
transfers the one-sided estimate to every nonprincipal character, with
correction `≤log q`, and retains the full zeta term for a principal character.
[LFunctionNonquadraticZeroFree.lean](../TwinPrime/Analytic/LFunctionNonquadraticZeroFree.lean)
applies 3-4-1 to primitive `χ` with `χ²≠1`. With
`Eₙ(q,t)=120+4K(q,t)+K(q,2t)+log q`, it proves nonvanishing for
`β≥1−1/(20Eₙ(q,t))`. The scalar contradiction in
[ZeroFreeArithmetic.lean](../TwinPrime/Analytic/ZeroFreeArithmetic.lean) is
thus connected to the actual L-function and its inducing character.

[ZetaLocalExpansion.lean](../TwinPrime/Analytic/ZetaLocalExpansion.lean)
proves the actual-zero expansion for the entire regularization `Z=(s−1)ζ`
at every height. With `J(t)=C[1+log 16+2log(‖2+it‖+2)]`, it gives
`Re(−ζ′/ζ(σ+it))≤Re(1/(σ−1+it))+J(t)` for `1<σ≤9/8`.
[LFunctionQuadraticZeroFree.lean](../TwinPrime/Analytic/LFunctionQuadraticZeroFree.lean)
uses this bound when `χ²=1`. For any
`E≥Eᵩ(q,t)=120+4K(q,t)+J(2t)+log q`, it excludes zeros with
`β≥1−1/(40E)` and `|t|≥1/(4E)`. The principal pole at twice the height
is retained and bounded by `1/(5a)` for `a=1/(4E)`.

[LFunctionConjugateZeros.lean](../TwinPrime/Analytic/LFunctionConjugateZeros.lean)
proves global conjugation of the inverse-character L-function for
nonprincipal characters, its same-character and derivative forms when
`χ²=1`, and lower bounds from two distinct actual zeros.
[LFunctionNearOneZeros.lean](../TwinPrime/Analytic/LFunctionNearOneZeros.lean)
sets `E₀(q)=40+K(q,0)` and `ε=1/(16E₀)`. The rectangle
`Re(ρ)≥1−ε`, `|Im(ρ)|≤ε` contains at most one zero for a fixed primitive
character modulo `q>1`. Its actual meromorphic order is one, and it is real
when `χ²=1`. The proof compares the zero sum's upper bound `5E₀` with
contribution at least `3E₀` per zero, retaining each integer multiplicity.

[LFunctionZeroFreeRegion.lean](../TwinPrime/Analytic/LFunctionZeroFreeRegion.lean)
combines the branches with `R(q,t)=Eₙ(q,t)+Eᵩ(q,t)+4E₀(q)`. In

```text
β ≥ 1−1/(40R(q,t)),
```

any actual zero of a primitive character modulo `q>1` is real and simple,
and the character satisfies `χ²=1`. There is at most one such zero for that
fixed character. The proof handles the different height-dependent budgets:
large heights use the generalized quadratic bound with `E=R`, while
`R≥4E₀` places the remaining zeros in the same near-one rectangle.
Simplicity is explicitly `meromorphicOrderAt Lχ (β:ℂ)=1`, not a truncated
or assumed multiplicity statement.

The principal zero-free region is also proved independently in
[ZetaZeroFree.lean](../TwinPrime/Analytic/ZetaZeroFree.lean). With
`Eζ(t)=120+4J(t)+J(2t)`, the actual entire regularization `Z` is nonzero
for `β≥1−1/(80Eζ(t))`, including at `s=1`. Its separate actual-zeta
corollary retains `β+it≠1`. At small heights the proved local nonvanishing
disk for `Z` applies. At larger heights conductor-one 3-4-1 retains both
principal poles, and gives the contradiction `320Eζ/21≤241Eζ/17`.
No BV-derived prime estimate is used.

[ZeroFreeLogarithms.lean](../TwinPrime/Analytic/ZeroFreeLogarithms.lean)
proves `R(q,t)≤100C[1+log q+log(|t|+4)]` and
`Eζ(t)≤100C[1+log(|t|+4)]`, with the same explicit absolute constant `C`.
It transfers the actual theorems to logarithmic regions of widths
`1/[4000C(1+log q+log(|t|+4))]` for primitive characters and
`1/[8000C(1+log(|t|+4))]` for zeta. The former retains the possible unique
real simple zero for each character; the latter has no zero, with `s≠1`
still required for the actual-zeta corollary. These are finite uniform
comparisons and proved corollaries, rather than asymptotic assumptions.

This per-character theorem is not a uniqueness assertion across characters
or moduli, and it gives no Siegel-type lower bound for the possible
exceptional zero's distance from one. That quantitative control and uniform
inversion/Perron estimates, including independent conductor-one prime
distribution, remain unproved; the new zeta zero-free theorem does not itself
establish that distribution estimate. The checked regions and exact constants are
documented in [L_FUNCTION_ZERO_FREE_ROUTE.md](L_FUNCTION_ZERO_FREE_ROUTE.md);
the broader distribution route is in
[SIEGEL_WALFISZ_ROUTE.md](SIEGEL_WALFISZ_ROUTE.md). Independent centered SW
and the signed bilinear input `(B*)` remain unproved.

### Addendum: checked zero-to-value bounds and the explicit Siegel input

[LFunctionZeroValue.lean](../TwinPrime/Analytic/LFunctionZeroValue.lean)
proves the complex-norm mean value estimate along a real segment. For a
primitive character of conductor `q>1` and an actual real zero `β∈[3/4,1]`,
the earlier growth bound gives

```text
‖Lχ(1)‖ ≤ [4+14sqrt(q)(1+log q)] * (1−β).
```

The fixed square-root conductor loss is too large for an arbitrary-power
Siegel gap. The sharper estimate is now proved in
[LFunctionNearOneGrowth.lean](../TwinPrime/Analytic/LFunctionNearOneGrowth.lean).
For `q≥256`, put `l=log q≥4`. Truncation at the actual cutoff `M=q` gives
`‖Lχ(s)‖≤10 exp(2)l` when `Re(s)≥1−2/l` and `‖s‖≤5/4`. The closed
disk of radius `1/l` about any real `u∈[1−1/l,1]` lies in that region,
with real part at least `1/2`. Cauchy's estimate proves

```text
‖Lχ′(u)‖ ≤ 10 exp(2)(log q)².
```

These are bounds for the actual primitive L-function, without a distribution
or exceptional-zero hypothesis. The finite sum uses
`n^(−Re(s))≤exp(2)/n` for `1≤n≤q`; the positive-half-plane truncation
bound controls its remainder. Primitivity and `q>1` ensure the function is
entire, so no pole lies on the Cauchy circle.

[LFunctionLogarithmicZeroValue.lean](../TwinPrime/Analytic/LFunctionLogarithmicZeroValue.lean)
then proves, for every actual real zero with `β≥1−1/log q`, `q≥256`,

```text
‖Lχ(1)‖ / [10 exp(2)(log q)²] ≤ 1−β.
```

Nonvanishing on `Re(s)≥1` supplies `β<1`. The proved logarithmic region is
narrower than `1/log q`; its possible zero is real and quadratic, so this
estimate applies to that zero. It retains the actual value `‖Lχ(1)‖`.

[LFunctionFiniteConductors.lean](../TwinPrime/Analytic/LFunctionFiniteConductors.lean)
uses qualitative nonvanishing and finite character groups to prove a
positive lower bound for `‖Lχ(1)‖` for all nonprincipal characters of every
positive modulus `q≤Q`. Combining this with the coarse derivative bound
gives a positive uniform gap for every real primitive zero with `1<q≤Q`.
Zeros below `3/4` use the trivial gap `1/4`. No quantitative dependence of
these finite-range constants on `Q` is asserted.

[SiegelZeroGap.lean](../TwinPrime/Analytic/SiegelZeroGap.lean) proves the
following conditional conversion. Its hypothesis `hvalue` is explicitly

```text
∀η>0, ∃c>0, ∀q>1, ∀ primitive χ modulo q with χ²=1,
  c q^(−η) ≤ ‖Lχ(1)‖.
```

From that hypothesis it derives, for every `ε>0`, one `d>0`, uniform over
all `q>1` and all primitive characters, such that every actual zero in the
proved logarithmic region satisfies `χ²=1`, `t=0`, and
`d q^(−ε)≤1−β`. The estimate
`(log q)²≤16q^(ε/2)/ε²` converts the input with exponent `η=ε/2` to
the explicit large-conductor constant `cε²/[160 exp(2)]`. Taking its
minimum with the finite-conductor gap at cutoff 256 covers all remaining
conductors, since `q^(−ε)≤1`. Thus the all-conductor quantifiers and
logarithmic loss are proved; the uniform hypothesis `hvalue` remains
unproved. These modules do not establish Siegel's lower bound.

### Addendum: positive four-factor coefficients and the residue

[QuadraticProductCoefficients.lean](../TwinPrime/Analytic/QuadraticProductCoefficients.lean)
proves the actual finite convolution construction for two characters of a
common modulus:

```text
aχ(n) = χ(n) for n>0,   aχ(0)=0,
c = ArithmeticFunction.zeta * aχ₁ * aχ₂ * a(χ₁χ₂).
```

Here multiplication is Dirichlet convolution. The coefficients are
multiplicative and `c(1)=1` for all characters. If `χ₁²=χ₂²=1`, every
`c(n)` is a nonnegative real, and `c(n²)≥1` for every positive integer
`n`. The finite proof uses the exact paired identity
`(aχ₂*a(χ₁χ₂))(n)=χ₂(n)(zeta*aχ₁)(n)`, the quadratic prime-value cases,
and multiplicativity. It requires neither primitivity nor distinctness.

[QuadraticProductPartialSums.lean](../TwinPrime/Analytic/QuadraticProductPartialSums.lean)
also passes its standalone check. For every real `σ`, it identifies the
actual complex finite sum `Σ_{1≤n≤X} c(n)n^(−σ)` with its real weighted
sum, proves nonnegativity and monotonicity in `X`, and proves it is at least
one whenever `X≥1`. This lower bound holds on either side of the line of
absolute convergence; it makes no infinite-series identification there.

[QuadraticProductLSeries.lean](../TwinPrime/Analytic/QuadraticProductLSeries.lean)
has passed its final standalone check and this independent review. It proves
absolute summability and the exact identity

```text
LSeries c s = ζ(s)Lχ₁(s)Lχ₂(s)L(χ₁χ₂)(s),   Re(s)>1.
```

Its entire regularization is `Z(s)Lχ₁(s)Lχ₂(s)L(χ₁χ₂)(s)`, under the
explicit conditions that all three character factors are nonprincipal.
Distinct nonprincipal quadratic characters satisfy those conditions. The
value at one and the punctured limit of `(s−1)` times the unregularized
product are exactly `Lχ₁(1)Lχ₂(1)L(χ₁χ₂)(1)`, which is nonzero by
qualitative nonvanishing. Equal characters or principal factors are not
silently included in the entire, simple-pole assertions.

The missing analytic step is a quantitative comparison of an actual
positive finite or smoothed coefficient sum with this residue, retaining
conductor dependence, inducing Euler factors, and any auxiliary real zero.
Finite positivity and a nonzero residue alone do not prove `hvalue`.
The proposed continuation is recorded in
[SIEGEL_EXCEPTION_ROUTE.md](SIEGEL_EXCEPTION_ROUTE.md). Independent centered
SW, its necessary uniform inversion estimates, and the signed input `(B*)`
remain unproved.

### Addendum: checked convolution cancellation and the actual four-factor main term

Independent review of this checkpoint found no missing premise, coefficient
support, endpoint, pole, or constant issue. The integrated build passed
8,839 jobs. The axiom audit passed for 812 selected declarations, using only
`propext`, `Classical.choice`, and `Quot.sound`, with zero errors. This
checkpoint adds 85 public theorems in 14 modules; the source scan of 184
files was clean. These verification results do not establish the remaining
Siegel or prime-distribution obligations.

[CharacterPeriodSum.lean](../TwinPrime/Analytic/CharacterPeriodSum.lean)
proves exact reduction of `Σ_{1≤n≤N}χ(n)` to its remainder sum modulo q
for every nonprincipal character of a positive modulus q. Its norm is
bounded by `N mod q`, hence by q; the separate length bound is N and the
general interval bound is `2q`. The finite identities include N=0 and
empty intervals. Imprimitive characters are included, and principal
characters are excluded only from the cancellation statements.

[CharacterConvolutionMass.lean](../TwinPrime/Analytic/CharacterConvolutionMass.lean)
bounds the absolute mass of a triple character convolution by
`x(1+log x)²`, for x≥1, without cancellation assumptions.
[CharacterConvolutionCancellation.lean](../TwinPrime/Analytic/CharacterConvolutionCancellation.lean)
uses exact real-endpoint hyperbola identities to give `3q√x` for two
nonprincipal factors and `10q²x^(2/3)(1+log x)` for three.
[CharacterConvolutionPower.lean](../TwinPrime/Analytic/CharacterConvolutionPower.lean)
absorbs the logarithm using `1+log x≤13x^(1/12)`, yielding
`130q²x^(3/4)` and the matching all-natural-prefix bound, including zero.
All characters share the same positive modulus; primitivity is unnecessary.

[PowerDirichletTail.lean](../TwinPrime/Analytic/PowerDirichletTail.lean)
and [PowerDirichletContinuation.lean](../TwinPrime/Analytic/PowerDirichletContinuation.lean)
derive locally uniform ordered convergence and holomorphy on Re(s)>α
from `‖Σ_{n≤N}a(n)‖≤C N^α`, for α,C≥0. The tail after M≥1 is bounded
by `2C M^(α−Re(s))(1+‖s‖/(Re(s)−α))`. The factor two accounts for
changing the partial-sum anchor. Convergence and holomorphy are proved
conclusions, not extra inputs.

For `f=aχ₁*aχ₂*aχ₃`, with all three factors nonprincipal,
[CharacterConvolutionContinuation.lean](../TwinPrime/Analytic/CharacterConvolutionContinuation.lean)
identifies this ordered limit with the actual product of three L-functions
on Re(s)>3/4, using absolute convergence on Re(s)>1 and analytic uniqueness.
At one, it proves

```text
Σ_{1≤n≤M} f(n)/n → R = Lχ₁(1)Lχ₂(1)Lχ₃(1),
‖R−Σ_{1≤n≤M} f(n)/n‖ ≤ 1300q²M^(−1/4),  M≥1.
```

This is ordered convergence, not absolute summability at one. The
arithmetic-function type is retained before coercion to a sequence, so
the products remain Dirichlet convolutions rather than pointwise products.

[ZetaConvolutionAsymptotic.lean](../TwinPrime/Analytic/ZetaConvolutionAsymptotic.lean)
proves the generic finite error `(1+25C)x^(4/5)(1+log x)²` from the
stated cancellation and mass bounds. With `y=x^(4/5)`, `z=x^(1/5)`,
the head costs `y(1+log x)²`, the other strip costs `4Cy`, the overlap
costs `Cy`, and the reciprocal tail costs `20Cy`. The last term includes
the factor two from flooring y. The exact relation yz=x and x≥1 keep
every endpoint valid, including x=1.

[CharacterConvolutionAsymptotic.lean](../TwinPrime/Analytic/CharacterConvolutionAsymptotic.lean)
discharges both generic premises with the proved character estimates and
identifies the main coefficient. It proves, for every real x≥1,

```text
‖Σ_{1≤n≤floor(x)} (ζ*aχ₁*aχ₂*aχ₃)(n) − xR‖
 ≤ (1+3250q²)x^(4/5)(1+log x)².
```

Here ζ is the arithmetic zeta coefficient function and `25·130=3250`.
For distinct nonprincipal quadratic χ₁,χ₂, setting χ₃=χ₁χ₂ identifies
R with `regularizedQuadraticLFunctionProduct χ₁ χ₂ 1`. All three
nonprincipal hypotheses are preserved; principal-factor cases with a
different pole order are not included. The bound uses the common modulus,
including its inducing Euler factors.

The auxiliary-real-zero weighted Abel comparison is still unproved.
This explicit summatory error and the earlier positive coefficients do
not yet yield the conductor-uniform Siegel value lower bound. Quantitative
prime-sum inversion, independent principal ψ estimates, uniform centered
Siegel–Walfisz, and `(B*)` also remain open. The current detailed status is
recorded in [SIEGEL_WALFISZ_ROUTE.md](SIEGEL_WALFISZ_ROUTE.md)
and [SIEGEL_EXCEPTION_ROUTE.md](SIEGEL_EXCEPTION_ROUTE.md).

### Addendum: centered residue comparison and the uniform Siegel value theorem

This checkpoint supersedes the earlier statements that the weighted
residue comparison and the uniform Siegel value bound were still missing.
Independent review of the final source, its intermediate estimates, and
the quantifier order found no missing premise, endpoint, inducing-factor,
pole, or circularity issue. The final value theorem and unconditional
zero-gap wrapper passed standalone Lean checking with exit zero and no
warnings. The completed full-project build passed 8,857 jobs. The axiom
audit passed for 896 selected declarations, including 84 new public
theorems in 18 modules, with zero errors and only `Classical.choice`,
`propext`, and `Quot.sound`. The scan of 202 source files was clean.
The printed value and zero-gap theorem types retain no supplied `hvalue`
input. The historical counts above describe their own earlier checkpoints.

[QuadraticCenteredCoefficients.lean](../TwinPrime/Analytic/QuadraticCenteredCoefficients.lean)
centers the actual coefficients by the actual residue λ. Its natural
prefix bound is `441(1+3250q²)N^(9/10)`, including N=0.
[QuadraticCenteredFunction.lean](../TwinPrime/Analytic/QuadraticCenteredFunction.lean)
constructs the entire quotient of `Freg−λZ` by s−1 using `dslope`;
away from one it equals `F−λζ`. All three nonprincipal conditions are
retained. [QuadraticCenteredContinuation.lean](../TwinPrime/Analytic/QuadraticCenteredContinuation.lean)
identifies the ordered centered series with that function on Re(s)>9/10.
It proves the actual error `18522(1+3250q²)M^(−1/20)` for M≥1 and
19/20≤β≤1. Absolute convergence is used only to start the identification
on Re(s)>1, and the removable value at one is handled separately.

[QuadraticResidueComparison.lean](../TwinPrime/Analytic/QuadraticResidueComparison.lean)
uses this tail and the exact zeta correction. The positive finite weighted
sum has real part at least one. If Re F(β)≤0 and the tail is at most 1/2,
the retained residue term yields `(1−β)/(4M^(1−β))≤‖λ‖`.
The ceiling cutoff discharges the tail, rather than assuming it small.
Its upper bound gives

```text
δ/(4 A^δ q^(40δ)) ≤ ‖λ‖,
δ=1−β>0,  A=2(37044·3251)^20,  19/20≤β<1.
```

The nonpositive-product hypothesis is sufficient in both branches of the
later dichotomy. The proof does not reverse a zero-to-small-value estimate
or infer a zero from an estimate for L(1).

[LFunctionInducedValue.lean](../TwinPrime/Analytic/LFunctionInducedValue.lean)
proves the multiplier bound `1+log Q` at one by a finite prime-subset
expansion and an injective map to the integers counted by H_Q. It also
proves Euler nonvanishing on Re(s)>0 and the exact zero equivalence away
from one. [CharacterCommonLevel.lean](../TwinPrime/Analytic/CharacterCommonLevel.lean)
preserves both primitive conductors under induction to Q=q₀q. Distinct
conductors ensure a nonprincipal product without claiming it is primitive.
The independent period bound gives `‖Lη(1)‖≤5+log Q` for this possibly
imprimitive product. Consequently
[QuadraticAuxiliaryComparison.lean](../TwinPrime/Analytic/QuadraticAuxiliaryComparison.lean)
retains precisely three logarithms and proves

```text
δ/[20‖Lχ₀(1)‖ A^δ Q^(40δ)(1+log Q)^3] ≤ ‖Lχ(1)‖
```

from the actual nonpositive common-level product at β. The original
auxiliary L-value is nonzero by qualitative nonvanishing, so division by
its norm is justified.

[SiegelValuePower.lean](../TwinPrime/Analytic/SiegelValuePower.lean)
proves the logarithmic absorption for δ≤ε/80, with
`k=δ/[20‖Lχ₀(1)‖ A^δ(1+6/ε)^3]>0` and lower bound `kQ^(−ε)`.
[SiegelValueFromComparison.lean](../TwinPrime/Analytic/SiegelValueFromComparison.lean)
uses `min(c_finite,kq₀^(−ε))`. The factor q₀^(−ε) is retained;
the finite minimum covers every q≤q₀, including other characters of the
same conductor. Thus the constant is uniform over the subsequent target
character and conductor quantifiers.

The actual final theorem
[siegel_value_lower_bound](../TwinPrime/Analytic/SiegelValue.lean#L23)
proves

```text
∀ ε>0, ∃ c>0, ∀ q>1, ∀ primitive χ modulo q,
  χ²=1 → c q^(−ε) ≤ ‖Lχ(1)‖.
```

It fixes δ₀=min(1/20,ε/80). If a primitive quadratic zero lies in
[1−δ₀,1), that witness is fixed before quantifying over target characters,
and exact induction supplies an actual product zero. If there is no such
zero, the kernel-checked primitive character modulo four supplies the
auxiliary character. Primitive-inducing zero equivalence transports the
global exclusion to all three nonprincipal quadratic factors. Reality,
continuity, positivity at two, and qualitative nonvanishing at and above
one give positive L-values at 1−δ₀; the proved zeta truncation gives a
negative zeta real part there. Hence the product is negative, discharging
the same comparison premise. The dichotomy assumes no value bound,
Siegel–Walfisz estimate, prime-sum asymptotic, or cross-character zero
uniqueness. Its classical witness choice does not give an effective c.

[SiegelZeroGapUnconditional.lean](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean)
now supplies the proved value theorem to the existing conversion. For
each ε>0 it obtains one d>0, uniform over all primitive q>1 and every
actual zero β+it in the proved logarithmic region, such that χ²=1,
t=0, and `dq^(−ε)≤1−β`. The region hypothesis remains explicit in
both the general theorem and its real-zero specialization. No value
lower-bound premise remains. This does not assert a Page-type uniqueness
result across different characters.

The classical uniform value theorem is not Siegel–Walfisz. Quantitative
inversion for the von Mangoldt sums, an independent principal ψ estimate,
and the full uniform centered `PointwiseSiegelWalfisz` proposition remain
unproved. Consequently the proved SW-to-BV implication still requires its
input, and the independent signed estimate `(B*)` and the twin-prime goal
remain open.

## 2026-09-05 — Smoothed Mellin and contour verification

The latest checked chain is documented in
[MELLIN_CONTOUR_ROUTE.md](MELLIN_CONTOUR_ROUTE.md). It adds actual ramp and
principal pole inversion, the justified Dirichlet-series interchange,
smoothed Mangoldt inversion for every positive modulus, widened local
expansions, full complex strip norm bounds, finite rectangle shifts,
two-tail truncation, and exact finite unsmoothing. The final primitive
smoothed contour theorem has only the stated character and numerical
conditions: no value, zero-free, inversion, or distribution premise.
The polylogarithmic width and budget constants are uniform before q.

Source review checked the actual definitions and proof connections, particularly
the omitted zero coefficient, vanishing integer-boundary ramp weight,
contour orientation and 1/(2π) normalization, both tails, nonnegative
analytic multiplicities, height margin two, both width halvings, and
the positive-real reciprocal-power identity. The principal pole inverse
is (x−1)^2/(2x); its complete error assembly is still required. The
finite difference keeps the real floor endpoints and the short-interval
coefficient mass before using the Mangoldt bound.

All 102 new public theorems in 16 modules passed standalone Lean checks
without warnings. The full root build passed 8873 jobs; the integrated
axiom audit passed 998 selected declarations with only Classical.choice,
propext and Quot.sound and no errors. The source scan covered 218 project
Lean files including the root import file, with no holes or trust bypasses.
The final checks and integration were completed. This checkpoint has
implementation-source review and kernel verification; it does not claim a
separate completed external mathematical review of the assembled contour theorem.

The earlier Siegel checkpoint remains valid. The new inversion and
contour results still require uniform asymptotic absorption and principal
assembly to yield centered sharp-sum Siegel–Walfisz. The twin-prime
endpoint retains SW and B* as explicit inputs, and the conjecture remains unproved.

## 2026-09-05 — Completed centered SW and the single-input endpoint

The new [classical proof map](CLASSICAL_DISTRIBUTION_THEOREM.md) records
the completed principal contour, uniform asymptotic absorption, centered
smoothed estimate, and exact finite-difference passage to sharp sums.
The independent theorem now has type `PointwiseSiegelWalfisz`, with no
distribution argument. Its existing maximalization and BV assembly give
`MaximalBombieriVinogradov`; the existing contraction gives `MertensLogSix`.

Source review covered the following connections against the source definitions:

- The principal inverse subtracts actual integrable functions. The
  regularized logarithmic derivative has the correct negative sign,
  and the exact pole inverse contributes x/2 with error at most one.
- The conductor-one evaluation width uses the same positive d as the
  primitive family. Both halvings and the height margin two are retained;
  its zeta budget is at most twice the conductor-one primitive budget.
- The right-line identity is exact. The principal tail retains the extra
  reciprocal c−1 term. The three error terms and the exponential threshold
  are uniform before quantifying over width, norm budget, conductor, or character.
- Centered finite differences retain the principal h/2 correction and
  the full `(h+1)log(x+h)` short-interval error. The coefficient product
  order is reconciled with the existing `characterPsi` definition.
- At h=x/(log x)^(A+2), stronger smoothed exponent 2A+4 suffices for
  sharp exponent A. The common threshold applies at the larger endpoint,
  and the conductor bound transfers by monotonicity for B>0.
- Natural restriction identifies the floor and `Icc 1 T = Ioc 0 T`.
  The final threshold is at least two, and the main term is T for the
  principal character. Conductor one is handled explicitly.

The full root build passed 8883 jobs. All 43 new public theorems in ten
modules occur in the 1041-declaration integrated audit, with only the
three standard axioms and no errors. The source scan covers 228 project
Lean files, with no holes, project axioms, or trust bypasses. No new
module warnings were reported. This is implementation-source review and Lean
verification, not a separate independent mathematical review.

The new endpoint `twinPrimeConjecture_of_signed_bilinear` has exactly one
premise: the cofinal fixed-shift B* lower bound with the original fifth-root
cutoffs and constant. M3 is complete; B* and the unconditional twin-prime
proof are not. Standard-axiom reports do not discharge that remaining premise.

## 2026-09-05 — Complete dispersion family and large-gcd review

The [dispersion proof map](DISPERSION_GCD_ROUTE.md) records the eight new
modules. A separate AI-assisted review checked the saved source and mathematical
scope, separately from the root build and kernel audit. The review found
no errors. In particular:

- Applying the existing dyadic assignment to n−1 gives the exact required
  (2^i,2^(i+1)] endpoints. Factors equal to one are excluded by U,V≥1.
  The signed pair sum is reindexed exactly, with all product cutoffs retained.
- The depth-squared bound is applied to the complete growing family. The
  diagonal sum has bound O(X L^4/sqrt U), which absorbs every fixed extra
  logarithmic loss at the primary cutoff.
- The rectangle cover by common divisors is an upper bound; multiple
  counting is harmless. The inverse-square tail gives AB/G. The dispersion
  pair sum retains both orientations and excludes its diagonal d=e.
- The large-gcd dispersion estimate keeps the mass T and absolute value
  in the correct places. At G=ceil(L^10), its root sum is O(X/L). No claim
  of arbitrary additional logarithmic savings is made for this fixed cutoff.
- The original-factor restriction uses gcd(d,r), a different range from
  the dispersion restriction gcd(d,e). It includes d=r, retains β and μ,
  and gives an exact split of the actual B. Its O(X/L^6) estimate implies
  precisely (B−B_small)/X→0 without a cancellation hypothesis.
- The residual dispersion budget is sum sqrt(max(T*Off_small,0)). Neither
  its vanishing nor cancellation of the remaining original-factor sum is
  proved. The global inequalities do not silently replace this residual
  by a signed sum over boxes.

All 62 new public theorems occur in the integrated audit of 1103 unique
selected declarations. Only the three standard axioms occur; no errors
were reported. Full root build passed 8891 jobs. The 236-file source scan
found no proof holes, project axioms, or trust bypasses, and the new
modules compiled without warnings. The printed twin-prime endpoint still
has the original cofinal B* premise. These estimates do not complete M4
or establish an unconditional twin-prime theorem.

## 2026-09-05 — Active band and simultaneous exceptional-range audit

The latest proof chain is in Sections 7–8 of
[DISPERSION_GCD_ROUTE.md](DISPERSION_GCD_ROUTE.md). Independent read-only
review covered all four new modules and the separate paper centering note.
No mathematical or scope issue was found.

The strict inequalities X<4MN and MN<2X are forced by an actual entry,
including both right-closed upper endpoints. Three product-exponent levels
suffice; the injection retaining the left exponent proves at most 3D boxes.
All discarded entries are exactly zero, so signed and positive-part sums
transport without an unproved support premise. The constants 12a/L² and
24a/L⁷ follow with a=2/log2 and the original cutoff G=ceil(L^10).

The prime-square proof uses μ(d)≠0 to force squarefree d before making
the two-allocation cover. It permits overlaps and enlarges prime bases to
all positive integers only for an upper bound. Hyperbola floors and empty
ranges are retained. The 8XL³/H estimate is factorwise absolute mass,
including p² wholly in r; its logarithmic specialization is 8X/L⁷.

The joint residual uses the exact actual pair sum. Its removed intersection
is bounded by that absolute mass, not by restricting a signed-tail theorem.
The primary difference bound is (24a+8)X/L⁷, and the normalized actual
difference tends to zero. The survival theorem keeps every squarefree input,
so the result has not removed the rough negative core or proved its sign.

The paper centering review retains both moving Mertens endpoints, the
correct supermultiplicative totient inequality, and one uniform threshold.
Its final constant 576·10⁶KCφ/log2 and reciprocal-cubic logarithm are correct.
The same deterministic energy bound shows the centered and raw full-moment
root budgets differ by o(X); this normalization alone supplies no easier
vanishing estimate. This paper assembly is explicitly distinguished from
Lean-proved inputs and the still-unproved centered variance.

Verification: 45 new public theorems in four modules; full root build 8895
jobs; integrated audit 1148 unique selected declarations with only the
standard three axioms and no errors; 240 project Lean files scanned clean.
No new module warnings. Printed theorem types preserve all numerical
conditions and still retain the cofinal signed B* premise at the twin-prime
endpoint. This checkpoint is verified partial progress, not completion.

## 2026-09-05 — Prime-beta error and coefficient review

Independent reading covered all seven new modules in the
[prime-beta proof map](BILINEAR_PRIME_BETA_ROUTE.md). The main review points:

* Low divisors of ab restrict exactly to a when b is U-rough. Original-beta
  cancellation for 1<a<=U includes repeated primes and b=1. The larger
  original-beta formula assumes a squarefree; the prime-only formula does not.
* Proper prime powers inside beta are bounded using the actual nonnegative
  psi-theta sum. Finite anchored Abel summation gives 3C/sqrt(V), uniformly
  in the upper endpoint, including T<V. No distribution premise is introduced.
* The divisible-right-factor hyperbola count includes all positive factors,
  its floor and harmonic bounds retain endpoints, and the divisor-tail
  interchange is finite. The actual beta replacement mass is at most
  4 X L^2 times the reciprocal tail. Enlarging the domain is justified by
  nonnegative absolute weights.
* The limit allows arbitrary U(X), primary V(X), and every fixed natural
  logarithmic power. The signed-difference estimate comes from absolute mass.
* Product grouping is a genuine bijection, preserving both strict cutoffs and
  the dyadic interval. The prime-only smooth/rough identity is consequently
  connected to the same finite sum as the replacement bound.

No missing premise, sign restriction or endpoint issue was found. The paper
log-radical notation is supported by the checked sum over distinct-prime logs;
a standalone radical identity is not claimed. The paper moment S=CX+o(X)
is not an exported Lean theorem. An o(X) replacement requires positive slack
when transferring an exact lower-bound threshold.

The unresolved range has smooth a approximately X^(3/5)..X^(4/5) and prime
b approximately X^(1/5)..X^(2/5). BV for unweighted residue classes cannot
be substituted for its signed smooth-weighted prime sum. No proof here
controls its required lower-bound contribution or proves B*.

Verification: 52 public theorems in seven modules; full build 8902 jobs;
1200 unique selected declarations audited with only Classical.choice,
propext and Quot.sound, zero errors; 247 project Lean files scanned clean.
All new modules compiled without warnings. M4-M6 are not marked complete.

## 2026-09-05 — Signed mixed-cutoff removal review

The [cutoff-change proof map](CUTOFF_SHIFT_ROUTE.md) records an actual
signed range estimate using the independent classical inputs. Review of all
seven new modules found no missing arithmetic or distribution premise.

The exact identity has sign B(U,V)-B(U,W)=I(U,V)-I(U,W) when V,W<=X.
The progression cap is the full product UV, with the shared-prime main
correction retained. Polynomial slack a<1/2 absorbs the BV logarithmic
restriction, and the summed even-modulus error has exponent a+1/2<1.
The product condition with primary U also implies W<=X eventually, making
the constant-five logarithmic comparison valid at both growing cutoffs.

The generic product theorem and quarter specialization are unconditional.
The quarter prime-beta replacement uses the earlier uniform absolute bound
and monotonicity of the negative half-power under quarterCutoff>=primaryCutoff.
Its extra logarithmic savings do not imply that rate for the signed cutoff
change. The latter controls the complete sum, not an arbitrary restriction.

The mixed smooth/rough formula retains m_U(a). The middle-prime negative
class is checked explicitly, including b=1 and repeated factors in b.
The remaining prime-quotient sum retains both smoothness and signed weights;
replacing it by the ordinary BV progression sum is unsupported.

Version-pinned primary-source comparisons test actual coefficient hypotheses,
not just distribution exponents. The seven-prime example in the note has a
nonzero coefficient but cannot fit any balanced three-factor convolution
at the required level. It refutes factorability of this weight without
asserting that a corresponding shifted value is prime. The other smooth-
function and prime-factor-correlation results inspected have incompatible
coefficient or support requirements. No broad impossibility theorem is claimed.

Verification: 38 public theorems in seven modules, full build 8909 jobs,
1238 unique selected declarations audited using only Classical.choice,
propext and Quot.sound, zero errors. All new modules compiled without
warnings. The 254-file source scan found no proof holes or trust bypasses.
B* and the complete Twin Primes proof remain unproved.

## 2026-09-05 — Finite classical center and logarithmic precision review

The [finite-center proof map](CLASSICAL_CENTER_PRECISION.md) and all seven
new modules were independently reviewed. J has signs +XS+FM-XQ, and its
exact correlation remainder is R_A+R_H-R_I. Positive cutoffs and UV<=X
justify both support endpoints. The odd-error constant is 2+4+2=8 and the
three even-modulus budgets are all retained.

The power-level BV proof chooses logarithmic exponent k+1 for the isolated
L^k-weighted sum, before selecting its eventual threshold. The product
power gap absorbs the BV logarithmic level restriction. The even estimate
uses exponent a+1/2<1 and logarithmic power k+2. k=0 and zero modulus caps
are covered in the general error lemmas; the combined correlation theorem
explicitly requires eventual cutoff positivity. No target-equivalent
distribution or signed hypothesis enters these estimates.

The centered cutoff identity retains the two actual finite Q terms.
Quarter applications use product exponents 2/5 and 9/20 and the proved
unconditional BV theorem. The prime-beta bridge first takes absolute values
and then decreases log(4X+4) to log(2X+2). Its triangle inequality keeps the
quarter center unchanged. These estimates do not claim the same rate for
the uncentered cutoff change or for an arbitrarily restricted signed sum.

The new conditional endpoint correctly combines actual center error and
Epp, scaled by log^k/X, into a limit zero. Its cofinal gain is selected
after the error threshold and supplies strict W2>Epp. The positive gain
remains visible in the printed theorem type and is not proved. Every
fixed logarithmic precision does not imply a power saving or a square-root
error. The countermodel in the note is explicitly a check on abstract
limit-based reasoning, not a countermodel of the arithmetic definitions.

The source review also checked the mean-square theorem's uniformity and
the bounded-multiplicative hypotheses of the almost-all-scales theorem.
Neither is treated as a result about the actual remaining signed prime
quotient. No positive constant or sublinear signed gain was obtained.

Verification: 17 public theorems, seven modules; full root build 8916 jobs;
1255 unique selected declarations audited using only Classical.choice,
propext and Quot.sound, zero errors. All new modules compile without
warnings. All 261 project Lean files passed the source scan. The original
PLAN assessment remains unchanged; M4-M6 remain incomplete.

## 2026-09-05 — Logarithmic smoothing and signed-gain audit

The [new paper calculation](SMOOTHED_SIGNED_GAIN_REVIEW.md) has a genuine
order-X displacement, not an unproved twin-prime margin. Independent review
checked all finite telescoping endpoints and the exact averaged center before
taking limits. The error is bounded uniformly by the same cap RW, so no
moving-average interchange is needed. The shared correction has a bounded
majorant tending to zero uniformly in W; its logarithmic average vanishes.

The smoothed quadratic totient sum has leading term 2C logR by an explicit
logarithmic integral. The odd Mangoldt/totient sum differs from sum Lambda/n
by a bounded prime-power correction, giving leading coefficient one. These
paper bridges yield Qbar->Cv/r and Jbar/X->C[1+(1-v)/r]. Subtraction against
the sharp center gives the negative displacement -C(1-v)/r without assuming
an asymptotic for W2. The fixed-power window cancels the additional boundary.
The note clearly states that these new calculations are not Lean theorems.

The Goldston-Yildirim specialization is a valid fixed-shift weighted second
moment under ordinary BV: k=3, shifts(0,2), multiplicities(2,1), and
R<X^(1/4-epsilon). The subsequent absolute-value bound retains a sqrt(logX)
loss. The Fouvry-Radziwill candidate has the right coefficient class but an
incompatible length inequality at Q comparable to X; the Wright extension
retains its incompatible large-factor condition. The Mellin/Fourier discussion
is limited to the proposed residue and major/minor-arc arguments, not all
possible logarithmic gains.

Exact Python diagnostics passed 4,800 averaging and 9,600 prime-beta
convolution identities. Both finite negative-change witnesses have genuine
shifted primes and exact compensation by A+H-I; the second uses the exact
primary and quarter floors. Those finite terms are distinguished from J.
No formal source changed, so no new full build or axiom audit was needed.
The existing verified formal checkpoint is unchanged. B* and the sufficient
logarithmic gain remain unproved.

## 2026-09-05 — Middle-prime sieve and weighted distribution

Independent review checked the new
[middle-prime class estimate](MIDDLE_PRIME_SIEVE_BOUND.md). The paper
linear sieve uses level D/q and threshold sqrt(D/q), hence s=2, and omits
the prime two. Every retained sieve prime is below q. The progression is
the actual shifted-Mangoldt interval with modulus qd and residue two;
its two endpoint errors are retained. The product qd has q as its unique
largest prime, so the supported aggregation has multiplicity one.

The formal Selberg route keeps 3^omega(d), rather than applying unweighted
BV to an unbounded coefficient. A weighted Cauchy inequality and the
elementary reciprocal-totient estimate give the squared-error majorant
3Y(1+log Y)^19 times the ordinary sum of actual progression errors.
Unconditional BV absorbs every fixed logarithmic loss at a fixed power
cap below X^(1/2). The total class bound keeps its exact denominator and
the extra outer logarithm; the latter is absorbed by using the error limit
at exponent k+1.

The paper constant at v=21/100 has a strict rational margin below 0.263.
The denominator's asymptotic and prime summation are still separate
formal obligations. The other signed masses are not bounded by this
calculation. Root build: 8921 jobs. Axiom/type audit: 1292 selected
declarations, all 37 new theorems included, only the three standard
axioms and zero errors. M4-M6 remain incomplete.

## 2026-09-05 — Summable denominator correction

The four follow-on modules passed standalone compilation and independent
review. The actual odd-squarefree coefficient is represented by a
multiplicative arithmetic function, including its value at zero and the
zero local factor at two. Its convolution correction has local values
-1/2 at two, 2/[p(p-2)] at odd primes, -1/[p(p-2)] at prime squares, and
zero at higher powers. The local absolute excess is bounded by 9/p^2.

Both Euler products are absolutely convergent, so multiplying the local
factors against those of the existing smoothing correction legitimately
gives total mass 1/C. The prime-two factors cancel as 1/2 times 2; no
reciprocal zero or conditional-product step is used.

The harmonic limit handles h(0) explicitly and retains the floors. Its
kernel lies in [0,1] on the positive summation range and tends to one for
each fixed positive divisor. Absolute summability therefore supplies the
entire domination hypothesis. The actual denominator limit is
S(z)/log z->1/C; the reciprocal limit uses the proved positive C.

The family substitution requires that for every threshold Z, eventually
every active z_q is at least Z. It multiplies the reciprocal inequalities
only by nonnegative weights and retains the complete weighted error.
Empty prime families cause no exception. Specific power thresholds and
the outer prime sum are still separate formal obligations.

The new total is 75 theorems in nine modules. Root build: 8925 jobs.
Axiom/type audit: 1330 unique selected declarations, every new theorem
included, only the three standard axioms, zero errors. Source and
whitespace scans passed for all 270 project Lean files. The rough-composite
paper bound does not close the signed budget; no conjecture proof or new
completed milestone is claimed.

## 2026-09-05 — Complete middle-prime bound and paper budget tests

The [class proof map](MIDDLE_PRIME_SIEVE_BOUND.md) now ends in the actual
Lean theorem T_(21/100)(X)<=0.263 C X eventually. The fixed level
a=49999/100000 supplies strict rational slack; no limiting distribution
statement at exponent one half is used. The proof includes the actual
integer support and level inequalities, uniform growth and logarithmic
rounding of thresholds, centered real-endpoint Abel summation, and the
proper-prime-power and totient replacement errors. It evaluates the
complete prime main sum and absorbs the complete weighted sieve error.
Independent reviews checked these ingredients and their assembly.

The [total-budget review](SIGNED_TOTAL_BUDGET.md) retains exact J at the
same mixed cutoffs and gives Q_tw>=0.737 C X-R-E_tot with E_tot=o(X).
It keeps all signed composite masses and every classical, beta, and
prime-power residual. Reusing the favorable composite-mass identity
does not provide an independent saving. The strongest certified positive
margin for the full sum remains zero.

The paper Buchstab test explicitly charges every removed least-prime
strip and records the vanishing beta and even-input defects. Its lower
budget reaches zero at exponent one quarter, so it cannot isolate primes
with a positive remaining budget. The scale-average test retains the
moving-cutoff coefficients after interchanging the finite sums. A direct
rough-prime Fourier selector is exact, but the inspected correlation
theorems do not give the required relative precision for the full phase
sum at shift two. These are assessments of the stated mechanisms, not
an impossibility claim about other methods.

Independent review of the scale-average test checked the finite averaging
identity and the selector's restricted domain W<m<=2X+2. The small-prime
zeros verify the qualitative nonpretentiousness hypothesis uniformly for
the varying family. The quantitative theorem still gives insufficient
absolute precision, and its separate main-term case fails its stated
prime-range hypothesis for this family. Weighted cancellation of separate
complex modes would additionally need uniform partial-sum control.

The current full build passed 8936 jobs. The axiom/type audit passed for
1396 unique selected declarations using only the three standard axioms.
Source scans passed for all 281 project Lean files. The printed class
bound has no distribution or arithmetic premise; the twin-prime endpoint
still requires a signed gain. Further substantial formalization is
conditioned on a paper improvement to the complete inequality.

## 2026-09-05 — Distribution levels and additive Fourier budgets

The [paper assessment](DISTRIBUTION_AND_FOURIER_BUDGET.md) was reviewed
for its complete-error budgets and the exact scope of its comparison
examples. The shifted Fourier phase, translated major-arc integral,
Ramanujan normalization, singular tails and support corrections agree.
Diagonal subtraction preserves the coefficient being estimated; its
global L2 norm cannot be used as a small order-X remainder.

Two independent reviews checked the nonnegative Fejer density. Its
shift-two coefficient vanishes exactly while its major total has the
desired leading constant. The statement excludes actual-prime
coefficients, full Siegel-Walfisz arc profiles, and unmodeled shifted
correlation data. The persistent-exception array separately matches
the stated averaged-shift quantifiers, including their fixed logarithmic
exponents and the possibility of a diagonal exception.

Review identified and corrected three sieve details: use a fixed
sublevel for the lower-sieve theorem; aggregate only odd squarefree
moduli, matching the hypothetical distribution input; and retain the
finite upper parameter beyond three before taking its continuous limit.
The complete upper residual and a finite parameter mesh are displayed.
Neither stronger-distribution diagnostics nor the Fourier comparisons
yield a positive margin for the actual full signed sum.

No Lean source changed in this paper checkpoint. The earlier build
and axiom/type audit remain the verified formal state; no new formal
endpoint or milestone is claimed.

## 2026-09-05 — Divisor-switching budget review

Two independent reviews checked the
[divisor-switching assessment](DIVISOR_SWITCH_BUDGET.md). The
Assing-Blomer-Li specialization, derivative constant and full Abel
residual give the stated negative leading unrestricted budget.
The fixed-polynomial obstruction is confined to its stated global
minorant class; it does not rule out other arithmetic weights.

The squarefree and shifted-prime-power defects remove all relevant
rough mass. The latter includes composite inputs and cannot be
replaced by the twin-correlation prime-power defect. Both moment
lower bounds are optimal on their finite nonnegative mass cones.
The complete divisor ranges, semiprime remainder and exact
multiplicity correction agree.

The elementary Selberg normalization is 8C. The finite remainder
sums to O(X/log^12 X); the growing-cofactor denominator comparison
and ordinary rough-count estimate justify the displayed o(X)
main-sum discrepancy. Review corrected two definition issues:
the clipped interval length is its nonnegative endpoint difference,
and the upper sums explicitly include every rough cofactor in the
enlarged interval, without a shifted-primality restriction.

The coefficient 128/25 bounds the proposed upper charge from below
and is not a lower bound on the actual balanced mass. Consequently
this estimate does not improve the total margin, which remains zero.
No additional formalization or milestone completion is justified
by this paper checkpoint; the earlier Lean verification is unchanged.

## 2026-09-05 — Exceptional-character and combined Chen budgets

Two independent reviews checked
[CHARACTER_BIAS_BUDGET.md](CHARACTER_BIAS_BUDGET.md) against the
published Matomäki-Merikoski fixed-shift corollary and the actual
Lean zero-gap/value statements. The convolution majorant retains
all composite leakage, including primes dividing the conductor
and higher prime powers. Its exact identity is not misreported
as a separate asymptotic supplied by the external theorem.

The selected scale X=q^10 keeps both prefix endpoints in the
published range. Their error budget is 3KX exp(-sqrt(log eta)).
Epp is deducted once for genuine primes and is absent, correctly,
from the W2-based transfer to T+R. Unbounded conductors of a
fixed sufficiently high quality suffice; a single fixed zero
does not. The source gives neither the necessary existence
hypothesis nor a numerical quality threshold. The repository's
zero-gap theorem is used only with its actual region premise.

The combined Chen/moment calculation has a separate support
audit: its central primes have opposite residue classes modulo
3, while genuine twins agree exactly on the original common
lower-integer interval after log-product weighting. A finite
endpoint correction is necessary only if the central-prime
intervals are aligned instead. The leading feasibility assignment
keeps every listed nonnegative mass and exact identity and has
zero twins. The proposed joint improvement retains both mass
deficits and its new leakage error.

The character route therefore supplies a conditional positive
budget, and the combined old inequalities supply no new margin.
Neither result is an unconditional signed gain. No new Lean
endpoint or completion of M4-M6 is claimed.

## 2026-09-05 — Review of fixed-pair extraction

The [new assessment](FIXED_PAIR_EXTRACTION_BUDGET.md) was checked
against Maynard Proposition 4.1, Polymath8b Theorem 3.14 and
Banks-Freiberg-Turnage-Buterbaugh Theorem 1. Its tuple graph is
a matching by the modulo-3 admissibility condition. The exact
empty-component identity explains both the extraction threshold
and the defect for signed weights.

The standard prime-count budget includes its common prefactor
and both actual residuals. The graph threshold exceeds its main
coefficient, even under the stronger hypothetical distribution
range. The two-dyadic transfer retains multiplicity and maximum
weight, without discarding endpoints or double-counting prime
powers. Qualitative tuple guarantees are separately distinguished
from a fixed-pair guarantee, including on actual primes restricted
to one residue class.

Independent review verified the exact dual norm identity for the
full two-coordinate marginal domain, including the fiber-mean
corrections and their zero-endpoint integrability. The explicit
step function attains quotient 2. Its full-marginal quotient
exceeds 2, but those tails are not evaluated by the source
theorem. The illustrative positive coefficient is labeled
unproved and retains its missing arithmetic and regularization
requirements.

The ceiling applies to that domain and its nested epsilon-simplex
family, not every support geometry or every sieve. It does not
bound actual prime mass from a truncated-marginal lower estimate.
No new formalization is justified by a complete-budget gain;
the unconditional margin remains zero.

## 2026-09-05 — Review of the Gowers fixed-shift budget

[GOWERS_FIXED_SHIFT_BUDGET.md](GOWERS_FIXED_SHIFT_BUDGET.md)
was independently reviewed for source scope, exact norm transfer
and the sparse comparison construction. The quantitative estimate
uses the source's corrected Siegel model; the distinct constants
in n and n+2 do not make their linear vectors independent.

The finite genuine-prime budget retains both mixed terms, the
residual pair term, the actual model deficit and Epp. The Fourier
phase, p^(3/2) loss, additive-quadruple padding factor and logarithmic
mask bound check. Fourier norms use counting measure and physical
L2 norms use normalized mean. The bounded chirp witness verifies
that the power loss is not merely an artifact of unbounded weights.

The Bernoulli-neighborhood comparison has exact cyclic exclusion
at shift two. Disjoint cube neighborhoods give centered independent
products; bad cubes have proportion at most B_s/N. Positivity of
the full Gowers moments justifies Markov and the finite union bound.
Mean normalization preserves all stated rates.

The interval extension has a separate valid-cube denominator and
collision count. Zero extension supplies nonnegativity and the
triangle inequality under the source's normalized convention.
Its centered correlation includes the exact four-weight boundary
term, rather than incorrectly importing cyclic translation invariance.

No comparison is claimed to reproduce all prime progression data
or additional majorant hypotheses. The proposed arithmetic saving
is unproved. Its conditional transfer to T+R cancels Epp correctly
and does not reuse the 0.263 class bound. No new Lean endpoint or
positive total margin is claimed.

## 2026-09-05 — Weighted quotient and microscopic endpoint review

The follow-up in [CUTOFF_SHIFT_ROUTE.md](CUTOFF_SHIFT_ROUTE.md#6-current-cutoff-weighted-distribution-and-its-full-residual)
distinguishes a support obstruction from an arithmetic mass bound.
Its broadened seven-prime family has harmonic coefficient mass
15 log^7(35/34)/7!, but this does not lower-bound the discarded
prime-shift contribution. The exact decomposition retains that
contribution, the sum of coefficient magnitudes in termwise
applications, and the outer tail beyond the distribution level.
The ordered budget takes a real part, retaining compatibility
with complex factorable weights.

The quotient sieve is applied only where D/a>=1. Its complete
signed identity keeps both upper and lower defects, and even
progression moduli remain separate. The 3/14 limiting parameter
does not supply a positive lower coefficient. Maynard's product
modulus conditions imply maximum exponent 11/21. Yang's new
convolution theorem is not replaced by its older arbitrary-weight
lemma; the smooth coefficient and extra prime selector remain
missing in the stronger statement.

[PRIME_FACTOR_ENDPOINT_BUDGET.md](PRIME_FACTOR_ENDPOINT_BUDGET.md)
retains the strict cofactor cutoff and exact dyadic floors. The
bound q>K>k ensures uniqueness of the largest prime factor.
Oddness gives the endpoint plateau for K<=3. Two microscopic
continuous predictions would disagree on the same actual set,
so the proposed uniform precision is impossible independently
of twin-prime infinitude.

The finite log-weight conversion and signed transfer were checked
with genuine H_K and D_K: Epp appears with its correct favorable
sign in the latter, without a second deduction from the former.
The contradiction is scoped to the proposed microscopic extension,
not the source's weak convergence. No positive total gain or new
Lean endpoint results.
