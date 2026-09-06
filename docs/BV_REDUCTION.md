# Finite foundations for the maximal BV obligation

The repository's `MaximalBombieriVinogradov` is now proved by the
[independent classical chain](CLASSICAL_DISTRIBUTION_THEOREM.md). This note
records its finite character reductions and the asymptotic assembly.
The newest twin-prime endpoint assumes only B*.

## Checked progression and primitive-character reductions

For a character χ modulo q, define

```text
P(t,χ) = Σ_{0<n≤t} Λ(n)χ(n),
E(t,χ) = P(t,χ) − [χ is principal] t,
Emax(T,χ) = max_{0≤t≤T} |E(t,χ)|.
```

`CharacterSums.lean` uses the pinned character orthogonality theorem to prove,
for q>0 and coprime a,q,

```text
φ(q) ψ(t;q,a) = Σχ χ(a^−1) P(t,χ).
```

`CharacterMaximal.lean` subtracts the principal contribution exactly and
retains both finite maxima:

```text
progressionMaxError(T,q) ≤ Σχ Emax(T,χ)/φ(q).
```

The principal sum is ψ(t) minus `noncoprimeMangoldtMass(t,q)`. Its excluded
prime terms divide q, so their total is at most `Σ_{d|q}Λ(d)=log q`.
The remaining terms are bounded by ψ(t)−θ(t). `CharacterExceptions.lean`
therefore proves, for t,q≥1,

```text
noncoprimeMangoldtMass(t,q) ≤ log q + 2√t log t.
```

On coprime indices χ and its inducing primitive character χ* agree. On
the other indices χ vanishes and |χ*|≤1. Their P sums consequently differ
in norm by at most this mass. A character is principal exactly when χ*
is principal, so centering preserves the same bound. Monotonicity of the
mass gives the replacement bound uniformly at every t≤T.

`CharacterPrimitiveReduction.lean` combines these facts. There are φ(q)
characters modulo q, so the averaged replacement costs one mass per modulus:

```text
Σ_{q≤Q} progressionMaxError(T,q)
 ≤ Σ_{q≤Q} (1/φ(q)) Σ_{χ mod q} Emax(T,χ*)
   + Q(log Q + 2√T log T).
```

Modulus one and endpoint zero are included. For q=1 the principal error
is ψ(t)−t, not zero. `CharacterConductor.lean` now regroups the original
characters exactly by conductor. With
`M(T,r)=Σ_{χ primitive mod r}Emax(T,χ)`, it proves

```text
Σ_{q≤Q} (1/φ(q)) Σ_{χ mod q} Emax(T,χ*)
 = Σ_{r≤Q} M(T,r) Σ_{0<k≤Q/r} 1/φ(rk).
```

The finite bijection uses induction of primitive characters, conductor
preservation, and injectivity. In particular, it retains the contribution
of conductor one at every original modulus.

`TotientReciprocal.lean` proves that a fixed constant `Cφ≥1` satisfies

```text
Σ_{0<n≤N} 1/φ(n) ≤ Cφ(1+log N),
Σ_{0<k≤Q/r} 1/φ(rk) ≤ Cφ(1+log Q)/φ(r)   (r>0).
```

Its correction function `h=(μ/n)*(1/φ)` has local values `h(1)=1`,
`h(p)=1/(p(p−1))`, and `h(p^k)=0` for k≥2. The local absolute Euler
excess is bounded by `2/p²`, proving absolute summability. The exact
identity `1/φ=h*(1/n)` then reduces the summatory estimate to harmonic
sums. Totient supermultiplicativity gives the bound for multiples.

`ConductorReduction.lean` combines the checked identities and bounds:

```text
Σ_{q≤Q} progressionMaxError(T,q)
 ≤ Cφ(1+log Q) Σ_{r≤Q} M(T,r)/φ(r)
   + Q(log Q+2√T log T).
```

`CharacterExceptionGrowth.lean` gives the explicit bound
`13 Q√X log X` for the final error at T=2X+2, when X≥2 and Q≤X.
For every A>0, it is eventually at most `X/log^A X` uniformly over
`Q≤X^(1/2)/log^(A+2)X`. The threshold is independent of Q and of any
separately selected endpoint at each modulus. The combined progression
reduction, including its new conductor form, uses exactly this scale and endpoint.

`ConductorAbel.lean` checks the summation step for large conductors. For
nonnegative a(r), if `Σ_{0<r≤R}a(r)≤A+BR+DR²` on `R₀≤R≤Q`, with
`1≤R₀≤Q` and nonnegative constants, then

```text
Σ_{R₀<r≤Q} a(r)/r ≤ A/R₀ + B(1+log(Q/R₀)) + 2DQ.
```

The exact boundary identity includes `−S(R₀)/R₀` and the kernel sum
over `R₀≤r<Q`, so it also covers `R₀=Q`. This theorem does not supply
the needed cumulative character mean value.

## Checked finite large-sieve transfer

`PrimitiveGauss.lean` proves `|τ(χ)|²=q` for primitive complex characters
at every positive modulus, including composite q and q=1. The proof
evaluates the pinned finite double Fourier transform at −1. It does not
apply a finite-field theorem to a composite residue ring.

`CharacterLargeSieveTransfer.lean` proves unit-group Parseval and the exact
Gauss factorization. Restricting the nonnegative Parseval sum to primitive
characters gives, for every finite natural index set s and complex a(n),

```text
(q/φ(q)) Σ_{χ primitive mod q} |Σ_{n∈s} a(n)χ^−1(n)|²
 ≤ Σ_{u∈(Z/qZ)×} |Σ_{n∈s} a(n)e(un/q)|².
```

This is the finite transfer used in the multiplicative large sieve.
The normalization and inverse convention
agree with [Tao's Notes 3, Exercise 11](https://terrytao.wordpress.com/2015/01/10/254a-notes-3-the-large-sieve-and-the-bombieri-vinogradov-theorem/).

`AdditiveKernel.lean` proves the elementary interval kernel bound

```text
|Σ_{M≤n<N} e(nθ)| ≤ min(N−M, 1/(2‖θ mod 1‖))
```

when θ is nonzero modulo one. The proof uses the exact geometric series,
the triangle inequality, and Jordan's sine inequality. Its diagonal bound
is N−M, including empty intervals.

`FiniteLargeSieve.lean` proves a finite Schur inequality, then synthesis
and correlation bounds by Cauchy–Schwarz duality. A bound B≥0 for every
absolute Gram row gives

```text
Σ_i |Σ_n a(n)E(i,n)|² ≤ B Σ_n |a(n)|².
```

`SeparatedReciprocal.lean` orders a positive δ-separated finite real set
to prove `Σ1/x≤H_card/δ`; splitting signs gives `Σ1/|x|≤2H_card/δ`.
`RationalFrequencySeparation.lean` proves distinct rational frequencies
a/q and b/r have circle distance at least 1/(qr), hence 1/Q² when
q,r≤Q. Reduced unit frequencies are unique across positive moduli,
including the frequency zero at modulus one.

`AdditiveLargeSieve.lean` now supplies the actual spacing-to-row estimate.
Centered representatives preserve separation, and the diagonal contributes
the interval length. For any finite set s of δ-separated frequencies, δ>0,

```text
Σ_{i∈s} |Σ_{M≤n<N} a(n)e(nθ_i)|²
 ≤ (N−M + H_|s|/δ) Σ_{M≤n<N} |a(n)|².
```

The row estimate and duality are both proved; there is no unproved row-bound
argument. The theorem also has a corollary replacing H_|s| by `1+log|s|`.
This is a large sieve with a logarithmic loss, not the sharper classical
constant `N−M+δ^−1`.

`RationalLargeSieve.lean` assembles the entire finite family of unit
residues over `1≤q≤Q`, proves its cardinality `Σ_{q≤Q}φ(q)`, and
applies the checked 1/Q² spacing. The phase bridge identifies its real
exponential with `ZMod.stdAddChar`, so summing the Gauss transfer yields

```text
Σ_{q≤Q} (q/φ(q)) Σ_{χ primitive mod q} |Σ_{M≤n<N} a(n)χ^−1(n)|²
 ≤ [N−M + Q² H_(Σ_{q≤Q}φ(q))] Σ_{M≤n<N} |a(n)|²
 ≤ [N−M + Q²(1+2log(Q+1))] Σ_{M≤n<N} |a(n)|².
```

Both bounds are unconditional finite theorems, also for Q=0 and empty
intervals. The inverse convention matches the positive additive phase.
`CharacterBilinear.lean` now proves the inversion reindexing and supplies
the direct-character convention. These particular theorems are for fixed
intervals; the maximal second-moment extensions are described next.

## Checked interval cancellation and maximal second moments

`CharacterInterval.lean` proves Pólya–Vinogradov for primitive characters
at every q>1, including composite moduli:

```text
|Σ_{M≤n<N} χ(n)| ≤ √q H_q ≤ √q(1+log q).
```

The proof uses spacing 1/q at one fixed modulus, the proved geometric
kernel, and primitive Gauss factorization. Modulus one is excluded from
this cancellation theorem and remains in the separate small-conductor work.
`CharacterLogInterval.lean` proves complex finite Abel summation and obtains
`|Σ_{0<n≤T}log(n)χ(n)|≤2√q(1+log q)log T`. This includes T=0 and
uniformly controls shorter prefixes. The associated finite Type I outer
sum with inner endpoint T/m is bounded by this constant times `Σ|a(m)|`.
These are interval bounds, not the full averaged Vaughan Type I estimate.

For fixed rectangles, `CharacterBilinear.lean` factors the character sum
exactly and uses weighted Cauchy–Schwarz with the large sieve. Its bound is
the product of the square roots of the two interval energy budgets.

`DyadicMaximal.lean` bounds each prefix by the full binary tree energy.
`DyadicIntervalCover.lean` covers any subinterval of a length-2^k interval
by at most 2(k+1) dyadic blocks, proves exact coverage, and proves that
disjoint target intervals cannot reuse a nonempty block. This supplies an
actual disjoint-interval square bound without an interval-count factor.

Writing `C_Q=Q²(1+2log(Q+1))` and `E=Σ_{M≤n<M+2^k}|a(n)|²`,
`CharacterMaximalLargeSieve.lean` proves

```text
Σ_{q≤Q} (q/φ(q)) Σ_{χ primitive}
  max_{M≤t≤M+2^k} |Σ_{M≤n<t}a(n)χ(n)|²
 ≤ (k+1)²(2^k+C_Q)E.
```

It also proves the bound `2(k+1)²(2^k+C_Q)E` for sums of squared
interval sums over any disjoint finite interval family selected separately
for each character. The finite maximum remains inside the character sum.
Both results are derived from the fixed-interval large sieve in Lean.

`DyadicStaircase.lean` proves the exact rectangular decomposition for any
nonincreasing natural boundary, and specializes it to
`F_t(m)=min(N+K,max(N,T/m+1))`. For M>0, its filtered double sum retains
`mn≤t` exactly, including all endpoint equalities. `DyadicStaircaseGeometry`
and `DyadicStaircaseLevels` now prove the level grouping and disjointness
needed for the [maximal Type II route](BV_MAXIMAL_ROUTE.md).
`IntervalFamilyLargeSieve` sums the fixed left-child energies without a
depth loss, while the adaptive estimate handles the correction intervals.
`DyadicStaircaseFirstMoment` combines these bounds with weighted
Cauchy–Schwarz. `CharacterMaximalBilinear` proves the resulting statement
for the actual primitive-character family:

```text
Σ_{q≤Q} (q/φ(q)) Σ_{χ primitive} max_{0≤t≤T}
  |Σ_{M≤m<M+2^k, N≤n<N+2^j, mn≤t} a(m)b(n)χ(mn)|
 ≤ 2(k+1)(j+1) sqrt((2^k+C_Q)E_a) sqrt((2^j+C_Q)E_b).
```

Only M>0 is required; the other natural parameters may be zero. Inverse
characters satisfy the same bound. Each character chooses an actual finite
maximizer, so the maximum is retained inside its sum. No distribution
hypothesis remains in this theorem. `BilinearBoxPolynomial` also proves
the finite polynomial bound used after coefficient energy estimates.

The exact Vaughan Type II assembly now checks as well. `CharacterVaughan`
retains the low von Mangoldt term in the full character identity and proves
the Type II pair sum. `VaughanBoxCoefficients` retains both strict lower
cutoffs and the common upper cutoff. `DyadicNatPartition` and
`DyadicBilinearPartition` give an exact partition into global power-of-two
cells. `VaughanActiveBoxes` proves all discarded sums and maxima vanish.
`CharacterVaughanDyadic` then bounds the Type II maximum by active box maxima.
Writing `D=ceil(log₂(T+1))`, `L_Q=1+2log(Q+1)`, and `S_II(t,χ)` for the
full Type II sum, `CharacterVaughanMean` proves

```text
Σ_{q≤Q} (q/φ(q)) Σ_{χ primitive} max_{0≤t≤T}|S_II(t,χ)|
 ≤ 2D⁴ log(T)L_Q [T + QT(1/√(U/2)+1/√(V/2)) + Q²√T].
```

Its only side conditions are U,V>0. The half-cutoffs arise from global
cells that meet the masked support; no cutoff is rounded to a power of two.
The inverse-character statement is also proved. This is a finite Type II
theorem, not the complete mean value for the von Mangoldt character sum.

## The full proved mean and conductor tail

[Vaughan's author notes, pp. 3–6](https://personal.science.psu.edu/rcv4/Bombieri.pdf)
state the required residue and endpoint maxima. A sufficient primitive
mean-value bound is

```text
Σ_{r≤R} (r/φ(r)) Σ_{χ primitive mod r} max_{t≤T}|P(t,χ)|
 ≪ (T + T^(5/6)R + √T R²) log^5(TR).
```

The implementation uses eighth-root internal cutoffs and proves a different
sufficient variant. `CharacterVaughanTypeI` gives both exact Type I factor
sums. `CharacterTypeIBounds` applies the proved primitive interval bounds;
`PrimitiveCharacterCounting` supplies the exact count at every positive
modulus. `CharacterTypeIMean` combines these estimates and treats modulus
one separately with `T log T`. The floor and logarithm comparisons in
`BVInternalCutoffs`, `BVLogComparisons`, and `VaughanMeanParameters` then
give the actual theorem `primitive_character_mean_value`:

```text
Σ_{r≤R} (r/φ(r)) Σ_{χ primitive mod r} max_{0≤t≤T}|P(t,χ)|
 ≤ C₀ [T + T^(15/16)R + √T R²] log⁶T,

C₀=5+16(2/log 2)^4,  T≥256,  1≤R≤√T.
```

The inverse-character version is also proved. There is no mean-value,
distribution, or cancellation hypothesis in this theorem beyond its
stated numerical range. The [Type I route](BV_TYPEI_ROUTE.md) records the
complete derivation. The weaker middle exponent still leaves a fixed
positive power saving, which is sufficient for BV.

`ConductorMean` proves the exact centered/uncentered conversion for
primitive conductors greater than one. `VaughanMeanValue` applies the
actual mean to every cumulative endpoint in the proved Abel inequality.
For `1≤R₀≤Q≤√T` and `T≥256`, it obtains

```text
Σ_{R₀<r≤Q} primitiveCharacterMass(T,r)/φ(r)
 ≤ C₀ log⁶T [T/R₀ + T^(15/16)(1+log(Q/R₀)) + 2√T Q].
```

The coefficients in the cumulative quadratic bound are fixed in T; they
do not vary with its endpoint. The finite progression reduction multiplies
this tail and the remaining small-conductor mass by `Cφ(1+log Q)`, then
adds the already explicit primitive-replacement error.
`sum_progressionMaxError_le_small_conductors_and_tail_if` includes Q=0
and Q<R₀: the tail is then zero and the small sum ends at `min(R₀,Q)`.

`SmallConductorMean` proves that a uniform centered bound
`characterMaxError T χ≤E` for primitive conductors r≤R₀ gives small mass
at most R₀E. The theorem `sum_progressionMaxError_le_small_conductor_budget`
uses precisely that explicit input. This finite implication does not
prove the uniform bound itself.

## Completed asymptotic assembly and its small-conductor input

`BVConductorGrowth` now absorbs the actual centered tail at T=2X+2.
For every A>0, eventually and uniformly over R₀,Q satisfying
`1≤R₀≤Q`, `log^(A+9)X≤R₀`, and
`Q≤sqrt(X)/log^(A+9)X`, the outer-weighted tail is at most
`Ktail X/log^A X`, with `Ktail=768CφC₀+1`.
The finite precursor uses the explicit margin
`log^(A+8)X≤X^(1/16)`; the existing logarithm-versus-power theorem proves
that margin eventually. No distribution estimate is an input.

`BVSmallConductorGrowth` chooses `R₀=ceil(log^(A+9)X)` and proves
`R₀≤log^(A+10)(2X+2)` eventually. A supplied uniform centered estimate
with error exponent `2A+12` and conductor exponent `A+10` contributes at
most `12CφC X/log^A X` after counting and the outer logarithm. The
admissible Q range also lies in the square-root range of the finite mean
and in the already proved replacement-error range with exponent A+2.

`SiegelWalfiszMaximal` proves that an independent centered pointwise SW
statement gives its full endpoint maximum. Short endpoints use
`|ψ(t,χ)−1_(χ principal)t|≤t log t+t`. For long endpoints the proof
retains uniform thresholds, compares log t with log T, and increases the
conductor exponent from B to B+1. Conductor one and endpoints zero and one
are retained.

`BombieriVinogradovFromSW` now proves both implications

```text
MaximalSiegelWalfisz → MaximalBombieriVinogradov,
PointwiseSiegelWalfisz → MaximalBombieriVinogradov.
```

It uses B=A+9 and K=`12CφC+Ktail+1`, and constructs a single natural
threshold before quantifying Q. The exact endpoint T=2X+2, every residue
and endpoint maximum, Q=0, and Q<R₀ are preserved. The resulting theorem
has SW as its explicit hypothesis; it does not establish SW.

The [independent proof](CLASSICAL_DISTRIBUTION_THEOREM.md) now supplies
that uniform centered pointwise small-conductor theorem. Qualitative
nonvanishing or infinitude in progressions does not give its rate;
see [Akbary–Hambrook, Theorem 1.2 and introductory discussion](https://arxiv.org/pdf/1309.2730).
The new proof includes independent quantitative control of the conductor-one
prime error through its principal contour, without a BV-derived estimate.
The [local analytic inventory](SIEGEL_WALFISZ_ROUTE.md) records the available
APIs, the newly proved finite Dirichlet tails and ordered convergence, and
the completed uniform quantitative analysis.

Moving a maximum outside a character sum without proof, omitting conductor
one, or assuming any pending estimate as a new theorem argument would not
discharge BV. These classical steps also do not establish the signed B*
estimate required by the twin-prime endpoint.
