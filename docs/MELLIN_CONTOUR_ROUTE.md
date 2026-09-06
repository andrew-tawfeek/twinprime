# Checked Mellin route to centered Siegel–Walfisz

Checkpoint: 2026-09-05. The exact `PointwiseSiegelWalfisz` proposition is
now proved. The full twin-prime conjecture remains unproved because B*
is unresolved. This note records the actual analytic estimates used in
the [completed classical chain](CLASSICAL_DISTRIBUTION_THEOREM.md).

## Actual inversion, including conductor one

[MellinRampKernel.lean](../TwinPrime/Analytic/MellinRampKernel.lean) defines
`w(u)=max(1−u,0)` with complex values and `K(s)=1/(s(s+1))`.
It proves the Mellin transform for Re(s)>0, vertical integrability for
every c>0, and actual inversion at every u>0. The norm majorant is
`(1+c^(−2))/(1+t²)`. The transform computation uses the two convergent
power integrals on (0,1]; inversion uses the pinned Mathlib theorem.

[MangoldtMellinInversion.lean](../TwinPrime/Analytic/MangoldtMellinInversion.lean)
first proves inversion for an absolutely convergent Dirichlet series.
Each term has norm
`u^(−c) |a(n)n^(−c)| |K(c+it)|`, giving summable norm integrals and an
actual justified exchange of series and integral. The zero coefficient
is omitted exactly as in `LSeries.term`. The finite ramp sum includes
`1≤n≤floor(x)`, and its endpoint weight is zero when n=x.

The actual Mangoldt specialization, for every positive modulus, every
character, c>1, and x>0, is

```text
Sχ(x) = Σ_{1≤n≤floor(x)} χ(n)Λ(n)(1−n/x)
      = (1/(2π)) ∫_{t∈ℝ} x^(c+it) [−Lχ′/Lχ(c+it)] K(c+it) dt.
```

The series majorant is the proved summable Mangoldt mass. The identity
uses the actual analytically continued L-function and retains principal,
imprimitive, and modulus-one characters. There is no convergence or
inversion premise in `weighted_mangoldt_sum_eq_mellinInv`.

## Rectangles and the full complex norm

The former radius-one expansion could not evaluate left of one.
[WideAnalyticLogDerivativeBound.lean](../TwinPrime/Analytic/WideAnalyticLogDerivativeBound.lean)
uses Cauchy radius 1/16 inside the existing radius-9/8 normalized-log
bound. The derivative constant is 288 on radius 17/16.
[WideLocalLogDerivativeExpansion.lean](../TwinPrime/Analytic/WideLocalLogDerivativeExpansion.lean),
[WideLFunctionLocalExpansion.lean](../TwinPrime/Analytic/WideLFunctionLocalExpansion.lean),
and [WideZetaLocalExpansion.lean](../TwinPrime/Analytic/WideZetaLocalExpansion.lean)
keep the actual divisor disk of radius 5/4 and outer disk of radius 3/2.
All older radius-one APIs and constants remain available.

[ZeroFreeRectangle.lean](../TwinPrime/Analytic/ZeroFreeRectangle.lean)
uses the proved Siegel gap to choose one d>0, before the conductor,
character, or height. Put

```text
W(ε,d,q,T) = min(1/16, min(primitiveLogZeroFreeWidth(q,T), d q^(−ε)))/2.
```

Every primitive q>1 has no zero for Re(s)≥1−W and |Im(s)|≤T.
[ZeroSumNorm.lean](../TwinPrime/Analytic/ZeroSumNorm.lean) shows that a
zero-free rectangle with width 2δ and height H+2 separates every actual
local zero from evaluation points with Re(s)≥1−δ, |Im(s)|≤H by at least δ.
The norm of the zero sum is at most the analytic multiplicity sum divided
by δ. Nonnegative divisor multiplicities and finite support are explicit.

[LogDerivativeStrip.lean](../TwinPrime/Analytic/LogDerivativeStrip.lean)
combines this with Jensen. For 1−δ≤Re(s)≤2 and |Im(s)|≤H, it bounds
`|Lχ′/Lχ(s)|` by

```text
M(q,H,δ) = Cwide (1+N) + N/[log(6/5) δ],
Cwide = 288(1+log5/log(6/5)),
N = log16 + 2logq + log(H+4).
```

The uniform actual theorem takes `δ=W(ε,d,q,H+2)/2` and has no supplied
zero-free hypothesis. A separate theorem bounds the regularized zeta
logarithmic derivative, including its value at one, using its proved
exception-free region. Its numerator is `log16+2log(H+4)`.

## Finite contours and actual smoothed sums

[MellinRectangle.lean](../TwinPrime/Analytic/MellinRectangle.lean)
applies Cauchy–Goursat to `G(s)=x^s F(s)K(s)` on a closed rectangle.
With both vertical parameters directed upward, the exact relation is
`right−left = i(bottom−top)`. For a>0, a≤c, H>0, x≥1 and |F|≤M,
the horizontal difference is at most
`2(c−a)x^c M/H²`. The left vertical integral is at most
`π(1+a^(−2))x^a M`, independently of H. These follow from the actual
finite integrals and the ramp kernel bounds.

[MellinTruncation.lean](../TwinPrime/Analytic/MellinTruncation.lean)
proves that both tails of an integrable function bounded by C/t² cost
at most `2C/H`. The actual right-line Mangoldt integrand has
`C=x^c m(c)`, where `m(c)=ΣΛ(n)n^(−c)`; for 1<c≤9/8,
`m(c)≤1/(c−1)+40`.

[SmoothedMangoldtContour.lean](../TwinPrime/Analytic/SmoothedMangoldtContour.lean)
combines these theorems. Its actual primitive-character result chooses
one d>0 for each ε>0, sets `δ=W(ε,d,q,H+2)/2`, `a=1−δ`, and uses
`M=M(q,H,δ)`. Uniformly for primitive q>1, x≥1, 1<c≤2, H>0,

```text
|Sχ(x)| ≤ x^c m(c)/(πH)
        + [π(1+a^(−2))x^a M + 2(c−a)x^c M/H²]/(2π).
```

Holomorphy and the norm hypothesis are discharged from the actual
L-function and its proved rectangle. The final theorem retains no
value-bound, zero-free, contour-shift, or distribution premise.

## Uniform widths, budgets, and unsmoothing

[SiegelWalfiszStripWidth.lean](../TwinPrime/Analytic/SiegelWalfiszStripWidth.lean)
chooses ε=1/(2B). For B,K,d>0, L≥1, q≥1 and q≤L^B, it proves
`W(ε,d,q,L^K+2)/2 ≥ k L^(−1/2)` with

```text
D=4000 C_loc (1+log7+2(B+K)),
k=min(1/16,min(D^(−1),d))/4 > 0.
```

[SiegelWalfiszStripBudget.lean](../TwinPrime/Analytic/SiegelWalfiszStripBudget.lean)
proves the corresponding `M(q,L^K,δ)≤C L`. Both results are pointwise
for L≥1 and have eventual formulations with L=log x, uniformly in q.
The constants retain the height margin, cap, and both width halvings.

[SmoothedPartialSum.lean](../TwinPrime/Analytic/SmoothedPartialSum.lean)
defines `A(x)=Σ_{1≤n≤floor(x)}a(n)(x−n)=xS(x)` and proves the exact
forward difference. Its deviation from the sharp sum through floor(x)
is bounded by the coefficient mass on `(x,x+h]`. For a Mangoldt character
twist, x≥0, h>0, and x+h≥1, this is at most `(h+1)log(x+h)`.
The finite interval partition, floor bounds, and every weight in [0,1]
are proved. No distribution theorem is assumed.

## Principal contribution and completed assembly

[MellinPoleKernel.lean](../TwinPrime/Analytic/MellinPoleKernel.lean)
proves the transform and actual inverse of `1/((s−1)s(s+1))` on c>1.
At 1/x, x≥1, its value is `(x−1)^2/(2x)`, differing from x/2 by at
most one. The computation is the exact ramp difference
`(u^(−1)w(u)−w(u))/2`; it does not assume a residue theorem.

[PrincipalMellinInversion.lean](../TwinPrime/Analytic/PrincipalMellinInversion.lean)
now proves the actual subtraction identity for the regularized integrand
using `−ζ′/ζ=1/(s−1)−Z′/Z`. Both summands are integrable. Subtracting
their inverse integrals gives the exact regularized contour for
`SΛ(x)−(x−1)^2/(2x)`. Its right-line tail has budget
`x^c(mangoldtDirichletMass(c)+1/(c−1))/(πH)`.

[SmoothedPrincipalContour.lean](../TwinPrime/Analytic/SmoothedPrincipalContour.lean)
combines that tail with the regularized-zeta rectangle, retaining the
bounded pole correction. [PrincipalStripParameters.lean](../TwinPrime/Analytic/PrincipalStripParameters.lean)
shows the common primitive evaluation width at conductor one fits inside
the zeta zero-free region, and its zeta norm budget is at most twice
the conductor-one primitive budget.

[ContourParameterBounds.lean](../TwinPrime/Analytic/ContourParameterBounds.lean)
proves `x^(1+1/log x)=e x`, the square-root exponential bound on the
left line, and `mangoldtDirichletMass(1+1/log x)≤log x+40` when log x≥8.
[ContourBudgetAbsorption.lean](../TwinPrime/Analytic/ContourBudgetAbsorption.lean)
then bounds the principal budget, with L=log x, by

```text
42 e x L^(1−K) + 3C x L exp(−k sqrt L) + C e x L^(1−2K).
```

For K=A+2, A>0, these are at most a constant times x/L^A, uniformly
in the admissible width and norm budget. The primitive budget is smaller.
The final pole correction of at most one is absorbed by L^A≤x.
[SmoothedSiegelWalfisz.lean](../TwinPrime/Analytic/SmoothedSiegelWalfisz.lean)
thus proves the centered smoothed estimate for all primitive conductors
q≤L^B, including one, with a common constant and threshold.

[CenteredUnsmoothing.lean](../TwinPrime/Analytic/CenteredUnsmoothing.lean)
centers the exact finite difference. Writing Eχ(x)=Sχ(x)−[χ=1]x/2,
the sharp centered sum has norm at most

```text
((x+h)|Eχ(x+h)| + x|Eχ(x)|)/h + (h+1)log(x+h) + h/2.
```

With h=x/L^(A+2) and smoothed exponent 2A+4, the total is at most
`(5C+5)x/L^A`. The proof retains the real floor endpoints and both
short-interval and principal corrections. [SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean)
proves that one threshold and conductor range work at both x and x+h,
then restricts to natural endpoints to give `PointwiseSiegelWalfisz`.

The existing maximalization, SW-to-BV, and BV-to-Mertens proofs apply in
[ClassicalDistribution.lean](../TwinPrime/Analytic/ClassicalDistribution.lean).
These analytic steps do not address the independent fixed-shift estimate B*.

## Verification

The first contour checkpoint added 102 public theorems in 16 modules.
The completed assembly adds 43 public theorems in ten more modules,
all compiling without new warnings. The full root build passed 8883 jobs.
The integrated audit passed 1041 selected declarations with only
`Classical.choice`, `propext`, and `Quot.sound`, and no Lean errors.
The source scan covers 228 project Lean files including the root import
file, with no holes, project axiom declarations, or trust bypasses.
The printed actual inversion and uniform primitive contour types retain
only the documented numerical and character conditions. The printed
SW, BV, and Mertens theorem types have no distribution arguments. The
new twin-prime endpoint retains B* as its only hypothesis. Source review covered the definitions and assembly; no separate independent mathematical review
of the new assembled SW theorem is claimed.
