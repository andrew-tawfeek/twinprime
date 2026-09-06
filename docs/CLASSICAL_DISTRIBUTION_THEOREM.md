# Completed classical distribution chain

Checkpoint: 2026-09-05. The repository now proves its exact centered
`PointwiseSiegelWalfisz` proposition, and hence its maximal
Bombieri–Vinogradov and quantitative Mertens statements. This completes
M3 of [PLAN.md](../PLAN.md). The signed fixed-shift estimate B* remains
unproved, so the twin-prime conjecture and M6 remain incomplete.

## Exact theorem and uniformity

[SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean)
proves `pointwise_siegel_walfisz : PointwiseSiegelWalfisz`:

```text
For every real A,B>0, there are C>0 and a natural T₀≥2 such that,
for every natural T≥T₀, every q≥1 with q≤(log T)^B, and every
primitive character χ modulo q,

  |Σ_{0<n≤T} Λ(n)χ(n) − [χ=1]T| ≤ CT/(log T)^A.
```

The constant and threshold are chosen before q and χ. Conductor one is
included. They need not be effective: the underlying proved Siegel
constant uses classical witness selection and finite minima. The theorem
does not assume a distribution estimate, value lower bound, zero-free
region, contour identity, or prime-sum main term.

## Source-to-lemma map

The earlier [small-conductor source audit](SIEGEL_WALFISZ_ROUTE.md),
[exceptional-zero proof](SIEGEL_EXCEPTION_ROUTE.md), and
[Mellin contour proof](MELLIN_CONTOUR_ROUTE.md) document the analytic
ingredients, their pinned Mathlib sources, and the proved repository
extensions. The final assembly is:

| Step | Checked source |
|---|---|
| Uniform Siegel value lower bound and arbitrary-power exceptional-zero gap | [SiegelValue.lean](../TwinPrime/Analytic/SiegelValue.lean), [SiegelZeroGapUnconditional.lean](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean) |
| Actual primitive nonvanishing rectangles and complex logarithmic-derivative bounds | [ZeroFreeRectangle.lean](../TwinPrime/Analytic/ZeroFreeRectangle.lean), [LogDerivativeStrip.lean](../TwinPrime/Analytic/LogDerivativeStrip.lean) |
| Actual smoothed inversion, finite contour shift, and both tails | [MangoldtMellinInversion.lean](../TwinPrime/Analytic/MangoldtMellinInversion.lean), [MellinRectangle.lean](../TwinPrime/Analytic/MellinRectangle.lean), [SmoothedMangoldtContour.lean](../TwinPrime/Analytic/SmoothedMangoldtContour.lean) |
| Regularized principal inversion and contour estimate | [PrincipalMellinInversion.lean](../TwinPrime/Analytic/PrincipalMellinInversion.lean), [SmoothedPrincipalContour.lean](../TwinPrime/Analytic/SmoothedPrincipalContour.lean) |
| Common positive width and logarithmic norm budget, including principal conductor one | [SiegelWalfiszStripWidth.lean](../TwinPrime/Analytic/SiegelWalfiszStripWidth.lean), [SiegelWalfiszStripBudget.lean](../TwinPrime/Analytic/SiegelWalfiszStripBudget.lean), [PrincipalStripParameters.lean](../TwinPrime/Analytic/PrincipalStripParameters.lean) |
| Right-line identities and uniform absorption of all contour errors | [ContourParameterBounds.lean](../TwinPrime/Analytic/ContourParameterBounds.lean), [ContourBudgetAbsorption.lean](../TwinPrime/Analytic/ContourBudgetAbsorption.lean) |
| Independent centered smoothed estimate | [SmoothedSiegelWalfisz.lean](../TwinPrime/Analytic/SmoothedSiegelWalfisz.lean) |
| Exact centered finite differences and their numerical error budget | [CenteredUnsmoothing.lean](../TwinPrime/Analytic/CenteredUnsmoothing.lean) |
| Uniform real and natural sharp endpoints | [SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean) |
| Maximal SW, exact BV, and quantitative Mertens without distribution arguments | [ClassicalDistribution.lean](../TwinPrime/Analytic/ClassicalDistribution.lean) |
| Twin-prime implication retaining only B* | [ConditionalSignedBilinear.lean](../TwinPrime/ConditionalSignedBilinear.lean) |

## Principal term and contour absorption

Write `Sχ(x)=Σ_{1≤n≤floor(x)}χ(n)Λ(n)(1−n/x)`. The actual identity
`−ζ′/ζ=1/(s−1)−Z′/Z`, with the entire regularization Z, splits its inverse
into the regularized contour and the pole weight `(x−1)²/(2x)`. For x≥1
this weight differs from x/2 by at most one. This proves the independent
principal main term without using a BV-dependent prime estimate.

Let L=log x, c=1+1/L, H=L^K, and a=1−δ. The common evaluation width
satisfies `δ≥kL^(−1/2)` and `0<δ≤1/16`, while the norm budget satisfies
`0≤M≤CL`. The principal budget dominates the primitive budget. For L≥8
it is bounded by

```text
42 e x L^(1−K) + 3C x L exp(−k sqrt L) + C e x L^(1−2K).
```

Here `x^c=e x` exactly and the right-line Mangoldt mass is at most L+40.
For any A>0, take K=A+2. Exponential decay absorbs the middle term and
the other exponents are at most −A. One threshold works for every
admissible δ and M. A further eventual inequality L^A≤x absorbs the
bounded pole correction. Thus for every A,B>0,

```text
|Sχ(x) − [χ=1]x/2| ≤ C x/(log x)^A
```

uniformly for primitive q≤(log x)^B. The principal bound uses the same
positive d as the nonprincipal family; its width is proved to fit within
the zeta zero-free region.

## Removing the smoothing weight

Let `Eχ(x)=Sχ(x)−[χ=1]x/2`. The exact finite-difference argument gives

```text
|Σ_{1≤n≤floor(x)}Λ(n)χ(n) − [χ=1]x|
 ≤ ((x+h)|Eχ(x+h)| + x|Eχ(x)|)/h
   + (h+1)log(x+h) + h/2.
```

The short interval `(x,x+h]` has at most h+1 indices. Every coefficient
has norm at most log(x+h). The last term is the principal quadratic
main term's finite-difference correction. Both floor conventions and
the orientation of the difference are retained in the proof.

For a target exponent A>0, apply smoothed SW with exponent 2A+4 and
choose `h=x/L^(A+2)`. Eventually L≥1 and L^(A+2)≤x, so
`1≤h≤x`, `x+h≤2x`, and `log(x+h)≤2L`. The three displayed errors are
at most `5C x/L^A`, `4x/L^A`, and `x/L^A`, respectively.
The resulting constant is 5C+5.

The threshold for the second smoothed estimate is automatic from x+h≥x.
Its conductor condition follows from the monotonicity of the logarithm
and B>0. No enlargement of B is needed for this forward difference.
Restriction to natural x=T identifies `Icc 1 T` with `Ioc 0 T` and gives
the exact repository proposition, with a natural threshold at least two.

## Consequences and the remaining obstruction

`ClassicalDistribution.lean` supplies the proved pointwise theorem to
the existing maximalization and SW-to-BV assembly. The BV-to-Mertens
reduction then proves `MertensLogSix`. The existing weighted progression,
totient, shared-prime, and Euler-product arguments supply (A) and (K),
including the existing constant `2*twinPrimeConstant`.

The new endpoint has exactly this remaining argument:

```text
∀ Y : ℕ, ∃ X ≥ Y,
  −((2*twinPrimeConstant)*X)/2
    ≤ bilinearTerm (primaryCutoff X) (primaryCutoff X) X.
```

It is a conditional implication to `TwinPrimeConjecture`. Neither SW nor
BV controls this fixed-shift signed bound. Its presence as a theorem
argument is not detected as an additional axiom and must not be omitted
from the proof-status report.

## Verification

The ten final-assembly modules add 43 public theorems. All compile with
the pinned Lean 4.32.0 and Mathlib revision. The full root build passes
8883 jobs. The source scan covers 228 project Lean files, including the
root import file, without proof holes, project axioms, or trust bypasses.
The integrated audit checks 1041 selected declarations, including all 43
new public theorems, with only Classical.choice, propext, and Quot.sound
and no errors. Endpoint types are recorded in the
[obligation ledger](PROOF_OBLIGATIONS.md). This checkpoint has implementation-source review and Lean verification; it does not claim a separate independent
mathematical review of the new assembled theorem.
