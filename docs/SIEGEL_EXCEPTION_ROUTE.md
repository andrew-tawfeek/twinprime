# Quantitative control of the possible real zero

This records the checked proof of Siegel's uniform value lower bound and its use in controlling the possible real zero. Mathlib is pinned to `81a5d257c8e410db227a6665ed08f64fea08e997` in [lake-manifest.json](../lake-manifest.json). The source links refer to that checkout. The proof uses actual L-functions, quantitative ordered-series tails, and a complete auxiliary-character dichotomy; it assumes no uniform value bound or existence of an auxiliary zero.

## Current proved scope

[ZeroFreeLogarithms.lean](../TwinPrime/Analytic/ZeroFreeLogarithms.lean#L124) proves that any zero in the stated logarithmic region for a primitive character of conductor `q>1` is real, simple, and belongs to a character satisfying `χ²=1`; it also proves uniqueness **for that character**. This is not a Landau–Page theorem asserting at most one exception across a growing family of conductors. The independent zeta region has no exception.

The unconditional theorem [siegel_value_lower_bound](../TwinPrime/Analytic/SiegelValue.lean#L23) now proves:

```text
For every ε>0 there is cε>0, independent of q and χ, such that
  ‖Lχ(1)‖ ≥ cε q^(−ε)
for every primitive quadratic χ of conductor q>1.
```

[SiegelZeroGapUnconditional.lean](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean#L16) now proves, for every `ε>0`, a uniform `dε>0` such that every actual zero in the proved logarithmic region has `χ²=1`, `t=0`, and `1−β ≥ dε q^(−ε)`. It supplies the proved value theorem to the conversion in [SiegelZeroGap.lean](../TwinPrime/Analytic/SiegelZeroGap.lean#L74); neither unconditional endpoint retains a value hypothesis. The value constant `cε` is uniform over both conductor and character, but ineffective: its construction may choose one existing near-one zero and uses finite minima from qualitative nonvanishing. It makes no claim to an algorithm or explicit numerical lower bound for `cε`. Mathlib's [LFunction_apply_one_ne_zero](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Nonvanishing.lean#L405) supplies the qualitative nonvanishing used for the fixed auxiliary value and finite conductor range; the new comparison and dichotomy supply the full uniform estimate.

Why this scale matters: for `q≤(log x)^B`, `B>0`, choosing `ε=1/(2B)` in the zero-gap theorem gives the scale `x exp(−c√(log x))`. The [Mellin contour route](MELLIN_CONTOUR_ROUTE.md) now proves actual smoothed inversion, uniform strip widths and norm budgets, finite contour estimates, the principal main term, and uniform error absorption. Centered finite differences complete [independent Siegel–Walfisz](CLASSICAL_DISTRIBUTION_THEOREM.md). The bilinear input `(B*)` remains unproved.

## Checked zero-to-value and finite-conductor bounds

The following is now proved in [LFunctionZeroValue.lean](../TwinPrime/Analytic/LFunctionZeroValue.lean#L65):

```lean
theorem norm_LFunction_one_le_gap_budget
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (4 + 14 * Real.sqrt q * (1 + Real.log q)) * (1 - β)
```

For every real `u∈[β,1]`, take Cauchy radius `1/4`. The disk lies in `Re(s)≥1/2`, `‖s‖≤5/4`. The proved [growth and derivative estimates](../TwinPrime/Analytic/LFunctionGrowth.lean#L19) give

```text
‖Lχ′(u)‖ ≤ 4 G(q,1/2,5/4)
          = 4 + 14√q(1+log q).
```

The proved `norm_sub_le_real_segment_deriv_bound` and `norm_LFunction_one_le_gap_of_deriv_bound` apply the [real-segment mean-value estimate](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Calculus/MeanValue.lean#L728), using `DirichletCharacter.differentiable_LFunction`. They work directly with complex norms and need no real-valuedness assumption. If a real-valued statement is useful, [LFunction_conj_of_sq_eq_one and its derivative counterpart](../TwinPrime/Analytic/LFunctionConjugateZeros.lean#L78) provide it.

**This existing derivative budget is too weak for the desired arbitrary power.** Combining it with `‖Lχ(1)‖≥cε q^(−ε)` only gives a gap of order `q^(−1/2−ε)/(1+log q)`. The fixed exponent `1/2` cannot be absorbed into arbitrary `ε`.

The sharper estimate is now proved as [norm_deriv_LFunction_near_one_le](../TwinPrime/Analytic/LFunctionNearOneGrowth.lean#L147), using the actual [truncation theorem](../TwinPrime/Analytic/CharacterDirichletContinuation.lean#L161) with `M=q`:

```text
q≥256,  1−1/log q ≤ u ≤ 1
    ⇒ ‖Lχ′(u)‖ ≤ 10 exp(2) (log q)².
```

Write `l=log q≥4`, and take the circle of radius `1/l` about real `u`. Its points satisfy `σ≥1−2/l≥1/2` and `‖s‖≤5/4`. For `1≤n≤q`, `n^(−σ)≤exp(2)/n`; hence the partial sum is bounded by `exp(2)(1+l)`. The truncation error is at most

```text
√q(1+l) q^(−σ)(1+‖s‖/σ)
 ≤ 4 exp(2) q^(−1/2)(1+l)
 ≤ 4 exp(2)(1+l).
```

Thus the circle bound is `5 exp(2)(1+l)≤10 exp(2)l`. [Cauchy's derivative estimate](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/Liouville.lean#L76) supplies the extra factor `l`. The numerical inputs are [eight_log_two_le_log_nat / half_le_log_two](../TwinPrime/Analytic/BVLogComparisons.lean#L16), the real-power exponential identity, and [harmonic_eq_sum_Icc / harmonic_le_one_add_log](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/Harmonic/Bounds.lean#L20). The Lean proof bounds the tail directly by the last displayed expression; no zero or value lower bound is assumed.

[LFunctionLogarithmicZeroValue.lean](../TwinPrime/Analytic/LFunctionLogarithmicZeroValue.lean#L30) proves the matching `10 exp(2)l²(1−β)` value bound and its division form. Its region-width comparison ensures the entire real segment lies above `1−1/log q`. `LFunction_zero_in_log_region_gap` combines this with the proved reality and quadratic-character conclusions for an actual zero.

[LFunctionFiniteConductors.lean](../TwinPrime/Analytic/LFunctionFiniteConductors.lean#L20) proves a positive lower bound for all nonprincipal `‖Lχ(1)‖` at each fixed modulus, then uniformly for `0<q≤Q`. It also proves a positive uniform gap for every real primitive zero with `1<q≤Q`, without a near-one restriction on the zero. The constants use finiteness, qualitative nonvanishing and the coarse derivative budget; no quantitative dependence on `Q` is asserted.

Finally, [SiegelZeroGap.lean](../TwinPrime/Analytic/SiegelZeroGap.lean#L17) proves `(log q)²≤16q^(ε/2)/ε²`. For `q≥256`, its `real_zero_power_gap_of_value_lower_bound` therefore gives

```text
‖Lχ(1)‖≥c q^(−ε/2)  ⇒  1−β≥[c ε²/(160 exp(2))] q^(−ε).
```

The global conversion theorem takes the minimum of this coefficient and the proved finite-conductor gap for `q≤256`; `q^(−ε)≤1` handles the finite range. Its value premise is now discharged by `siegel_value_lower_bound`, proved below through a separate argument. The value theorem does not use this zero-gap conversion as a premise.

## The checked four-factor positive series

For quadratic characters `χ₁,χ₂` of a common positive modulus `Q`, define, using **Dirichlet convolution** multiplication of arithmetic functions,

```text
aχ := toArithmeticFunction (χ ·)
c  := ArithmeticFunction.zeta * aχ₁ * aχ₂ * a(χ₁*χ₂).
```

[QuadraticProductCoefficients.lean](../TwinPrime/Analytic/QuadraticProductCoefficients.lean#L21) now defines this function and proves `quadraticProductCoefficients_isMultiplicative`, `quadraticProductCoefficients_one`, `quadraticProductCoefficients_nonneg`, and `one_le_quadraticProductCoefficients_square`. The last gives `c(n²)≥1` for `n≠0`. These use `ComplexOrder`, so the coefficients are nonnegative real numbers. At a prime `p`, put `a=χ₁(p)` and `b=χ₂(p)`. The local generating series is

```text
1 / [(1−X)(1−aX)(1−bX)(1−abX)].
```

For the common modulus, if `p|Q`, both values vanish and this is `(1−X)^(−1)`. Otherwise `a,b∈{1,−1}`: it is `(1−X)^(−4)` when both are `1`, and `(1−X²)^(−2)` in the other three cases. Therefore the prime-power coefficients are respectively `1`, `binomial(k+3,3)`, or `0` for odd `k` and `k/2+1` for even `k`. These are finite coefficient identities; no infinite Euler-product interchange is needed for their proof.

The pinned [Nonvanishing.lean](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Nonvanishing.lean#L75) exposes `zetaMul`, `isMultiplicative_zetaMul`, `zetaMul_prime_pow_nonneg`, and `zetaMul_nonneg` for the **two-factor** product. The new proof uses these, a finite twisted-pair convolution identity, alternating prime-power sums and multiplicative factorization. It proves the required positivity and square lower bounds, without exposing every displayed closed coefficient formula as a separate theorem. Positivity of two unrelated `zetaMul` functions is not used as a substitute for the four-factor identity.

[QuadraticProductLSeries.lean](../TwinPrime/Analytic/QuadraticProductLSeries.lean#L35) iterates [ArithmeticFunction.LSeriesSummable_mul and LSeries_mul'](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Convolution.lean#L182), and uses the actual L-function identities to prove absolute summability and

```text
LSeries c s = ζ(s)Lχ₁(s)Lχ₂(s)L(χ₁*χ₂)(s),  Re(s)>1.
```

The summability and product identity need no quadratic or nonprincipal hypothesis. The same module proves that `Z(s)Lχ₁(s)Lχ₂(s)L(χ₁*χ₂)(s)` is entire when all three character factors are nonprincipal. Its value at one, and the actual punctured limit of `(s−1)` times the unregularized product, equal the product of the three `L(1)` values. This value is nonzero by qualitative nonvanishing. Distinct nonprincipal quadratic characters satisfy `χ₁*χ₂≠1`. Here [Z(1)=1](../TwinPrime/Analytic/ZetaContinuation.lean#L148), so the proved limit gives the residue without treating `ζ(1)` as finite. Equal characters or a principal factor change the pole order and remain separate cases. The later centered comparison supplies the quantitative residue lower bound under its explicit nonpositive-product condition.

[QuadraticProductPartialSums.lean](../TwinPrime/Analytic/QuadraticProductPartialSums.lean) proves that the actual finite Dirichlet sum at every real exponent is the complex cast of the corresponding real weighted sum. The real sum is nonnegative, monotone in its natural cutoff, and at least one for cutoff `X≥1`; the complex sum is also at least one in `ComplexOrder`. These finite statements require no infinite-series convergence at exponents below one.

Different primitive conductors are now handled by the proved common-level route: [CharacterCommonLevel.lean](../TwinPrime/Analytic/CharacterCommonLevel.lean) induces to `Q=q₀q` and preserves conductor and quadraticity. [LFunctionInducedValue.lean](../TwinPrime/Analytic/LFunctionInducedValue.lean#L84) preserves the exact Euler factors from [LFunction_changeLevel](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L150), bounds their norms at one by `1+log Q`, and proves that they introduce no zeros for `Re(s)>0`. Thus induced values are compared with primitive values explicitly. A direct different-modulus coefficient construction is an optional alternative, not a missing premise of the proof.

## Checked cancellation and the summatory main term

This checkpoint is fully verified: the root build passed 8857 jobs, and the integrated axiom audit passed all 896 selected declarations, including all 84 new public theorems in 18 modules, with only `Classical.choice`, `propext` and `Quot.sound` and zero errors. The source scan covered 202 Lean files with no holes, project axioms or trust bypasses. The printed Siegel value and zero-gap theorem types have no supplied value hypothesis. The twin-prime endpoint still requires the independent Siegel–Walfisz and `(B*)` inputs.

| New module | Proved conclusion |
| --- | --- |
| [CharacterPeriodSum](../TwinPrime/Analytic/CharacterPeriodSum.lean#L83) | Every nonprincipal character modulo `Q` has initial sum norm at most `Q`, including imprimitive characters. |
| [CharacterConvolutionMass](../TwinPrime/Analytic/CharacterConvolutionMass.lean) | Absolute pair and triple masses are at most `x(1+log x)` and `x(1+log x)²`, for `x≥1`. |
| [ReciprocalPowerSums](../TwinPrime/Analytic/ReciprocalPowerSums.lean#L19) | Exact finite bound `Σ_{n≤x}n^(−α)≤x^(1−α)/(1−α)` for `0≤α<1`; the square-root constant is `2`. |
| [CharacterConvolutionCancellation](../TwinPrime/Analytic/CharacterConvolutionCancellation.lean#L39) | Nonprincipal pair and triple sum norms are bounded by `3Q√x` and `10Q²x^(2/3)(1+log x)`, with real cutoffs. |
| [CharacterConvolutionPower](../TwinPrime/Analytic/CharacterConvolutionPower.lean#L30) | The triple sum norm is at most `130Q²x^(3/4)`, with a natural-prefix version including zero. |
| [PowerDirichletTail](../TwinPrime/Analytic/PowerDirichletTail.lean#L132) and [PowerDirichletContinuation](../TwinPrime/Analytic/PowerDirichletContinuation.lean#L120) | Power-bounded prefixes give quantitative ordered tails, locally uniform convergence and identification with a separately known holomorphic function. |
| [CharacterConvolutionContinuation](../TwinPrime/Analytic/CharacterConvolutionContinuation.lean) | The actual triple ordered series agrees with three L-functions on `Re(s)>3/4`. At one its reciprocal-tail bound is `1300Q²M^(−1/4)`. The coefficient cancellation premise is discharged. |
| [ZetaConvolutionPowerBounds](../TwinPrime/Analytic/ZetaConvolutionPowerBounds.lean) and [ZetaConvolutionAsymptotic](../TwinPrime/Analytic/ZetaConvolutionAsymptotic.lean) | The finite hyperbola estimates give error `(1+25C)x^(4/5)(1+log x)²` for a zeta convolution, where the inner sum bound is `Cx^(3/4)` and its absolute mass is at most `x(1+log x)²`. The main term is its actual ordered reciprocal limit. |

For the application, take three nonprincipal characters `χ₁,χ₂,χ₁χ₂` at common level `Q`, let `b₃` be their triple convolution, and `c=ζ*b₃`. The proved actual-character specialization in [CharacterConvolutionAsymptotic.lean](../TwinPrime/Analytic/CharacterConvolutionAsymptotic.lean) is:

```text
S(x) := Σ_{n≤x} c(n),   λ := Lχ₁(1)Lχ₂(1)L(χ₁χ₂)(1),
‖S(x)−λx‖ ≤ C_Q x^(4/5)(1+log x)²,
C_Q := 1+3250Q²,   x≥1.
```

The coefficient identification uses the ordered continuation, not absolute summability of `b₃(n)/n`. The finite hyperbola split is now `y=x^(4/5)`, `z=x^(1/5)`: the absolute head costs `x^(4/5)(1+log x)²`, the short strip costs `4C x^(4/5)`, the overlap costs `C x^(4/5)`, and the reciprocal tail with its floor costs `20C x^(4/5)`. With `C=130Q²`, their total gives `1+3250Q²`.

The earlier paper proposal retained the triple logarithm and used cutoffs `x^(3/4),x^(1/4)` to target a sharper four-factor error `O(Q²x^(3/4)(1+log x)²)`. That sharper error is not the present formal conclusion. Absorbing the logarithm first permits reuse of the checked pure-power tail theorem and gives the sufficient exponent `4/5`. The implemented centered continuation absorbs the remaining logarithmic square and works on `Re(s)>9/10`; the **triple** continuation already reaches `Re(s)>3/4`.

## Checked centered weighted residue comparison

[QuadraticCenteredCoefficients.lean](../TwinPrime/Analytic/QuadraticCenteredCoefficients.lean#L48) defines `d=c−λ·ArithmeticFunction.zeta`. At every natural `N`, its prefix sum is exactly `S(N)−Nλ`. Since `1+log N≤21N^(1/20)` for `N≥1`, the proved bound is

```text
‖Σ_{n≤N}d(n)‖ ≤ 441 C_Q N^(9/10),
```

including the zero prefix. [QuadraticCenteredFunction.lean](../TwinPrime/Analytic/QuadraticCenteredFunction.lean) sets

```text
H(s) := regularizedQuadraticLFunctionProduct(s)−λ regularizedRiemannZeta(s),
G(s) := dslope H 1 s.
```

The actual residue identity gives `H(1)=0`, and `G` is entire when the three character factors are nonprincipal. For `s≠1`, its exact formula is `G(s)=F(s)−λζ(s)`. [QuadraticCenteredContinuation.lean](../TwinPrime/Analytic/QuadraticCenteredContinuation.lean#L51) identifies the ordered `d`-series with `G` on `Re(s)>9/10` using the prefix estimate, absolute convergence on `Re(s)>1`, and analytic uniqueness. It does not assert absolute summability below one.

For `19/20≤β<1`, [the uniform real tail](../TwinPrime/Analytic/QuadraticCenteredContinuation.lean#L95) and the exact finite centering identity give

```text
T_N(β) = F(β) + λ (Σ_{n≤N}n^(−β)−ζ(β)) + Δ_N,
‖Δ_N‖ ≤ 18522 C_Q N^(−1/20),   N≥1.
```

The constant is `2·441·(1+20)=18522`. [ZetaRealTruncation.lean](../TwinPrime/Analytic/ZetaRealTruncation.lean) proves the correctly signed pole comparison and bounds the bracket's norm by `2N^(1−β)/(1−β)`. [ResidueCutoff.lean](../TwinPrime/Analytic/ResidueCutoff.lean) chooses the actual natural cutoff

```text
N := ceil((37044 C_Q)^20),
‖Δ_N‖≤1/2,   1≤N≤2(37044 C_Q)^20.
```

Finite coefficient positivity gives `T_N(β).re≥1`. Therefore `F(β).re≤0` is sufficient; a product zero is a special case. [QuadraticResidueComparison.lean](../TwinPrime/Analytic/QuadraticResidueComparison.lean#L57) proves, with `δ=1−β>0`,

```text
δ/(4N^δ) ≤ ‖λ‖.
```

No sign of the remainder or of `λ` is assumed. [ResidueConductorBound.lean](../TwinPrime/Analytic/ResidueConductorBound.lean) proves `N≤A Q^40` with `A:=2(37044·3251)^20`. Raising the upper cutoff bound to the positive exponent `δ` yields the weaker, useful lower bound `δ/(4A^δ Q^(40δ))≤‖λ‖` with the correct denominator direction. Every displayed estimate in this section is proved; no improper integral is needed.

## Checked conductor comparison and complete dichotomy

[CharacterCommonLevel.lean](../TwinPrime/Analytic/CharacterCommonLevel.lean) induces primitive characters of conductors `q₀,q` to `Q=q₀q`. Their primitive conductors remain `q₀,q`, so `q₀≠q` ensures distinct induced characters. Both square-one identities survive induction, and their product is nonprincipal. The proof only needs comparisons for `q>q₀`; every conductor `q≤q₀`, including other characters at `q₀`, is handled by a finite minimum.

[LFunctionInducedValue.lean](../TwinPrime/Analytic/LFunctionInducedValue.lean) proves that the exact inducing multiplier at one has norm at most `∏_{p|Q}(1+1/p)≤1+log Q`. The finite squarefree-divisor expansion and harmonic bound prove this without a fixed power loss in `Q`. For `Re(s)>0`, every multiplier factor is nonzero, so induction preserves exactly the actual zeros away from the possible pole at one. [LFunctionPeriodBound.lean](../TwinPrime/Analytic/LFunctionPeriodBound.lean) proves ordered continuation for every nonprincipal character in this half-plane and the actual bound `‖Lη(1)‖≤5+log Q`, including imprimitive `η`. Its proof truncates at `Q`: the period-sum tail is at most `4` and the head is at most `1+log Q`.

Thus [QuadraticAuxiliaryComparison.lean](../TwinPrime/Analytic/QuadraticAuxiliaryComparison.lean) proves

```text
‖λ‖ ≤ 5 ‖Lχ₀(1)‖ ‖Lχ(1)‖ (1+log Q)³,

F(β).re≤0,  19/20≤β<1  ⇒
  ‖Lχ(1)‖ ≥ δ/[20 ‖Lχ₀(1)‖ A^δ Q^(40δ) (1+log Q)³],
  δ:=1−β,  Q:=q₀q,  A:=2(37044·3251)^20.
```

The auxiliary value is strictly positive in norm by qualitative nonvanishing. The denominator `20` combines the residue factor `4` and the upper-bound factor `5`; no lower bound for an inducing multiplier is needed.

For any `ε>0`, [SiegelValuePower.lean](../TwinPrime/Analytic/SiegelValuePower.lean#L26) proves that `δ≤ε/80` and `Q≥1` imply

```text
Q^(40δ) (1+log Q)³ ≤ (1+6/ε)³ Q^ε.
```

Indeed `1+log Q≤(1+6/ε)Q^(ε/6)`, and `40δ+ε/2≤ε`. Consequently the comparison gives `k Q^(−ε)≤‖Lχ(1)‖`, where

```text
k := δ/[20 ‖Lχ₀(1)‖ A^δ (1+6/ε)³] > 0.
```

[SiegelValueFromComparison.lean](../TwinPrime/Analytic/SiegelValueFromComparison.lean#L21) separates `Q^(−ε)=q₀^(−ε)q^(−ε)` and sets `cε=min(c_finite, k q₀^(−ε))`. The finite constant applies to every nonprincipal character at `0<q≤q₀`; `q^(−ε)≤1` completes that range. This lemma retains the auxiliary product sign as an explicit input. The final theorem supplies it in both branches below.

[SiegelValue.lean](../TwinPrime/Analytic/SiegelValue.lean#L23) sets `δ₀=min(1/20,ε/80)>0` and uses the following exhaustive classical case split:

1. **A near-one primitive quadratic zero exists.** Choose one primitive `χ₀` of conductor `q₀>1` and one actual real zero `β∈[1−δ₀,1)`. Then `0<δ=1−β≤δ₀`, so both `β≥19/20` and `δ≤ε/80` hold. Its zero survives exact induction, hence `F(β)=0` for every target conductor `q>q₀`. The comparison and finite-conductor lemma give the uniform value bound.
2. **No such zero exists.** Fix `σ=1−δ₀` and the actual primitive quadratic character of conductor four constructed in [QuadraticAuxiliaryCharacter.lean](../TwinPrime/Analytic/QuadraticAuxiliaryCharacter.lean). [QuadraticNoZeroTransport.lean](../TwinPrime/Analytic/QuadraticNoZeroTransport.lean#L49) transfers the global primitive exclusion on `[σ,1)` to every nonprincipal quadratic character through its conductor. This includes all three common-level factors for `q>4`. [LFunctionRealSign.lean](../TwinPrime/Analytic/LFunctionRealSign.lean#L51) uses conjugation, continuity, positive real part at two, and qualitative nonvanishing at and to the right of one to prove each factor's real value at `σ` is positive. Zeta truncation proves `ζ(σ).re<0` for `19/20≤σ<1`. Hence the actual product has negative real part, and the same quantitative comparison applies with `δ=δ₀`.

There is no assumed existence of arbitrarily close zeros and no reversal of the zero-to-small-value implication. The first branch fixes its auxiliary object once for the chosen exponent, before ranging over target conductors and characters. The second branch supplies a concrete auxiliary object and proves the required sign. The final theorem has only `ε>0`, positive modulus, conductor greater than one, primitivity and `χ²=1` as conditions on its universally quantified arguments; it has no value, zero-gap, or zero-existence premise. Its `cε` is uniform but no effective numerical value is asserted.

Route attribution: [Tao's Notes 2, Exercises 58 and 60](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/) describe weighted two-factor and four-factor comparisons using hyperbola methods, with Perron as an alternative. The constants, centered ordered continuation and exact implementation above are established in the linked local modules.

## Optional improper-integral alternative

The following is a separate paper derivation, not a formalized integral comparison and not a remaining dependency of the Siegel value theorem. It can reach `Re(s)>4/5` without the extra logarithm absorption. Put `θ=4/5`, `E(x)=S(x)−λx`, and

```text
F(s) := ζ(s)Lχ₁(s)Lχ₂(s)L(χ₁χ₂)(s),
T_x(s) := Σ_{n≤x}c(n)n^(−s),
R_x(s) := E(x)x^(−s) − s ∫_x^∞ E(t)t^(−s−1) dt.
```

Here `x≥1` is real, the finite cutoff is `floor x`, the integral is complex-valued, and positive real bases use their usual complex powers. For `Re(s)>1`, exact Abel summation gives

```text
T_x(s) = F(s) + λ x^(1−s)/(1−s) + R_x(s).
```

The integral defining `R_x` converges locally uniformly for `Re(s)>θ`. Its holomorphy requires a proof with uniform domination on compact subsets, including the logarithms introduced by differentiation. An identity theorem can then extend the formula to `Re(s)>θ`, `s≠1`. To avoid treating a pole as holomorphic, clear it first: `(s−1)T_x(s)+λx^(1−s)−(s−1)R_x(s)` should equal the entire regularized product on this half-plane. The known residue identity supplies the value at one. This does **not** identify the generally divergent raw four-factor `LSeries` with `F` below one.

For `σ=Re(s)>θ`, `ν=σ−θ` and `L=1+log x`, direct integration gives the useful explicit bound

```text
‖R_x(s)‖ ≤ C_Q x^(θ−σ)
  * [L² + |s| (L²/ν + 2L/ν² + 2/ν³)].
```

Indeed, `∫_x^∞t^(−1−ν)(1+log t)²dt` equals `x^(−ν)[L²/ν+2L/ν²+2/ν³]`. This retains the dependence on distance from the convergence boundary and on complex height. For a real `β∈[9/10,1)`, `ν≥1/10` and `|β|≤1`, so

```text
‖R_x(β)‖ ≤ 2211 C_Q x^(4/5−β)(1+log x)².
```

The constant is `1+10+200+2000`. The elementary bound `1+log x≤41x^(1/40)` then gives

```text
‖R_x(β)‖ ≤ K C_Q x^(−1/20),   K:=2211*41²=3716691.
```

Taking `x=(2K C_Q)^20` makes this at most `1/2`. If `β` is an actual zero of one nonprincipal character factor, then `F(β)=0`; zeta has no pole there. The checked finite positivity gives `T_x(β)≥1`. Since `δ:=1−β>0`, the pole term in the formula is **positive-sign** `λx^δ/δ`, and hence

```text
‖λ‖ ≥ δ/(2x^δ).
```

No sign is assigned to `R_x(β)`: the deduction uses its absolute bound. A norm argument already suffices, so positivity of each individual `L(1)` need not be silently assumed at this step. If a real inequality for `λ` is used instead, its real nonnegativity must first be justified from `S(x)/x→λ` and coefficient positivity. The pole term has denominator `1−β`, not `β−1`.

## Remaining work and scope limits

The uniform Siegel value estimate is now proved. The independent improper-integral alternative above is optional and remains unformalized; it is no longer an obligation for this route. The earlier qualitative [LSeries_positive_of_differentiable_of_eqOn](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Positivity.lean#L107) is not being misapplied to a meromorphic four-factor series: the proof uses finite positivity and an entire **centered** function, keeping the original zeta pole explicit.

The unconditional exceptional zero-gap theorem uses the sharp near-one derivative estimate and the finite-conductor gap already proved. Actual smoothed inversion and finite quantitative contours for the relevant character sums now check. Their uniform asymptotic assembly, the principal contour assembly, and centered finite differences now prove independent Siegel–Walfisz, as recorded in the [classical proof map](CLASSICAL_DISTRIBUTION_THEOREM.md). The uniform value theorem neither proves a Landau–Page uniqueness theorem across different characters nor supplies an effective lower-bound constant. The independent twin-prime bilinear estimate `(B*)` remains unresolved.
