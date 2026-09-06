# A formalized Pólya–Vinogradov route to the finite Vaughan mean

The finite Type I identities and estimates, exact primitive-character
counts, eighth-root cutoff comparisons, and full maximal mean below are
now proved in Lean. The centered large-conductor tail, its asymptotic
absorption at `T=2X+2`, and the full implication from uniform centered
Siegel–Walfisz to maximal BV are also proved. Both pointwise and maximal
Siegel–Walfisz suffice: the uniform pointwise-to-maximal conversion is
proved. The [independent pointwise Siegel–Walfisz theorem](CLASSICAL_DISTRIBUTION_THEOREM.md)
now supplies the distribution input; §8 records the finite implementation map.

The key choice is to use BV-internal cutoffs
`U=V=floor(T^(1/8))`. The resulting middle term has exponent 15/16 instead
of 5/6. That remains a power saving after conductor summation, and permits
the existing elementary Pólya–Vinogradov bounds to handle Type I directly.
This proves BV conditionally on Siegel–Walfisz. It does not prove
Siegel–Walfisz itself or the separate twin-prime B* input.

## 1. The exact four terms

For a complex character χ, write `P(t,χ)=characterPsi t χ`. Define

```text
S1(U,t,χ) = Σ_{0<n≤t} (μ_≤U * log)(n) χ(n),
S2(U,V,t,χ) = Σ_{0<n≤t} (c_(U,V) * ζ)(n) χ(n),
L(V,t,χ) = P(min(t,V),χ),
SII(U,V,t,χ) = characterVaughanII U V t χ,
c_(U,V) = μ_≤U * Λ_≤V.
```

Real arithmetic-function coefficients are embedded into ℂ. The checked
`characterPsi_eq_vaughan` gives, for every natural endpoint and both cutoffs,

```text
P(t,χ) = S1(U,t,χ) − S2(U,V,t,χ) + L(V,t,χ) + SII(U,V,t,χ).     (V)
```

The low term cannot be omitted when t≤V. The existing
`vaughanIdentity_sum` assumes its summation indices exceed V and is not the
appropriate full-prefix identity. Also, the existing `bilinearTerm` and
`bilinearPairs` concern the shifted correlation with Λ(mn+2); the unshifted
BV character sum uses `characterVaughanII` instead.

The named sums are `characterVaughanI1` and `characterVaughanI2` in
`CharacterVaughanTypeI.lean`; `characterPsi_eq_vaughan_types` is (V) in
these names. The proved `characterVaughanI1_eq_factor_sum` and
`characterVaughanI2_eq_factor_sum` give

```text
S1(U,t,χ)
 = Σ_{0<d≤U} μ(d)χ(d) Σ_{0<r≤t/d} log(r)χ(r),                 (I1)

S2(U,V,t,χ)
 = Σ_{0<d≤UV} c_(U,V)(d)χ(d) Σ_{0<r≤t/d} χ(r).              (I2)
```

All quotients are natural division. These identities retain t exactly;
they do not replace the inner quotient by a real endpoint. If d>t, the
inner sum is empty. The upper bound UV in (I2) is justified by the checked
`vaughanCoefficient_eq_zero_of_lt`. The d=0 index is excluded, as in the
convolution divisor-antidiagonal representation.

The reusable `sum_character_convolution_eq_factor_sum` proves this
reindexing for any real arithmetic functions whose first factor vanishes
above its stated cutoff. The Vaughan specializations discharge that
support condition explicitly, for all natural cutoffs, endpoints, and
moduli.

## 2. Primitive moduli q>1: uniform finite endpoint bounds

Let q>1 and χ be primitive modulo q. The existing `CharacterInterval` and
`CharacterLogInterval` theorems give, for every natural y,

```text
|Σ_{0<r≤y} χ(r)| ≤ sqrt(q)(1+log q),
|Σ_{0<r≤y} log(r)χ(r)| ≤ 2sqrt(q)(1+log q)log y.              (PV)
```

The second formula also covers y=0, with Lean's totalized `log 0=0`.
The needed local APIs are `norm_sum_primitive_character_Ioc_le` and
`norm_sum_primitive_character_log_Ioc_le`. Their assumptions are q>1 and
primitivity; they do not assume character cancellation separately.

For any selected endpoint t≤T, natural logarithm monotonicity gives
`log(t/d)≤log T`. Use `|μ(d)|≤1` and `|χ(d)|≤1` in (I1). There are U
positive outer indices, so

```text
|S1(U,t,χ)| ≤ 2 U sqrt(q)(1+log q)log T.                     (B1)
```

For (I2), the checked `abs_vaughanCoefficient_le_log` gives
`|c_(U,V)(d)|≤log d≤log(UV)`. Hence

```text
|S2(U,V,t,χ)| ≤ UV log(UV) sqrt(q)(1+log q).                 (B2)
```

Both budgets are uniform over all t≤T. Consequently the same bounds hold
for the corresponding finite maxima, separately for every character. No
additional logarithm is needed to take these maxima. In particular, the
proof must not sum (B1) or (B2) over all possible endpoints.

`CharacterTypeIBounds.lean` proves (B1) and (B2) as
`norm_characterVaughanI1_le` and `norm_characterVaughanI2_le`, then proves
`characterVaughanI1Max_le` and `characterVaughanI2Max_le` for their finite
maxima. The I2 bound is independent of t and needs no upper-endpoint
hypothesis.

Finally, `|χ(n)|≤1` and `0≤Λ(n)≤log n` give

```text
|L(V,t,χ)| ≤ V log V.                                      (BL)
```

This is `norm_characterPsi_min_le` in `CharacterTrivialBounds.lean`.
That module defines `characterPsiMax T χ` over `Icc 0 T`; the full
four-term maximal inequality is `characterPsiMax_le_vaughan`.

The finite endpoint conventions are harmless: at U=0 or UV=0 the relevant
outer convolution sum is zero, and at V=0 the low term is zero. The later
cutoff selection will use positive U,V, so these edge cases need not enter
the power comparisons.

## 3. Weighted primitive-character means

For a nonnegative quantity F(q,χ), use the nonprincipal-modulus mean

```text
W_R(F) = Σ_{2≤q≤R} (q/φ(q)) Σ_{χ primitive mod q} F(q,χ).
```

At a positive modulus the number of primitive characters is at most the
number of all characters, namely φ(q). Therefore a bound `F(q,χ)≤A(q)`
with A(q)≥0 implies

```text
W_R(F) ≤ Σ_{2≤q≤R} q A(q).
```

The exact character count is already available in Mathlib, and the
repository uses this conversion in `CharacterPrimitiveReduction.lean`,
inside `progressionMaxError_le_primitiveCharacter_sum`:

```lean
letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
  simpa only [Nat.card_eq_fintype_card] using
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
```

Here `hq : 0 < q`. Apply `Finset.card_filter_le` to `univ` filtered by
`IsPrimitive`, then use `Finset.card_univ` and `hcard`. Since
`Nat.totient_pos.mpr hq` gives φ(q)>0, multiplying the resulting cardinal
bound by q/φ(q) gives at most q. This is an exact finite counting argument;
it does not assume a primitive-character counting asymptotic.
`PrimitiveCharacterCounting.lean` now packages it as
`card_dirichletCharacter_eq_totient`,
`card_primitiveCharacters_le_totient`, and `weighted_primitive_count_le`,
with finite weighted-budget summation theorems. No extra logarithm is
introduced by counting characters.

This is where the weight and the character count cancel. Neither the
factor q nor a character multiplicity is discarded. Elementary comparison
with the largest summand gives

```text
Σ_{2≤q≤R} q ≤ R²,
Σ_{2≤q≤R} q sqrt(q)(1+log q) ≤ R² sqrt(R)(1+log R).
```

Together with (B1), (B2), and (BL), this yields the explicit finite budgets

```text
W_R(max_{t≤T}|S1|)
 ≤ 2 U R² sqrt(R)(1+log R)log T,

W_R(max_{t≤T}|S2|)
 ≤ UV log(UV) R² sqrt(R)(1+log R),

W_R(max_{t≤T}|L|) ≤ V log V R².                             (WM)
```

The finite empty sums R=0,1 are included. `CharacterTypeIMean.lean` proves
the two Type I bounds as `primitive_character_vaughanI1_maximal_mean_le`
and `primitive_character_vaughanI2_maximal_mean_le`.
`primitive_character_low_mean_le` averages the common bound V log V,
which controls every selected low-term endpoint.

## 4. Conductor one is separate

Pólya–Vinogradov above excludes q=1. There is one character modulo one and
its weight q/φ(q) is one. The elementary inequality, uniformly for t≤T,

```text
|P(t,χ mod 1)| ≤ Σ_{0<n≤t} Λ(n) ≤ T log T                  (ONE)
```

supplies its contribution to an *uncentered* maximal mean.
`characterPsiMax_le` proves this common maximum bound, and
`primitive_characterPsiMax_mean_le` separates modulus one before using
(V) over q≥2. Thus the three principal Type I pieces do not require
separate cancellation bounds.

(ONE) is not an estimate for `ψ(t)−t` with a saving. It does not supply the
conductor-one portion of the small-conductor Siegel–Walfisz input. Using a
prime-error estimate derived from BV to prove that BV input would be circular.

## 5. Why cube-root cutoffs fail for this direct PV approach

With U=V approximately T^(1/3), (WM) at R approximately sqrt(T) has powers

```text
Type I1: U R^(5/2)  ≈ T^(19/12),
Type I2: UV R^(5/2) ≈ T^(23/12).
```

The intended quadratic part of the cumulative mean is
`sqrt(T)R²≈T^(3/2)=T^(18/12)`. Thus the direct triangle-plus-PV argument
does not establish the classical cube-root-cutoff mean bound. Logarithmic
losses in R cannot absorb those fixed positive power gaps.

Instead, choose smaller internal cutoffs. In the range R≤sqrt(T), the
condition `UV≤T^(1/4)` ensures

```text
UV R² sqrt(R) ≤ sqrt(T)R².
```

Balanced eighth-root cutoffs satisfy this condition and keep a positive
power saving in Type II. They are independent of the repository's
twin-correlation primary cutoff; changing the internal choice in a BV proof
does not change that correlation decomposition.

## 6. Exact eighth-root comparisons and the combined polynomial

Assume T≥256 and put

```text
y = (T:ℝ)^(1/8),   W = floor(y),   U=V=W.
```

Since y≥2, the elementary floor inequalities give

```text
0<W,     y/2 ≤ W ≤ y,
W² ≤ T^(1/4),     W≤sqrt(T),     log W≤log T,
log(W²)≤log T.
```

For example, `floor y>y−1` and y≥2 imply `floor y≥y/2`.
All comparisons with natural W are real-cast comparisons when used in
these displays. For `1≤R≤sqrt(T)`, one also has

```text
sqrt(R)≤T^(1/4),
1+log R≤log T,     log T≥1.
```

The last two hold with substantial slack under T≥256. Thus (WM) gives

```text
W_R(max|S1|) ≤ 2sqrt(T)R² log²T,
W_R(max|S2|) ≤ sqrt(T)R² log²T,
W_R(max|L|)  ≤ sqrt(T)R² log²T.                              (SMALL)
```

The actual Type II theorem in `CharacterVaughanMean.lean` has the budget

```text
2 D(T)^4 log T L_R ·
 [T + RT(1/sqrt(U/2)+1/sqrt(V/2)) + R²sqrt(T)],

D(T)=clog 2 (T+1),     L_R=1+2log(R+1).                     (II)
```

The half-cutoffs are essential: the global cells have starts and lengths
exactly `2^k`, while the cutoff masks permit cells beginning as low as U/2
or V/2. No arbitrary length is equated with a power of two.
For W≥T^(1/8)/2,

```text
W/2 ≥ T^(1/8)/4,
1/sqrt(W/2) ≤ 2T^(−1/16),
RT(1/sqrt(U/2)+1/sqrt(V/2)) ≤ 4R T^(15/16).                 (HALF)
```

In the same restricted R-range,

```text
D(T) ≤ (2/log 2)log T,
L_R ≤ 2log T.
```

For the first inequality, the Lean proof uses the comparison
`clog 2 (T+1)≤Nat.log 2 T+1≤log T/log 2+1`, then `log T≥log 2`.
For the second, use `R+1≤2sqrt(T)` and
`1+2log 2≤log T`, valid here. `BVInternalCutoffs.lean` proves the floor,
power, and reciprocal-square-root comparisons. `BVLogComparisons.lean`
proves the logarithm and depth bounds from `log 256=8log 2` and
`1/2≤log 2`, including `one_le_log_of_256_le`.

Equations (II) and (HALF) consequently imply the proved budget

```text
Type II mean
 ≤ 16(2/log 2)^4 [T + R T^(15/16) + R²sqrt(T)] log^6T.
```

`VaughanMeanParameters.lean` proves this numerical absorption as
`bvTypeIIBudget_le`. Its Type I bound has constant four, and the principal
term costs at most one copy of the final polynomial. Taking the finite
maximum in (V), adding (ONE) and (SMALL), and using `log T≥1`, gives the
proved full mean:

```text
Σ_{1≤q≤R} (q/φ(q)) Σ_{χ primitive mod q} max_{0≤t≤T}|P(t,χ)|
 ≤ C0 [T + T^(15/16)R + sqrt(T)R²] log^6T,

C0 = 5 + 16(2/log 2)^4,
T≥256, 1≤R≤sqrt(T).                                       (MEAN)
```

This is `primitive_character_mean_value` in `VaughanMeanValue.lean`.
`bvMeanConstant` is C0 and `bvMeanPolynomial T R` is the displayed
polynomial. `primitive_character_mean_value_inv` proves the same bound
with χ⁻¹. These theorems take no mean-value or prime-distribution estimate
as an input: the raw finite mean and its numerical budget are both proved.

The numerical constant is deliberately generous. The Type II sum may
include q=1 when used as an upper bound for its q>1 contribution; this is
legitimate because all summands are nonnegative. Its inclusion does not
replace or omit the separate principal contribution (ONE).

## 7. Why a mean bound restricted to R≤sqrt(T) is enough

The conductor step only uses moduli Q≤sqrt(T), eventually with additional
logarithmic saving. Fix such Q and an integer R0 with `1≤R0≤Q`. Every
cumulative endpoint r in the hypothesis of `ConductorAbel` then satisfies
`r≤Q≤sqrt(T)`, exactly the range of (MEAN).

Use the nonnegative coefficient sequence

```text
a(r) = (r/φ(r)) Σ_{χ primitive mod r} max_{t≤T}|P(t,χ)|.
```

Its cumulative bound has constants independent of r:

```text
A=C0 T log^6T,
B=C0 T^(15/16) log^6T,
D=C0 sqrt(T) log^6T.
```

`ConductorMean.lean` identifies this sequence as
`primitiveCharacterPsiWeight T` and proves that its `coefficientSum`
is exactly the actual weighted primitive-character mean on `Icc 1 r`.
The checked Abel inequality therefore gives

```text
Σ_{R0<r≤Q} a(r)/r
 ≤ C0 log^6T [T/R0 + T^(15/16)(1+log(Q/R0)) + 2sqrt(T)Q].
```

At every r>R0≥1 a primitive character is nonprincipal, so its centered
and uncentered maxima agree. This bridge is now proved and applied:
`primitiveCharacterMass_eq_sum_characterPsiMax` and
`primitiveCharacterPsiWeight_div_eq` identify `a(r)/r` with
`primitiveCharacterMass T r / φ(r)` precisely for r>1.
`sum_large_primitiveCharacterMass_le` then proves the actual centered
tail bound above from (MEAN). Its right side is
`bvLargeConductorBudget T R0 Q`; it has no remaining mean-bound hypothesis.
The centered conductor-one term stays outside this tail.

For clarity, put M(T,r)=`primitiveCharacterMass T r`, Cφ=
`totientReciprocalConstant`, and define

```text
Tail(T,R0,Q) = if R0≤Q then bvLargeConductorBudget T R0 Q else 0.
```

For T≥256, R0≥1, and every natural Q≤sqrt(T), the proved all-Q split is

```text
Σ_{1≤q≤Q} progressionMaxError(T,q)
 ≤ Cφ(1+log Q) [Σ_{1≤r≤min(R0,Q)} M(T,r)/φ(r) + Tail(T,R0,Q)]
   + Q[log Q + 2sqrt(T)log T].                              (SPLIT)
```

This is `sum_progressionMaxError_le_small_conductors_and_tail_if`.
It includes Q=0 and Q<R0: the tail is zero, and the small-conductor sum
is clipped at Q. The Abel theorem is only used in the branch R0≤Q.
The uncentered modulus-one contribution to the cumulative mean does not
replace the centered modulus-one error in the small-conductor sum.

`SmallConductorMean.lean` supplies an exact finite criterion for that sum.
If E≥0 and

```text
∀ r∈Icc 1 R0, ∀ primitive χ mod r, characterMaxError T χ ≤ E, (SC)
```

then `primitiveCharacterMass_div_totient_le` gives M(T,r)/φ(r)≤E
for 1≤r≤R0,
and `sum_small_primitiveCharacterMass_le` gives

```text
Σ_{1≤r≤min(R0,Q)} M(T,r)/φ(r) ≤ R0 E.                       (SM)
```

The counting lemma (SM) itself also permits R0=0. Combining it with
(SPLIT), `sum_progressionMaxError_le_small_conductor_budget` proves

```text
Σ_{1≤q≤Q} progressionMaxError(T,q)
 ≤ Cφ(1+log Q) [R0 E + Tail(T,R0,Q)]
   + Q[log Q + 2sqrt(T)log T],                              (CRITERION)
```

under T≥256, R0≥1, Q≤sqrt(T), E≥0, and exactly the explicit input (SC).
This is a proved finite implication. No small-conductor estimate is
inferred from the uncentered mean or from the criterion itself.

## 8. Implemented modules

The following modules implement the finite estimates and the completed
conditional BV assembly:

| Module | Completed result |
| --- | --- |
| `CharacterTrivialBounds.lean` | Low and principal budgets; uncentered maximum; centered/uncentered equality for primitive q>1. |
| `CharacterVaughanTypeI.lean` | Exact convolution reindexing, both Type I factor sums, named full Vaughan identity. |
| `PrimitiveCharacterCounting.lean` | Exact character cardinality and finite weighted primitive counts. |
| `CharacterTypeIBounds.lean` | Uniform pointwise Type I bounds, their finite maxima, full four-term maximum inequality. |
| `CharacterTypeIMean.lean` | Type I and low weighted means, separate q=1 budget, full raw mean with actual Type II input discharged. |
| `BVInternalCutoffs.lean` | Eighth-root floor, power, and half-cutoff square-root comparisons. |
| `BVLogComparisons.lean` | Explicit logarithm and dyadic-depth comparisons for T≥256. |
| `VaughanMeanParameters.lean` | Numerical absorption into the polynomial with exponent 15/16 and log^6 T. |
| `ConductorMean.lean` | Exact centered-tail bridge from an explicit quadratic cumulative mean. |
| `SmallConductorMean.lean` | Exact finite consequence (SM) of the supplied centered input (SC). |
| `VaughanMeanValue.lean` | Proved full mean, inverse-character version, actual centered tail, all-Q split, and small-E criterion. |
| `BVConductorGrowth.lean` | Uniform logarithmic absorption of the actual weighted tail at `T=2X+2`, with `Ktail=768CφC0+1`. |
| `BVSmallConductorGrowth.lean` | Ceiling logarithmic cutoff, its range at `2X+2`, admissible modulus comparisons, and small-conductor budget absorption. |
| `SiegelWalfisz.lean` | Explicit pointwise and maximal centered uniform propositions, including primitive conductor one; these definitions are not proofs. |
| `SiegelWalfiszMaximal.lean` | Proved implication from pointwise to maximal Siegel–Walfisz, uniform in growing conductors and all natural endpoints. |
| `BombieriVinogradovFromSW.lean` | Complete maximal and pointwise Siegel–Walfisz implications to the exact named maximal BV statement. |

These build on the earlier exact Vaughan, primitive Pólya–Vinogradov,
large-sieve, maximal product-cutoff, conductor-regrouping, and Abel modules.
The finite identities retain natural division, positive factor support,
the original endpoint maxima, and all inducing-character multiplicities.

## 9. Completed asymptotic assembly and its supplied input

The former logarithmic absorption, endpoint conversion, and maximalization
steps are now proved. For any real target exponent A>0, set

```text
T = 2X+2,
R0 = bvSmallConductorCutoff A X = ceil((log X)^(A+9)),
B = A+9,
Q ≤ sqrt(X)/(log X)^B.
```

`eventually_bvLargeConductorBudget_le_log_saving` in
`BVConductorGrowth.lean` proves
uniformly in arbitrary R0,Q satisfying `1≤R0≤Q` and
`(log X)^(A+9)≤R0` that, eventually in X,

```text
Cφ(1+log Q) bvLargeConductorBudget (2X+2) R0 Q
 ≤ Ktail X/(log X)^A,
Ktail = 768CφC0+1.
```

Its finite precursor reduces the weighted tail to
`64CφC0 [8X log^7X/log^(A+9)X + 4X^(15/16)log^8X]`.
The proved eventual comparison `log^(A+8)X≤X^(1/16)` handles the second
term. The threshold depends on A, not on R0 or Q.

`BVSmallConductorGrowth.lean` proves, eventually,

```text
1≤R0,    (log X)^(A+9)≤R0≤2(log X)^(A+9)≤(log T)^(A+10).
```

Apply maximal centered Siegel–Walfisz with decay exponent `2A+12` and
conductor exponent `A+10`. If its constant is C, the resulting common
bound in (SC) is `E=C T/(log T)^(2A+12)`. The checked small-conductor
calculation gives

```text
Cφ(1+log Q) R0 E ≤ 12CφC X/(log X)^A.
```

It first obtains the stronger denominator `log^(A+2)X`, then weakens it.
The range `B=A+9` also implies the `A+2` range in
`CharacterExceptionGrowth.lean`, so the replacement error contributes at
most `X/(log X)^A`. The all-Q split retains the branch Q<R0, where the
tail is zero, including Q=0. The thresholds for all three bounds and the
Siegel–Walfisz input are combined before choosing Q. Thus
`MaximalSiegelWalfisz.bombieriVinogradov` proves the exact
`MaximalBombieriVinogradov` quantifiers with
`K=12CφC+Ktail+1` and `T=2X+2`.

The maximalization is also complete. `PointwiseSiegelWalfisz.maximal`
splits endpoints at `T/log^(a+2)T`. Short endpoints use the elementary
centered bound `t log t+t`, including t=0 and conductor one. Longer
endpoints satisfy `t≥sqrt(T)`, so `log T≤2log t` and eventually lie above
the pointwise threshold. Increasing its conductor exponent from b to b+1
makes the pointwise hypothesis applicable uniformly. In particular the
pointwise input used through this conversion has exponents `2A+12` and
`A+11`. `PointwiseSiegelWalfisz.bombieriVinogradov` composes the two proved
implications.

The required independent distribution theorem is `PointwiseSiegelWalfisz`:
for every a,b>0, uniform constants bound
`|ψ(t,χ)−1_(χ principal)t|` by `C t/log^a t` for every primitive conductor
`r≤log^b t` above a common endpoint threshold. It includes `ψ(t)−t` at
conductor one. The independent theorem is now proved in
[SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean),
using actual contours and centered finite differences. The separate signed
twin-prime bound B* remains open; these results do not prove the Twin Primes
Conjecture unconditionally.
