# Independent small-conductor prime distribution: source audit and proof

This audit concerns the Mathlib pin `v4.32.0`, commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, recorded in
[lake-manifest.json](../lake-manifest.json#L4).
The inventory was checked against local sources on 2026-09-04. Subsequent
repository work has proved the implications from pointwise centered
Siegel–Walfisz to its maximal form and from that form to the exact repository
Bombieri–Vinogradov statement. For primitive characters of conductor
greater than one, locally uniform ordered convergence, identification with
`LFunction`, and quantitative truncation are proved on `Re(s)>0`. The
repository also proves explicit L-function growth and derivative bounds,
a uniform lower bound on `Re(s)≥2`, a multiplicity-aware local Jensen zero
count, and logarithmic-derivative identities and three-four-one positivity
on `Re(s)>1`. Pole-corrected truncation of the actual zeta function is
proved for `Re(s)>0`, `s≠1`, with an entire regularization handling one.
The local expansion over the actual zeros is now proved with an explicit
conductor/height remainder. Its proof removes the divisor polynomial and
bounds a normalized holomorphic logarithm; it assumes no abstract zero
expansion. Quantitative inducing Euler corrections, an explicit bound for
the regular part of the zeta pole, and signs of the actual zero terms are
also proved.
The one-sided bounds retaining a selected actual zero, and the scalar
parameter contradiction needed for zero exclusion, are proved as well.
Their application now gives an explicit primitive L-function zero-free
region with at most one exceptional zero for each character. Any such
zero is real and simple and belongs to a quadratic character. The uniform
Siegel value lower bound at one and its arbitrary-power zero-gap consequence
are now proved independently, as described below. Uniqueness across different
characters is not asserted.
A separate zero-free region for the entire pole regularization of zeta
is also proved, with no exceptional zero.
Actual nonprincipal-character cancellation now also gives ordered triple
convolution convergence to the product of three L-functions on Re(s)>3/4,
including one. An explicit four-factor summatory error about the actual
product of their L(1) values is proved, with constant `1+3250q²` and error
`x^(4/5)(1+log x)²`. Centering by the actual residue now gives the weighted
comparison below one. Common-level Euler factors, a real-sign dichotomy,
and finite-conductor nonvanishing then prove one positive constant for
every primitive quadratic character at each fixed positive power exponent.
Section 5 records the exact ranges, constants, and verification status.
This note records those results alongside the pinned source inventory.
The [completed classical proof map](CLASSICAL_DISTRIBUTION_THEOREM.md)
now supplies independent centered pointwise Siegel–Walfisz and hence
unconditional BV and quantitative Mertens. B* remains unproved.

These zero-free results are repository additions. The pinned-Mathlib audit
found no quantitative zero-free region, exceptional-real-zero estimate,
Siegel–Walfisz theorem, Perron formula, or Wiener–Ikehara theorem was found
in the pinned sources. Searches included their usual names and variants
throughout `Mathlib/**/*.lean`. The sole Wiener–Ikehara match is an explanatory
comment in `PrimesInAP.lean`. `NumberTheory/SiegelsLemma.lean` concerns integer
linear algebra, not the exceptional-zero problem.

## 1. The exact repository distribution quantity

[CharacterMaximal.lean](../TwinPrime/Analytic/CharacterMaximal.lean#L17)
defines

```text
centeredCharacterPsi t χ = characterPsi t χ − (if χ = 1 then t else 0),
characterPsi t χ = Σ_{1≤n≤t} Λ(n)χ(n),
characterMaxError T χ = max_{0≤t≤T} ‖centeredCharacterPsi t χ‖.
```

The maximum is a genuine finite maximum over natural endpoints, including
zero. For a primitive character of conductor `r > 1`, the principal case is
excluded by the proved `primitive_character_ne_one`; at conductor one the
centered sum is exactly the ordinary ψ error.

The finite theorem
[sum_small_primitiveCharacterMass_le](../TwinPrime/Analytic/SmallConductorMean.lean#L40)
(namespace `TwinPrime.Analytic`) has the following input and conclusion:

```lean
(T R₀ Q : ℕ) (E : ℝ) (hE : 0 ≤ E)
(hsmall : ∀ r ∈ Icc 1 R₀, ∀ χ : DirichletCharacter ℂ r,
  χ.IsPrimitive → characterMaxError T χ ≤ E) :
(∑ r ∈ Icc 1 (min R₀ Q), primitiveCharacterMass T r / Nat.totient r)
  ≤ (R₀ : ℝ) * E
```

This is proved counting, not a distribution theorem.
[SiegelWalfisz.lean](../TwinPrime/Analytic/SiegelWalfisz.lean)
now defines the two precise uniform propositions. `PointwiseSiegelWalfisz`
says that for every real `A,B>0` there exist `C>0` and a natural `T₀≥2`,
depending only on `A,B`, such that for every natural `T≥T₀`, every natural
`1≤r≤(log T)^B`, and every primitive character modulo r,

```text
‖centeredCharacterPsi T χ‖ ≤ C T/(log T)^A.
```

`MaximalSiegelWalfisz` replaces the left side by `characterMaxError T χ`,
retaining the same quantifier order. Both include conductor one and are now
proved by the independent theorem and its maximalization. The repository proves

```text
PointwiseSiegelWalfisz → MaximalSiegelWalfisz → MaximalBombieriVinogradov.
```

The arrows include all endpoint, cutoff, logarithmic-budget, and final
asymptotic quantifier conversions; there is no remaining asymptotic gap
after the uniform pointwise hypothesis is supplied. Sections 7–8 describe
the proved steps. Section 6 and the [classical proof map](CLASSICAL_DISTRIBUTION_THEOREM.md)
record the independent proof supplying that hypothesis, uniformly in the
growing conductor family and including its principal term.

The already proved
[MaximalBombieriVinogradov.maximal_psi_error](../TwinPrime/Analytic/BombieriVinogradovPsi.lean#L37)
and `.psi_error` both explicitly take `hBV : MaximalBombieriVinogradov`.
They cannot discharge the conductor-one input in a proof of BV. The existing
BV-to-Mertens chain has the same dependency and supplies no independent PNT.

## 2. Checked L-function ingredients

The following signatures reproduce the mathematical content of the local
declarations. Open namespaces and notation are stated explicitly; `L` below
is Mathlib's notation for `LSeries`, and `Λ` is `vonMangoldt`.

In namespace `DirichletCharacter`, for `χ : DirichletCharacter ℂ N` and
`[NeZero N]`,
[DirichletContinuation.lean](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L75)
provides:

```lean
LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ}
  (hs : 1 < s.re) : LFunction χ s = LSeries (χ ·) s

differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
  (hs : s ≠ 1 ∨ χ ≠ 1) : DifferentiableAt ℂ (LFunction χ) s

differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
  Differentiable ℂ (LFunction χ)
```

The derivative also agrees with the L-series derivative on `1 < s.re`
(`deriv_LFunction_eq_deriv_LSeries`, line 79). The primitive functional equation
is [IsPrimitive.completedLFunction_one_sub](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L284):

```lean
{χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
completedLFunction χ (1 - s) =
  N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s
```

This is an identity, not a quantitative vertical-strip growth bound.

[Dirichlet.lean](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Dirichlet.lean#L400)
has, without an additional cancellation input:

```lean
DirichletCharacter.LSeriesSummable_twist_vonMangoldt
  {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
  LSeriesSummable (↗χ * ↗Λ) s

DirichletCharacter.LSeries_twist_vonMangoldt_eq
  {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
  L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / L ↗χ s

ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  {s : ℂ} (hs : 1 < s.re) :
  L ↗Λ s = -deriv riemannZeta s / riemannZeta s
```

Together with continuation, these identify the analytic generating function
on the absolutely convergent half-plane. They do not invert that generating
function to a finite ψ estimate.

The strongest located nonvanishing result is
[Nonvanishing.lean:397](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Nonvanishing.lean#L397):

```lean
DirichletCharacter.LFunction_ne_zero_of_one_le_re
  (χ : DirichletCharacter ℂ N) ⦃s : ℂ⦄
  (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : LFunction χ s ≠ 0

DirichletCharacter.LFunction_apply_one_ne_zero
  {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0
```

The proof also exposes the useful algebraic positivity inequality
[norm_LFunction_product_ge_one](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/Nonvanishing.lean#L307):

```lean
(χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) (y : ℝ) :
‖LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 *
  LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ ≥ 1
```

The nearby `LFunctionTrivChar_isBigO_near_one_horizontal` and
`LFunction_isBigO_horizontal` at lines 315 and 333 are local bounds as
`x → 0+`, for fixed modulus and, in the latter case, fixed character and
height. They contain no conductor/height dependence for their constants.
Nonvanishing on the boundary supplies no quantitative width to its left.
Compactness for a fixed finite character family and bounded height does not
control how those bounds deteriorate as the family and height grow.

## 3. Principal poles and arithmetic-progression boundary regularity

The conductor-one identity
[LFunction_modOne_eq](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L67)
is `LFunction χ = riemannZeta` for `χ : DirichletCharacter ℂ 1`.
For a general principal character, the same file proves:

```lean
LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
  LFunctionTrivChar N s =
    (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s

LFunctionTrivChar_residue_one :
  Tendsto (fun s => (s - 1) * LFunctionTrivChar N s) (𝓝[≠] 1)
    (𝓝 (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)))
```

These are at lines 174 and 182. At line 338, `LFunctionTrivChar₁ N` updates
`(s-1)L(s,1)` at `s=1` to its actual residue. Theorems
`LFunctionTrivChar₁_apply_one_ne_zero` and
`differentiable_LFunctionTrivChar₁` establish a nonzero value at one and an
entire regularization. Its negative logarithmic derivative is continuous
where the original function does not vanish, including at one
(`continuousOn_neg_logDeriv_LFunctionTrivChar₁`, line 369).

The exact induced-character identity
[LFunction_changeLevel](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L150)
is also already available. For positive M,N, `hMN : M ∣ N`, a character χ
modulo M, and `χ≠1 ∨ s≠1`, it gives

```text
LFunction (changeLevel hMN χ) s
 = LFunction χ s · ∏_{p∈N.primeFactors}(1−χ(p)p^(−s)).
```

The factors for primes dividing M equal one.
[LFunctionEulerCorrection.lean](../TwinPrime/Analytic/LFunctionEulerCorrection.lean)
now differentiates this actual identity for Re(s)>1 and bounds the norm of
the logarithmic-derivative correction by `log N`. Its primitive-inducing
specialization applies to every character of positive modulus, including
χ² when χ² is imprimitive or principal. Section 5 records the signs and
the exact range of this bound.

The root theorem `riemannZeta_ne_zero_of_one_le_re` includes `s=1` only
because the totalized value assigned there happens to be nonzero; its own
documentation explicitly calls that value a junk value. It is not evidence
that ζ is analytic at one. Any contour or boundary argument must retain the
regularization and the pole term, whose logarithmic derivative supplies the
linear main term.

For `[NeZero q]` and `a : ZMod q`, namespace
`ArithmeticFunction.vonMangoldt`,
[PrimesInAP.lean:282](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/PrimesInAP.lean#L282)
gives an exact character decomposition:

```lean
LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
  LSeries ↗(residueClass a) s =
    -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * (deriv (LFunction χ) s / LFunction χ s)
```

Here `residueClass a n` is `Λ(n)` in that residue class and zero otherwise.
The auxiliary function at line 304 satisfies the following exact statements:

```lean
continuousOn_LFunctionResidueClassAux :
  ContinuousOn (LFunctionResidueClassAux a) {s | 1 ≤ s.re}

eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
  Set.EqOn (LFunctionResidueClassAux a)
    (fun s => L ↗(residueClass a) s - (q.totient : ℂ)⁻¹ / (s - 1))
    {s | 1 < s.re}
```

They occur at lines 333 and 348. This is an available qualitative boundary
input for a future Tauberian argument. It is not a proved Tauberian conclusion.
The same file proves the fixed-modulus lower bound (line 392)

```lean
LSeries_residueClass_lower_bound (ha : IsUnit a) :
  ∃ C : ℝ, ∀ {x : ℝ}, x ∈ Set.Ioc 1 2 →
    (q.totient : ℝ)⁻¹ / (x - 1) - C ≤
      ∑' n, residueClass a n / (n : ℝ) ^ x
```

and `Nat.infinite_setOf_prime_and_eq_mod` (line 475) and
`Nat.forall_exists_prime_gt_and_modEq` (line 504). These prove infinitude,
not a prime-counting asymptotic or a uniform logarithmic error term. The
constant above may depend arbitrarily on `q` and `a`.

## 4. Integral and general complex-analysis APIs

[SumCoeff.lean:137](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/SumCoeff.lean#L137)
already proves the Abel integral identity

```lean
LSeries_eq_mul_integral (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
  {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s)
  (hO : (fun n => ∑ k ∈ Icc 1 n, f k) =O[atTop]
    (fun n => (n : ℝ) ^ r)) :
  LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ),
    (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))
```

Its `hS` is a summability hypothesis, not supplied by a bound on ordered
character partial sums in the conditionally convergent half-plane.
The theorem at line 336 has direction

```lean
LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div
  (hlim : Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, f k) / n) atTop (𝓝 l))
  (hfS : ∀ s : ℝ, 1 < s → LSeriesSummable f s) :
  Tendsto (fun s : ℝ => (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l)
```

Thus the summatory asymptotic implies the residue limit. Reversing this
implication would import precisely the missing Tauberian step. The
nonnegative variant at line 362 also assumes the summatory limit.

Useful quantitative general-purpose tools are present. For example,
[JensenFormula.lean:389](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/JensenFormula.lean#L389)
contains:

```lean
AnalyticOnNhd.sum_divisor_le {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ}
  (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M)
  (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|)) (h₂f : f c ≠ 0)
  (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
  ∑ᶠ u, divisor f (closedBall c |r|) u ≤
    Real.log (M / ‖f c‖) / Real.log (R / r)
```

[Complex.borelCaratheodory](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/BorelCaratheodory.lean#L109)
has signature, with implicit real `M,R` and complex `z`:

```lean
(hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
(hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M})
(hR : 0 < R) (hz : z ∈ ball 0 R) :
‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) +
  ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)
```

The repository now supplies explicit primitive L-function growth and a
center-value lower bound, and applies Jensen as described in Section 5.
It also constructs the normalized holomorphic logarithm of the quotient
after removing the actual local zeros and proves the quantitative
logarithmic-derivative remainder in Section 5. These are repository
theorems built from the pinned APIs, not additional assumptions.
The located Mathlib ζ-zero theorem
[IsCompact.inter_riemannZetaZeros_finite](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/ZetaZeros.lean#L64)
only says `(S ∩ riemannZetaZeros).Finite` for compact `S`; it does not give
a quantitative count as the height grows.

## 5. Proved truncation, growth, and local zero estimates

The repository now derives quantitative Dirichlet tails from its proved
Pólya–Vinogradov interval bound. The input theorem
[norm_sum_primitive_character_Ico_le](../TwinPrime/Analytic/CharacterInterval.lean#L148)
is:

```lean
{q : ℕ} (hq : 1 < q) (χ : DirichletCharacter ℂ q)
(hχ : χ.IsPrimitive) (M N : ℕ) :
‖∑ n ∈ Ico M N, χ (n : ZMod q)‖ ≤ Real.sqrt q * (1 + Real.log q)
```

Write `B(q)=sqrt(q)(1+log q)` and
`Sχ(s,N)=Σ_{1≤n≤N} n^(−s)χ(n)`. For primitive χ modulo q>1,
[CharacterDirichletTail.lean](../TwinPrime/Analytic/CharacterDirichletTail.lean)
proves, for natural `1≤M≤N` and `σ=Re(s)>0`,

```text
‖Σ_{M<n≤N} n^(−s)χ(n)‖
 ≤ B(q) M^(−σ) (1 + ‖s‖/σ).                             (FTχ)
```

`norm_cpow_neg_sub_le` first bounds the variation on positive real inputs:

```text
‖b^(−s) − a^(−s)‖ ≤ (‖s‖/σ)(a^(−σ) − b^(−σ)),  0<a≤b.
```

`norm_sum_Ioc_cpow_mul_le_of_partial_sums` combines this with finite Abel
summation anchored at M. The character specialization is
`norm_sum_primitive_character_dirichlet_Ioc_le`. Its interval PV input
bounds each sum over `(M,t]` directly, so no extra factor two is needed.
Equal endpoints are included; M=0 is excluded from this tail estimate.

The same module defines `characterDirichletPartialSum` and proves
`cauchySeq_characterDirichletPartialSum` and
`exists_characterDirichletPartialSum_limit`. Thus for each fixed s with
σ>0 there is an ordered limit Lχ(s), and for every natural M≥1,

```text
‖Lχ(s) − Sχ(s,M)‖ ≤ B(q) M^(−σ) (1 + ‖s‖/σ).             (OTχ)
```

This is ordered convergence, not absolute or unconditional summability.
For σ>1, `tendsto_characterDirichletPartialSum_LFunction` identifies the
partial-sum limit with Mathlib's `LFunction`; this absolutely convergent
identification applies to every positive modulus and character, including
conductor one, and removes the zero L-series term explicitly.

[CharacterDirichletContinuation.lean](../TwinPrime/Analytic/CharacterDirichletContinuation.lean)
now extends the primitive q>1 identification throughout σ>0. On every set
with `σ≥δ>0` and `‖s‖≤H`, it proves the common tail budget

```text
‖Lχ(s) − Sχ(s,M)‖ ≤ B(q) M^(−δ)(1+H/δ),  M≥1.
```

This gives uniform convergence on those sets and locally uniform
convergence on the positive half-plane. Every finite summand with n>0 is
entire in s, so the limit is holomorphic. The half-plane is connected;
analytic uniqueness identifies the limit with the existing nonprincipal
`LFunction`, using agreement in a neighborhood of s=2. The theorem
`norm_LFunction_sub_characterDirichletPartialSum_le_of_re_pos` proves,
for primitive q>1 and natural Y≥1,

```text
‖LFunction χ s − Σ_{1≤n≤Y} χ(n)n^(−s)‖
  ≤ B(q) Y^(−σ) (1 + ‖s‖/σ),  σ>0.                       (TRχ)
```

`tendstoLocallyUniformlyOn_characterDirichletPartialSum_LFunction` records
locally uniform convergence to the actual L-function. No continuation
hypothesis is added, and the argument assumes no distribution result.

An alternative exact integral representation remains a proposed lemma.
With `Aχ(u)=Σ_{1≤n≤floor(u)} χ(n)`, it is

```text
LFunction χ s − Σ_{1≤n≤Y} χ(n)n^(−s)
 = −Aχ(Y)Y^(−s) + s ∫_Y^∞ Aχ(u)u^(−s−1) du.              (ABELχ)
```

The integral converges absolutely for σ>0 because Aχ is bounded. One could
prove this identity first on σ>1, then continue its holomorphic right side.
The proved (FTχ), (OTχ), and full positive-half-plane (TRχ) do not assume
this integral representation. Mathlib's `LSeriesSummable` asserts unconditional
summability and cannot replace the ordered-limit construction for general
σ>0.

Conductor one is handled separately in
[ZetaTruncation.lean](../TwinPrime/Analytic/ZetaTruncation.lean).
For natural `1≤M≤N` and σ>0, integration of the proved complex-power
variation on each unit interval gives the sharp finite Euler estimate

```text
‖Σ_{M<n≤N} n^(−s) − ∫_M^N u^(−s) du‖
 ≤ (‖s‖/σ)(M^(−σ)−N^(−σ)).
```

When s≠1, the integral is evaluated exactly. Define

```text
Z(s,N)=Σ_{1≤n≤N} n^(−s)+N^(1−s)/(s−1).
```

The module proves Cauchy convergence of Z(s,N) and an ordered limit with
error at most `(‖s‖/σ)N^(−σ)` for σ>0, s≠1. For σ>1 it identifies that
limit with the actual zeta function. Equal finite endpoints are included;
the truncation endpoint must be positive.

[ZetaContinuation.lean](../TwinPrime/Analytic/ZetaContinuation.lean)
now proves the remaining identification on the entire positive half-plane
away from one. The approximants

```text
R(s,N)=(s−1)Σ_{1≤n≤N}n^(−s)+N^(1−s)
```

are entire for N≥1 and equal one at s=1. Their ordered limit has uniform
error at most `(H+1)(H/δ)N^(−δ)` when Re(s)≥δ>0 and ‖s‖≤H.
Locally uniform convergence makes the limit holomorphic on Re(s)>0;
analytic uniqueness identifies it with Mathlib's entire
`LFunctionTrivChar₁ 1`, using agreement near s=2. The regularized error is
bounded by `‖s−1‖(‖s‖/σ)N^(−σ)`, including the exact zero error at s=1.
Dividing away from one gives convergence of Z(s,N) to actual ζ(s).
Passing the original finite bound to that limit proves
`norm_riemannZeta_sub_sum_sub_pole_le_of_re_pos`:

```text
‖ζ(s) − Σ_{1≤n≤Y} n^(−s) − Y^(1−s)/(s−1)‖
 ≤ (‖s‖/σ)Y^(−σ),  Y≥1, σ>0, s≠1.                     (TRζ)
```

There is no extra factor involving `‖s−1‖` in this final error bound.
Neither the character nor the zeta continuation asserts absolute
summability of the underlying series in 0<σ≤1.

The exact fractional-part integral representation

```text
ζ(s) − Σ_{1≤n≤Y} n^(−s) − Y^(1−s)/(s−1)
 = −s ∫_Y^∞ (u−floor(u))u^(−s−1) du
```

is not used or claimed by the unit-interval proof. The explicit pole
correction is retained throughout; ζ's totalized value at one supplies no
analytic substitute for it.

[ZetaLogDerivative.lean](../TwinPrime/Analytic/ZetaLogDerivative.lean)
sets `Z=regularizedRiemannZeta` and proves the exact identity

```text
−ζ′(s)/ζ(s)=1/(s−1)−Z′(s)/Z(s),               s≠1, Z(s)≠0.
```

The cutoff-one estimate gives `‖Z(s)−s‖≤‖s−1‖‖s‖/Re(s)` on Re(s)>0.
Consequently `‖Z(s)‖≤H+(H+1)H/δ` on Re(s)≥δ>0, ‖s‖≤H;
Cauchy bounds for every iterated derivative are also proved. More locally,
`‖Z(s)−1‖≤2/3` and `‖Z(s)‖≥1/3` for `‖s−1‖≤1/4`, without assuming
nonvanishing. Cauchy's estimate then gives

```text
‖Z′(s)/Z(s)‖≤40                         when ‖s−1‖≤1/8,
‖−ζ′(s)/ζ(s)−1/(s−1)‖≤40               when 0<‖s−1‖≤1/8.
```

These local pole estimates supply the small-height case of the proved
all-height zeta region below.

[ZetaLocalExpansion.lean](../TwinPrime/Analytic/ZetaLocalExpansion.lean)
extends the needed one-sided pole estimate to every height. It applies the
actual-divisor expansion to the entire regularization Z, with center
`‖Z(2+it)‖≥1/4` and outer growth `4(‖2+it‖+2)²`. Qualitative zeta
nonvanishing and `Z(1)=1` put all its actual zeros in Re(s)<1. Define

```text
Kζ(t)=C_loc[1+log16+2log(‖2+it‖+2)].
```

For `1<σ≤9/8` and every real t it proves
`Re(−ζ′/ζ(σ+it))≤Re(1/(σ−1+it))+Kζ(t)`.
The budget is nonnegative and at most
`C_loc[1+log16+2log(|t|+4)]`. The principal pole is retained at every
height, rather than replaced by an assumed bound for an analytic function.

[LFunctionLowerBound.lean](../TwinPrime/Analytic/LFunctionLowerBound.lean)
proves for every character of positive modulus and every s with Re(s)≥2,

```text
‖LFunction χ s−1‖≤3/4,  1/4≤‖LFunction χ s‖,
‖(LFunction χ s)⁻¹‖≤4.
```

The proof isolates the coefficient n=1 and bounds the remaining series by
inverse squares. It includes principal characters and gives an absolute
lower bound at the centers used for Jensen; it is not a lower bound near
the line Re(s)=1.

[LFunctionGrowth.lean](../TwinPrime/Analytic/LFunctionGrowth.lean)
defines `G(q,δ,H)=1+B(q)(1+H/δ)`. Taking Y=1 in (TRχ) gives
`‖LFunction χ s‖≤G(q,δ,H)` for primitive q>1, Re(s)≥δ>0 and ‖s‖≤H.
On a closed disk of radius R<Re(s) centered at s, the common bound is
`G(q,Re(s)−R,‖s‖+R)`. Cauchy's inequalities then give, for R>0 and
every natural k,

```text
‖(LFunction χ)^(k)(s)‖
 ≤ k! G(q,Re(s)−R,‖s‖+R)/R^k.
```

These are explicit bounds for L and its derivatives. Dividing them by L
near a possible zero is not justified by the center-value lower bound.

[LFunctionZeroCount.lean](../TwinPrime/Analytic/LFunctionZeroCount.lean)
now applies Jensen to primitive χ of conductor q>1 at any center s with
Re(s)=2. It uses inner radius 5/4 and outer radius 3/2; the latter disk
lies in Re(z)≥1/2. The circle growth budget is bounded by
`4q²(‖s‖+2)`, and the center norm is at least 1/4. The theorem
`sum_divisor_LFunction_le_log_conductor_height` proves exactly

```text
Σ_{ρ∈closedBall(s,5/4)} ord_ρ L(·,χ)
 ≤ [log 16 + 2 log q + log(‖s‖+2)]/log(6/5).
```

The Lean left side is the finite-support sum of the analytic divisor,
valued in integers and then cast to reals. Since this primitive
nonprincipal L-function is entire and nonzero at the center, it counts
zeros with their multiplicity, including zeros on the inner boundary;
there are no pole contributions. This count supplies the multiplicity
budget for the proved local expansion below; it does not itself exclude
zeros or bound an exceptional zero.

[HolomorphicLog.lean](../TwinPrime/Analytic/HolomorphicLog.lean)
constructs a normalized holomorphic logarithm of a nonvanishing holomorphic
function on a disk.
[AnalyticLogDerivativeBound.lean](../TwinPrime/Analytic/AnalyticLogDerivativeBound.lean)
uses Borel–Carathéodory and Cauchy estimates to prove
`‖g′(z)/g(z)‖≤144(1+log(M/‖g(c)‖))` on `closedBall c 1` when g is
holomorphic, nonzero, and bounded by M on `ball c (5/4)`. The constant is
explicit: the normalized logarithm is bounded by `18(1+log(M/‖g(c)‖))`
at radius 9/8, and the Cauchy radius is 1/8.

Application to L-functions first removes the actual zeros.
[HolomorphicZeroRemoval.lean](../TwinPrime/Analytic/HolomorphicZeroRemoval.lean)
constructs the analytic quotient g and proves `f=P·g` at every point,
including the original zeros. Here P is the polynomial of the actual
divisor on the closed radius-5/4 disk, and g is nonzero on that disk.
[ZeroFactorBounds.lean](../TwinPrime/Analytic/ZeroFactorBounds.lean)
identifies its natural total multiplicity N with the integer divisor sum,
proves `‖P(c)‖≤(5/4)^N` and `‖P(w)‖≥(1/4)^N` on the outer radius-3/2
circle, and obtains `‖g‖≤M·4^N` on the outer disk and
`‖g(c)‖≥‖f(c)‖/(5/4)^N`. The normalized logarithmic budget therefore costs
at most `1+log(M/‖f(c)‖)+N log5`.
[ZeroFactorLogDerivative.lean](../TwinPrime/Analytic/ZeroFactorLogDerivative.lean)
proves the exact derivative identity for this factorization.

[LocalLogDerivativeExpansion.lean](../TwinPrime/Analytic/LocalLogDerivativeExpansion.lean)
combines these results with Jensen. Put

```text
C_loc=144(1+log5/log(6/5)),
S_f(c,z)=Σᶠρ divisor(f,closedBall(c,5/4))(ρ)/(z−ρ).
```

For f holomorphic near the outer closed disk, f(c)≠0, an outer-circle
bound M≥1, z in the closed unit disk, and f(z)≠0, the theorem proves
`‖f′(z)/f(z)−S_f(c,z)‖≤C_loc(1+log(M/‖f(c)‖))`.
The sum uses actual analytic multiplicities, including inner-boundary
zeros; no local-expansion hypothesis is introduced.
[LFunctionLocalExpansion.lean](../TwinPrime/Analytic/LFunctionLocalExpansion.lean)
specializes this with `M=4q²(‖c‖+2)` and the center lower bound. For
primitive χ modulo q>1, Re(c)=2, z∈closedBall(c,1), and L(z,χ)≠0,

```text
‖L′(z,χ)/L(z,χ)−Sχ(c,z)‖
 ≤ C_loc[1+log16+2log q+log(‖c‖+2)].
```

Here `Sχ=S_(L(·,χ))`. A companion theorem uses Mathlib's qualitative
nonvanishing on Re(z)≥1 to discharge the evaluation-point condition.

[LFunctionLogDerivative.lean](../TwinPrime/Analytic/LFunctionLogDerivative.lean)
proves the actual continuation identity `−L'/L=Σ Λ(n)χ(n)n^(−s)` on
Re(s)>1 for every positive modulus and character. It defines the real
nonnegative majorant `D(σ)=Σ Λ(n)n^(−σ)` and identifies it there with
`(−ζ'(σ)/ζ(σ)).re`. Thus `‖L'(s,χ)/L(s,χ)‖≤D(Re(s))`. It also proves
the derivative form of three-four-one positivity for σ>1 and real t:

```text
0 ≤ 3D(σ) + 4 Re(−L'/L(σ+it,χ))
                 + Re(−L'/L(σ+2it,χ²)).
```

The coefficient proof uses `3+4 Re(z)+Re(z²)≥0` for `‖z‖≤1`, with
`z=χ(n)n^(−it)`. Its first term is the full zeta series; at nonunits the
other two character terms vanish and the nonnegative `3Λ(n)n^(−σ)`
remains. No Euler-factor contribution is dropped, and no primitivity
hypothesis is needed for these logarithmic-derivative statements.

The imprimitive correction is now quantitative. For a character ψ modulo
positive d dividing q, define

```text
Eψ,q(s)=Σ_{p|q} ψ(p)log(p)p^(−s)/(1−ψ(p)p^(−s)).
```

`LFunctionEulerCorrection` proves `‖Eψ,q(s)‖≤log q` on Re(s)≥1, with
nonzero Euler denominators. For Re(s)>1 it proves
`L′/L(s,changeLevel ψ)=L′/L(s,ψ)+Eψ,q(s)`; the negative logarithmic
derivative has correction `−Eψ,q(s)`. The actual primitive-inducing
character can be substituted for ψ, so χ² need not be primitive. If the
inducing character is principal, its function is zeta at conductor one;
the pole term and the regularized remainder above remain present.

[LFunctionInducedBound.lean](../TwinPrime/Analytic/LFunctionInducedBound.lean)
combines the correction with the primitive estimate. For every
nonprincipal character η modulo q, including imprimitive η, it proves
`Re(−L′/L(σ+it,η))≤B(q,t)+log q` for `1<σ≤9/8`. For the principal
character the exact identity is `−L′/L=−ζ′/ζ−E`, and its real part is
at most `Re(−ζ′/ζ)+log q`. Thus the character-square cases below use
the actual inducing character and account for all missing Euler factors.

[LFunctionZeroSigns.lean](../TwinPrime/Analytic/LFunctionZeroSigns.lean)
proves that actual zeros of primitive χ modulo q>1 lie in Re(ρ)<1,
using the existing qualitative boundary nonvanishing theorem. Every
nonzero divisor multiplicity is positive, and every reciprocal-divisor
term has nonnegative real part when Re(z)>1. Thus `Re Sχ(c,z)≥0`.
An actual zero β+iγ with β≥3/4 has multiplicity at least one and lies in
the radius-5/4 disk centered at 2+iγ. For every σ>1 the selected term gives
`1/(σ−β)≤Re Sχ(2+iγ,σ+iγ)`. This is a proved lower bound from an actual
zero, not an abstract assumption about the zero sum.

[LFunctionZeroInequality.lean](../TwinPrime/Analytic/LFunctionZeroInequality.lean)
now combines the actual expansion with these signs. Define

```text
B(q,t)=C_loc[1+log16+2log q+log(‖2+it‖+2)].
```

This budget is nonnegative and increases with positive conductor. For
primitive χ modulo q>1 and `1<σ≤9/8`, the proved one-sided bounds are

```text
Re(−L′/L(σ+it,χ)) ≤ B(q,t)−Re Sχ(2+it,σ+it) ≤ B(q,t).
```

If β+it is an actual zero with β≥3/4, the stronger bound is

```text
Re(−L′/L(σ+it,χ)) ≤ B(q,t)−1/(σ−β).
```

Its reciprocal has coefficient one because the actual multiplicity is at
least one. No prescribed zero expansion or zero-sign hypothesis is assumed.

[ZeroFreeArithmetic.lean](../TwinPrime/Analytic/ZeroFreeArithmetic.lean)
proves the scalar contradiction: for E>0 and `0≤δ≤1/(20E)`, setting
`a=1/(4E)` makes `4/(a+δ)≤3/a+E` impossible. Indeed its left side is at
least `40E/3`, whereas the right side is `13E`. For E≥120 it also proves
`0<a≤1/8` and `0<1/(20E)≤1/4`, the ranges needed by the local estimates.
The corresponding actual-character applications are now proved.

[LFunctionNonquadraticZeroFree.lean](../TwinPrime/Analytic/LFunctionNonquadraticZeroFree.lean)
defines

```text
E_n(q,t)=120+4B(q,t)+B(q,2t)+log q.
```

For primitive χ modulo q>1 with `χ²≠1`, three-four-one and the induced
nonprincipal-square bound give `4/(σ−β)≤3/(σ−1)+E_n(q,t)` from an actual
zero β+it near one. The proved scalar contradiction then excludes every
zero with `β≥1−1/(20E_n(q,t))`, at every height.

[LFunctionQuadraticZeroFree.lean](../TwinPrime/Analytic/LFunctionQuadraticZeroFree.lean)
keeps the additional principal pole when `χ²=1`. Write

```text
E_q(q,t)=120+4B(q,t)+Kζ(2t)+log q.
```

For any larger budget `E≥E_q(q,t)`, it excludes zeros with
`β≥1−1/(40E)` and `|t|≥1/(4E)`. With `a=1/(4E)`, the doubled-height
pole has real part `a/(a²+4t²)≤1/(5a)`. The resulting scalar inequality
would have left side at least `160E/11` and right side `69E/5`, which is
impossible. The generalized larger-budget form permits the common
budget below; the small-height interval is handled separately.

[LFunctionConjugateZeros.lean](../TwinPrime/Analytic/LFunctionConjugateZeros.lean)
proves the actual L-function and derivative conjugation identities for
real characters, and bounds two distinct actual reciprocal-zero terms
together by the full zero sum. No symmetry of multiplicities is assumed.
[LFunctionNearOneZeros.lean](../TwinPrime/Analytic/LFunctionNearOneZeros.lean)
sets `E₀(q)=40+B(q,0)`, `a=1/(4E₀(q))`, and `ε=1/(16E₀(q))`.
For each fixed primitive χ modulo q>1, its actual zero sum at the real
point `1+a` is at most `5E₀`. Each zero in the rectangle
`Re(ρ)≥1−ε`, `|Im(ρ)|≤ε` contributes at least `3E₀`, multiplied by its
actual positive integer multiplicity. Consequently there is at most one
such zero, and its actual divisor multiplicity and meromorphic order
both equal one. For `χ²=1`, conjugation forces this zero to be real.

[LFunctionZeroFreeRegion.lean](../TwinPrime/Analytic/LFunctionZeroFreeRegion.lean)
combines all character and height cases using

```text
R(q,t)=E_n(q,t)+E_q(q,t)+4E₀(q),
w(q,t)=1/(40R(q,t)).
```

For any actual zero β+it of a primitive χ modulo q>1 with
`β≥1−w(q,t)`, it proves `χ²=1`, `t=0`, and
`meromorphicOrderAt (LFunction χ) β=1`. There is at most one zero in this
region for the fixed χ, even when two candidate points use different
height budgets. The comparison `R≥4E₀` puts the remaining small-height
case inside the proved rectangle. This is a complete per-character
exception statement for the explicit region. It does not give a lower
bound for `1−β`, nor a Page theorem comparing distinct characters.

[ZeroFreeLogarithms.lean](../TwinPrime/Analytic/ZeroFreeLogarithms.lean)
proves an explicit logarithmic comparison for this actual budget:

```text
R(q,t) ≤ 100C_loc[1+log q+log(|t|+4)].
```

Thus the narrower region with width
`1/[4000C_loc(1+log q+log(|t|+4))]` retains the same real, quadratic,
simple, and per-character-unique exception conclusion. This is a proved
uniform conductor/height bound, not asymptotic notation concealing a
character-dependent constant.

[ZetaZeroFree.lean](../TwinPrime/Analytic/ZetaZeroFree.lean)
proves an all-height region without an exception for the entire
regularization Z. Put

```text
Eζ(t)=120+4Kζ(t)+Kζ(2t).
```

Then `Z(β+it)≠0` whenever `β≥1−1/(80Eζ(t))`. The same condition excludes
zeros of the actual ζ function away from its pole at one. The proof uses
the actual Z-divisor and retains both height-dependent pole terms in
three-four-one. Small heights `|t|≤1/8` lie in the already proved
nonvanishing disk about one. At larger heights, with `a=1/(4Eζ(t))`,
both relevant pole real parts are at most `1/(17a)`; the scalar
contradiction compares `320Eζ/21` with `241Eζ/17`. The value `Z(1)=1`
is retained; ζ's assigned value at its pole is not used as an analytic
nonvanishing argument.

`ZeroFreeLogarithms.lean` also proves
`Eζ(t)≤100C_loc[1+log(|t|+4)]`. Hence Z has no zero in the narrower
region of width `1/[8000C_loc(1+log(|t|+4))]`. The actual-zeta corollary
explicitly assumes `β+it≠1`. Both this height comparison and the primitive
conductor/height comparison above are checked inequalities with absolute
constants.

### Ordered convolution limits and an explicit four-factor main term

The declarations in this subsection have passed standalone Lean checks;
the checkpoint's full-project build and axiom audit are recorded separately.
All character factors below have one common positive modulus q. They may
be imprimitive. Multiplication of arithmetic functions means Dirichlet
convolution, and all summatory functions use the exact natural floor:
`A_f(x)=Σ_{1≤n≤floor(x)} f(n)`.

[CharacterPeriodSum.lean](../TwinPrime/Analytic/CharacterPeriodSum.lean#L55)
proves, for every nonprincipal χ, the exact initial-sum identity
`Σ_{1≤n≤N}χ(n)=Σ_{1≤n≤N mod q}χ(n)`. Consequently its norm is at most
`N mod q`, and hence at most q; the elementary bound by N also holds for
principal characters. The general interval bound is `2q`. These results
include N=0 and empty intervals and use complete-period cancellation,
without a primitive-character or prime-distribution assumption.

For `a_j=toArithmeticFunction(χ_j)` and three nonprincipal factors, the
exact hyperbola identity in
[CharacterConvolutionCancellation.lean](../TwinPrime/Analytic/CharacterConvolutionCancellation.lean#L37)
gives, for every real x≥1,

```text
‖A_(a₁*a₂)(x)‖ ≤ 3q√x,
‖A_(a₁*a₂*a₃)(x)‖ ≤ 10q² x^(2/3)(1+log x).
```

[CharacterConvolutionPower.lean](../TwinPrime/Analytic/CharacterConvolutionPower.lean#L33)
uses `1+log x≤13x^(1/12)` to obtain `130q²x^(3/4)`, and proves the
corresponding coefficient-prefix inequality for every natural N, including
zero. Independently,
[CharacterConvolutionMass.lean](../TwinPrime/Analytic/CharacterConvolutionMass.lean)
bounds the absolute mass of the triple convolution by `x(1+log x)²`.
This mass estimate does not require the factors to be nonprincipal.

[PowerDirichletTail.lean](../TwinPrime/Analytic/PowerDirichletTail.lean)
and [PowerDirichletContinuation.lean](../TwinPrime/Analytic/PowerDirichletContinuation.lean)
prove the general ordered continuation from an actual prefix bound
`‖Σ_{n≤N}a(n)‖≤C N^α`, for α,C≥0. On Re(s)>α the error after M≥1 is
`2C M^(α−Re(s))(1+‖s‖/(Re(s)−α))`; the convergence is locally uniform
and the limit is holomorphic. These are proved conclusions from the
prefix bound, not additional convergence assumptions.

[CharacterConvolutionContinuation.lean](../TwinPrime/Analytic/CharacterConvolutionContinuation.lean#L95)
discharges that prefix bound for `f=a₁*a₂*a₃`. Its absolute-convergence
identity on Re(s)>1 and analytic uniqueness then identify the ordered
limit on Re(s)>3/4 with `Lχ₁(s)Lχ₂(s)Lχ₃(s)`. In particular,

```text
Σ_{1≤n≤M} f(n)/n → R = Lχ₁(1)Lχ₂(1)Lχ₃(1),
‖R−Σ_{1≤n≤M} f(n)/n‖ ≤ 1300q² M^(−1/4),  M≥1.
```

All three nonprincipal hypotheses are retained, so the product is
holomorphic at one. Absolute summability of this reciprocal series is
not asserted. The coefficient at n=0 is excluded explicitly.

For a general f with `‖A_f(x)‖≤C x^(3/4)` and absolute mass at most
`x(1+log x)²`,
[ZetaConvolutionAsymptotic.lean](../TwinPrime/Analytic/ZetaConvolutionAsymptotic.lean#L69)
proves an error `(1+25C)x^(4/5)(1+log x)²` about the actual ordered
reciprocal limit. The real cutoffs are `y=x^(4/5)` and `z=x^(1/5)`,
with yz=x. The finite error consists of the head mass, a strip bounded
by `4Cy`, an overlap bounded by `Cy`, and a reciprocal-tail term bounded
by `20Cy`. The last bound includes the factor two from flooring y.
Every cutoff remains in the range ≥1, including x=1.

The actual specialization in
[CharacterConvolutionAsymptotic.lean](../TwinPrime/Analytic/CharacterConvolutionAsymptotic.lean#L22)
discharges both generic bounds and identifies the main coefficient:

```text
‖A_(ζ*a₁*a₂*a₃)(x) − x Lχ₁(1)Lχ₂(1)Lχ₃(1)‖
 ≤ (1+3250q²)x^(4/5)(1+log x)²,  x≥1.
```

Here ζ denotes the arithmetic zeta coefficient function. For distinct
nonprincipal quadratic χ₁,χ₂, take χ₃=χ₁χ₂. The same theorem then applies
to `quadraticProductCoefficients`, with main coefficient equal to the
actual value `regularizedQuadraticLFunctionProduct χ₁ χ₂ 1`. This is the
regularized residue, with the zeta pole retained. If a character factor
is principal, these hypotheses fail and no single-residue formula is
claimed. The modulus in the error is the common level q.

This summatory error is now used in the centered continuation and residue
comparison below. No inversion for a von Mangoldt sum, independent ψ
estimate, or distribution theorem is deduced by these convolution results.

### Centered residue comparison and the uniform Siegel value theorem

The final theorem in
[SiegelValue.lean](../TwinPrime/Analytic/SiegelValue.lean#L23)
has passed standalone Lean checking with no warnings. It proves

```text
∀ ε>0, ∃ c>0, ∀ q>1, ∀ primitive χ modulo q,
  χ²=1 → c q^(−ε) ≤ ‖Lχ(1)‖.
```

The constant precedes the conductor and character quantifiers. No value
bound, zero-gap estimate, distribution theorem, or Siegel–Walfisz
hypothesis is supplied. The choice argument makes no effectiveness claim.
Full-project verification is recorded in the checkpoint ledger separately.

Write F(s)=ζ(s)Lχ₁(s)Lχ₂(s)L(χ₁χ₂)(s) and
λ=Lχ₁(1)Lχ₂(1)L(χ₁χ₂)(1). All three character factors must be
nonprincipal. In
[QuadraticCenteredFunction.lean](../TwinPrime/Analytic/QuadraticCenteredFunction.lean),
the difference of the entire regularizations, `Freg−λZ`, vanishes at one.
Its `dslope` quotient H is entire and equals `F−λζ` away from one.
[QuadraticCenteredCoefficients.lean](../TwinPrime/Analytic/QuadraticCenteredCoefficients.lean)
subtracts λ from every positive-index coefficient and proves

```text
‖Σ_{1≤n≤N}(c(n)−λ)‖ ≤ 441(1+3250q²)N^(9/10),  N≥0.
```

[QuadraticCenteredContinuation.lean](../TwinPrime/Analytic/QuadraticCenteredContinuation.lean)
identifies the actual ordered series with H on Re(s)>9/10, using
absolute convergence only on Re(s)>1 and analytic uniqueness. For
19/20≤β≤1 and M≥1 the centered tail is at most
`18522(1+3250q²)M^(−1/20)`. The value at one is the removable value;
no substitution of the undefined pole expression is made there.

[QuadraticResidueComparison.lean](../TwinPrime/Analytic/QuadraticResidueComparison.lean)
combines this actual tail, the positive finite coefficient sum, and the
proved zeta truncation. If 19/20≤β<1 and Re F(β)≤0, put δ=1−β>0.
A tail at most 1/2 gives `δ/(4M^δ)≤‖λ‖`. The checked cutoff is
`M=ceil((37044(1+3250q²))^20)`. The ceiling and conductor bounds in
[ResidueCutoff.lean](../TwinPrime/Analytic/ResidueCutoff.lean)
and [ResidueConductorBound.lean](../TwinPrime/Analytic/ResidueConductorBound.lean)
give, with the absolute constant `A=2(37044·3251)^20`,

```text
δ/(4 A^δ q^(40δ)) ≤ ‖λ‖.
```

An actual auxiliary zero implies Re F(β)=0, but the nonpositive form
also supports the branch in which no nearby primitive quadratic zero
exists. This distinction is essential to the final dichotomy.

[CharacterCommonLevel.lean](../TwinPrime/Analytic/CharacterCommonLevel.lean)
induces primitive characters of distinct conductors q₀ and q to Q=q₀q.
Their conductors are preserved, so both induced characters and their
quadratic product are nonprincipal. The product need not be primitive.
[LFunctionInducedValue.lean](../TwinPrime/Analytic/LFunctionInducedValue.lean)
bounds the Euler multiplier at one by `1+log Q`: expanding ∏(1+1/p)
over prime subsets injects their products into the harmonic sum through Q.
The Euler multiplier is nonzero on Re(s)>0. Together with the proved
nonprincipal bound `‖Lη(1)‖≤5+log Q` in
[LFunctionPeriodBound.lean](../TwinPrime/Analytic/LFunctionPeriodBound.lean),
[QuadraticAuxiliaryComparison.lean](../TwinPrime/Analytic/QuadraticAuxiliaryComparison.lean)
proves

```text
‖λ_Q‖ ≤ 5‖Lχ₀(1)‖‖Lχ(1)‖(1+log Q)^3,
δ/[20‖Lχ₀(1)‖ A^δ Q^(40δ)(1+log Q)^3] ≤ ‖Lχ(1)‖.
```

The second statement uses the actual nonpositive-product condition.
[SiegelValuePower.lean](../TwinPrime/Analytic/SiegelValuePower.lean)
absorbs the logarithms for δ≤ε/80. With
`k=δ/[20‖Lχ₀(1)‖A^δ(1+6/ε)^3]>0`, the displayed lower bound
dominates `k Q^(−ε)`.
[SiegelValueFromComparison.lean](../TwinPrime/Analytic/SiegelValueFromComparison.lean)
takes the minimum of a finite-conductor positive bound and
`k q₀^(−ε)`. Thus every q≤q₀, including all characters at q=q₀,
is covered, and the common-level factor q₀ is retained for larger q.

The final theorem chooses δ₀=min(1/20,ε/80) and splits on the existence
of any primitive quadratic zero in [1−δ₀,1). If one exists, its character
and zero are fixed before the target conductor is quantified; exact
induction preserves the product zero. Otherwise,
[QuadraticAuxiliaryCharacter.lean](../TwinPrime/Analytic/QuadraticAuxiliaryCharacter.lean)
supplies the actual primitive quadratic character of conductor four.
[QuadraticNoZeroTransport.lean](../TwinPrime/Analytic/QuadraticNoZeroTransport.lean)
transfers the global primitive exclusion to all three nonprincipal
factors, including an imprimitive product. The reality and continuity
argument in [LFunctionRealSign.lean](../TwinPrime/Analytic/LFunctionRealSign.lean)
then gives positive L-values and negative Re ζ at β=1−δ₀, hence
Re F(β)<0. This discharges the comparison hypothesis in both branches.
The argument never infers a zero from a small value at one.

The standalone-checked wrapper in
[SiegelZeroGapUnconditional.lean](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean)
composes the value theorem with the checked conversion in
[SiegelZeroGap.lean](../TwinPrime/Analytic/SiegelZeroGap.lean):
for each ε>0, one d>0 bounds every actual primitive zero in the proved
logarithmic region by `d q^(−ε)≤1−β`, with χ²=1 and t=0. This scope
does not assert uniqueness across different characters or a prime-sum
estimate. Both the general statement and its real-zero specialization
passed with no warnings; neither retains a supplied value-bound hypothesis.

## 6. Completed analytic assembly

The final analytic steps are proved in the modules listed below. They use
the independent L-function and contour arguments in addition to the finite
Vaughan and character large-sieve theorems.

The independent uniform Siegel value estimate and the actual residue
comparison are now established as in Section 5. A Page-type uniqueness
theorem across different characters remains unproved and is not used by
that argument. The former distribution obligations are now discharged:

1. **Uniform asymptotic absorption.** [ContourBudgetAbsorption.lean](../TwinPrime/Analytic/ContourBudgetAbsorption.lean)
   uses c=1+1/log x and H=(log x)^(A+2). All three errors are at most
   a constant times x/(log x)^A at a threshold uniform over conductors.
2. **Independent principal estimate.** [PrincipalMellinInversion.lean](../TwinPrime/Analytic/PrincipalMellinInversion.lean)
   and [SmoothedPrincipalContour.lean](../TwinPrime/Analytic/SmoothedPrincipalContour.lean)
   prove the actual regularized contour and its principal main term.
   The constant pole correction and the common-width comparison are
   retained. This argument does not use a BV-dependent ψ estimate.
3. **Uniform pointwise Siegel–Walfisz.** [SmoothedSiegelWalfisz.lean](../TwinPrime/Analytic/SmoothedSiegelWalfisz.lean)
   supplies the centered smoothed estimate with uniform constants.
   [CenteredUnsmoothing.lean](../TwinPrime/Analytic/CenteredUnsmoothing.lean)
   applies the exact finite difference with h=x/(log x)^(A+2) to smoothed
   exponent 2A+4. [SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean)
   proves the common threshold at x and x+h and the exact natural-endpoint
   `PointwiseSiegelWalfisz` proposition, including conductor one.

An independently proved Wiener–Ikehara theorem could turn Section 3's
boundary regularity into a fixed-modulus PNT. That would be real progress,
but it would provide neither the arbitrary logarithmic error saving nor the
growing-conductor uniformity required here.

### 6.1. Checked smoothed Mellin inversion and contours

The earlier source-audited proposal is now implemented in the
[Mellin contour route](MELLIN_CONTOUR_ROUTE.md). The ramp transform and
its actual inverse, the justified Dirichlet-series interchange, and the
actual Mangoldt-character identity are proved, including conductor one.
The principal pole kernel has exact inverse `(x−1)^2/(2x)`.

Widened local expansions reach radius 17/16 with constant 288. The
actual zero-free rectangles, local-zero separation, Jensen counts, and
full complex norm bounds now check left of one. The uniform evaluation
width for q≤(log x)^B and H=(log x)^K is at least
`k(log x)^(−1/2)`, and the primitive norm budget is at most `C log x`.

Finite rectangle shifts, both truncation tails, and the exact finite
unsmoothing bound also check. Their primitive-character specialization
proves an actual smoothed contour estimate with no supplied value,
zero-free, inversion, or distribution premise. The previous radius
limitation is therefore resolved.

Quantitative asymptotic absorption, the principal contour assembly, and
the exact centered sharp-sum SW theorem are now proved as in Section 6.
The existing pointwise-to-maximal and SW-to-BV implications are applied
without modification by [ClassicalDistribution.lean](../TwinPrime/Analytic/ClassicalDistribution.lean).
The independent signed B* problem remains unresolved.

## 7. Proved pointwise-to-maximal conversion

[SiegelWalfiszMaximal.lean](../TwinPrime/Analytic/SiegelWalfiszMaximal.lean)
proves `PointwiseSiegelWalfisz.maximal`. The pointwise hypothesis has
constants and a threshold depending only on its two logarithmic exponents,
uniformly in the character and modulus. For fixed A,B>0, the proof splits
natural `0≤t≤T` at `H=T/(log T)^(A+2)`.

For `t≤H`, use the elementary bound

```text
‖centeredCharacterPsi t χ‖ ≤ t log t + t
 ≤ T (log T + 1)/(log T)^(A+2)
 ≤ 2 T/(log T)^A
```

for sufficiently large T. `norm_centeredCharacterPsi_le_trivial` proves
the first inequality for every character and natural endpoint, including
the principal case. At t=0 both terms vanish, and t=1 is included. No
distribution estimate is used for these short endpoints.

For t>H, the formal proof uses the eventual comparison
`(log T)^(A+2)≤sqrt T`, proved from logarithmic-versus-power growth.
It follows that `H≥sqrt T` and `log t≥(1/2)log T`. Choosing T at least
the square of the pointwise threshold ensures that every such t exceeds
that threshold. Also, eventually

```text
r ≤ (log T)^B ≤ (log t)^(B+1).
```

Indeed the middle comparison follows from `log t≥(log T)/2` once
`log T≥2^(B+1)`. Apply the pointwise theorem with conductor exponent `B+1`
and error exponent `A`. This gives
`C t/(log t)^A ≤ C 2^A T/(log T)^A`, uniformly for every remaining `t`.
Taking the finite maximum now costs only the constant `max(2,C 2^A)`.

All these comparisons and the finite maximum are now formalized. The
threshold remains uniform over the growing conductor family. The proof
uses the enlarged exponent B+1 explicitly; it does not apply a pointwise
theorem at t using only the conductor condition stated at T.

## 8. Proved Siegel–Walfisz-to-BV implication

[BombieriVinogradovFromSW.lean](../TwinPrime/Analytic/BombieriVinogradovFromSW.lean)
proves

```lean
MaximalSiegelWalfisz.bombieriVinogradov
  (hSW : MaximalSiegelWalfisz) : MaximalBombieriVinogradov

PointwiseSiegelWalfisz.bombieriVinogradov
  (hSW : PointwiseSiegelWalfisz) : MaximalBombieriVinogradov
```

For the requested BV saving A>0, the proof takes modulus exponent A+9 and
small-conductor cutoff `ceil((log X)^(A+9))`. It uses maximal SW with
error exponent `2A+12` and conductor exponent `A+10` at the exact endpoint
T=2X+2. `BVSmallConductorGrowth.lean` bounds that cutoff and its uniform
small-conductor budget. `BVConductorGrowth.lean` absorbs the actual proved
large-conductor budget, with an eventual threshold uniform in both cutoff
and modulus limit. The existing replacement-error estimate is included.

The all-Q finite split handles Q below the conductor cutoff, including Q=0.
The final theorem supplies positive constants and a natural threshold,
uniformly for every admissible Q and every sufficiently large X, exactly
as quantified by `MaximalBombieriVinogradov`. The second implication
composes the first with the proved maximalization in Section 7. No final
endpoint, logarithmic absorption, or asymptotic quantifier gap remains in
either implication.

These results preserve the independent analytic obligation: neither
`PointwiseSiegelWalfisz` nor `MaximalSiegelWalfisz` has been proved without
a distribution hypothesis. The independent SW proof uses its own principal
contour, without the BV-dependent ψ estimates. Uniform asymptotic assembly
and the independent principal estimate are now proved as in Section 6.
The local logarithmic-derivative expansion over the actual zeros, its
explicit conductor/height remainder, the inducing Euler correction, and
the stated local zeta-pole bounds are already proved. So are the one-sided
selected-zero bounds and the scalar contradiction with admissible
parameters. Their actual nonquadratic and quadratic applications and the
combined primitive region are proved, with at most one real simple zero
per character. The regularized zeta region has no exception. These
zero-free results are now accompanied by the centered residue comparison
and the uniform Siegel value lower bound. Actual smoothed inversion and
finite contour estimates are now also proved as in Section 6.1. Their
asymptotic assembly and the centered sharp-sum theorem are complete. The full
twin-prime proof retains the independent B* problem.
