# From local L-function bounds to a quantitative zero-free region

This records the proved primitive L-function zero-free region, its possible
real simple exception for each character, the independent zeta zero-free
region, and the remaining Siegel–Walfisz obligations. Local API links refer to the Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997` pinned in
[lake-manifest.json](../lake-manifest.json). The independent centered
`PointwiseSiegelWalfisz` statement and the signed bilinear input `(B*)` remain
unproved. Their conditional route to twin primes is unchanged.

## 1. Proved inputs

- [CharacterDirichletContinuation](../TwinPrime/Analytic/CharacterDirichletContinuation.lean)
  identifies the locally uniform ordered character sums with the actual
  `LFunction` throughout `Re(s)>0`. For primitive `χ` modulo `q>1`, `M≥1`, and
  `σ=Re(s)>0`, the truncation error is at most
  `sqrt(q)(1+log q) M^(−σ)(1+‖s‖/σ)`.
- [ZetaContinuation](../TwinPrime/Analytic/ZetaContinuation.lean) proves, for
  `σ>0` and `s≠1`,
  `‖ζ(s)−Σ_{n≤M}n^(−s)−M^(1−s)/(s−1)‖ ≤ (‖s‖/σ)M^(−σ)`.
  Its locally uniform regularized sums converge to the entire function
  `Z(s)=(s−1)ζ(s)`, with the regularized value `Z(1)=1`. The regularized error
  estimate includes `s=1`. Neither continuation asserts absolute summability
  of the original series in `0<σ≤1`.
- [LFunctionGrowth](../TwinPrime/Analytic/LFunctionGrowth.lean) bounds primitive
  `q>1` functions on `σ≥δ>0`, `‖s‖≤H` by
  `G(q,δ,H)=1+sqrt(q)(1+log q)(1+H/δ)`, and proves Cauchy bounds for all
  iterated derivatives. [LFunctionLowerBound](../TwinPrime/Analytic/LFunctionLowerBound.lean)
  gives `‖Lχ(c)‖≥1/4` for `Re(c)≥2`, for every positive modulus and character.
- [LFunctionZeroCount](../TwinPrime/Analytic/LFunctionZeroCount.lean), theorem
  `sum_divisor_LFunction_le_log_conductor_height`, proves for primitive `q>1`
  and `Re(c)=2` that the number `Nχ(c)` of zeros in the closed disk of radius
  `5/4`, counted with their actual analytic multiplicities, satisfies

  ```text
  Nχ(c) ≤ [log 16 + 2 log q + log(‖c‖+2)] / log(6/5).
  ```

  This uses the outer radius `3/2`, the bound `4q²(‖c‖+2)`, the center lower
  bound, and Mathlib's `AnalyticOnNhd.sum_divisor_le` in
  [JensenFormula](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/JensenFormula.lean).
  The divisor is integer-valued and has finite support; holomorphy excludes
  poles and the nonzero center excludes an identically zero function.
- [LFunctionLogDerivative](../TwinPrime/Analytic/LFunctionLogDerivative.lean)
  proves the actual identity `−Lχ′/Lχ = Σ χ(n)Λ(n)n^(−s)` for `Re(s)>1`, its
  norm majorant `Re(−ζ′/ζ(σ))`, and

  ```text
  0 ≤ 3 Re(−ζ′/ζ(σ)) + 4 Re(−Lχ′/Lχ(σ+it))
        + Re(−Lχ²′/Lχ²(σ+2it)),                 σ>1.
  ```

  These results allow every character and positive modulus, including `q=1`.
  The first term is the full zeta function. Nonunits contribute the
  nonnegative term `3Λ(n)n^(−σ)`; no primitivity of `χ²` is used.

## 2. Proved normalized holomorphic logarithm

Let `g` be holomorphic and
nowhere zero on `B(c,5/4)`, and suppose `‖g(w)‖≤M` there. Put
`H=1+log(M/‖g(c)‖)`, so `H≥1`.
[HolomorphicLog](../TwinPrime/Analytic/HolomorphicLog.lean), theorem
`exists_normalized_holomorphic_log_on_ball`, constructs a holomorphic `h`
on any positive-radius ball with `h(c)=0`, `exp(h)=g/g(c)`, and `h′=g′/g`.
[AnalyticLogDerivativeBound](../TwinPrime/Analytic/AnalyticLogDerivativeBound.lean),
theorem `norm_logDerivative_le_of_nonvanishing_on_ball`, proves

```text
‖g′(z)/g(z)‖ ≤ 144 H                      when ‖z−c‖≤1.
```

The radius arithmetic is explicit. `Re(h)≤H`; translated
`Complex.borelCaratheodory_zero` from
[BorelCaratheodory](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/BorelCaratheodory.lean)
gives `‖h(w)‖≤2H(9/8)/(5/4−9/8)=18H` for `‖w−c‖≤9/8`.
For `‖z−c‖≤1`, its surrounding closed disk of radius `1/8` lies in that disk.
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` from
[Liouville](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/Liouville.lean)
then gives `18H/(1/8)=144H`.

The construction applies `DifferentiableOn.isExactOn_ball` to `g′/g` and
normalizes its primitive with `Complex.IsExactOn.with_val_at`, both in
[HasPrimitives](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Complex/HasPrimitives.lean).
The derivative of `g exp(−h)` is zero; constancy on the ball gives the
normalized exponential identity. Thus the logarithm is holomorphic and its
derivative identity is proved, rather than supplied as another hypothesis.

## 3. Proved expansion over the actual zeros

For `f` holomorphic near the closed disk
`B̄(c,3/2)`, `f(c)≠0`, and an outer-circle bound `M≥1`, let `D(ρ)` be its
zero multiplicities in `B̄(c,5/4)`.
[LocalLogDerivativeExpansion](../TwinPrime/Analytic/LocalLogDerivativeExpansion.lean),
theorem `norm_logDeriv_sub_zero_sum_le`, proves for `‖z−c‖≤1` and `f(z)≠0`,

```text
f′(z)/f(z) = Σρ D(ρ)/(z−ρ) + E(z),
‖E(z)‖ ≤ C [1+log(M/‖f(c)‖)],
```

with the explicit absolute constant `C=144(1+log 5/log(6/5))`. The sum uses
the actual integer-valued analytic divisor, with finite support and
nonnegative multiplicities. No zero-expansion hypothesis is assumed.

[HolomorphicZeroRemoval](../TwinPrime/Analytic/HolomorphicZeroRemoval.lean)
constructs the removable extension `g=f/P` for
`P(z)=∏ρ(z−ρ)^D(ρ)`, with exact equality `f=P g` at every point, including
the removed zeros. It proves `g` holomorphic on a neighborhood of the outer
closed disk and nonzero throughout the inner closed disk.
[ZeroFactorBounds](../TwinPrime/Analytic/ZeroFactorBounds.lean) identifies
`N=Σρ D(ρ)` with the natural multiplicity sum. The outer-circle distance
`‖z−ρ‖≥1/4` gives `‖P(z)‖≥(1/4)^N`. Maximum modulus then gives
`‖g‖≤M·4^N` on the outer disk, while
`‖g(c)‖≥‖f(c)‖/(5/4)^N`. Thus its normalized logarithmic budget is at most
`1+log(M/‖f(c)‖)+N log 5`. Jensen gives
`N≤log(M/‖f(c)‖)/log(6/5)`, and the proved bound in section 2 yields `C`.

[ZeroFactorLogDerivative](../TwinPrime/Analytic/ZeroFactorLogDerivative.lean)
proves `P′/P=Σρ D(ρ)/(z−ρ)` whenever `P(z)≠0`.
Its `logDeriv_eq_zeroFactor_sum_add` applies to the same quotient used in
the boundary estimates, so the error is exactly `g′/g`. The finite-product
formula also holds for any finitely supported integer exponent function at
a nonzero value; the analytic application supplies nonnegative exponents.

The actual primitive L-function specialization is now proved in
[LFunctionLocalExpansion](../TwinPrime/Analytic/LFunctionLocalExpansion.lean).
For primitive `χ` modulo `q>1`, `Re(c)=2`, and `z∈B̄(c,1)` with `Lχ(z)≠0`,
it proves

```text
‖Lχ′/Lχ(z)−Σρ Dχ,c(ρ)/(z−ρ)‖
 ≤ C [1+log 16+2log q+log(‖c‖+2)].
```

The outer growth bound is `M=4q²(‖c‖+2)` and `‖Lχ(c)‖≥1/4`. Its second
public theorem discharges `Lχ(z)≠0` on `Re(z)≥1` using Mathlib's qualitative
nonvanishing result. This does not assert a quantitative zero-free strip.

[LFunctionZeroSigns](../TwinPrime/Analytic/LFunctionZeroSigns.lean) proves
that every point in this actual divisor's support has real part `<1`.
Actual zeros have integer multiplicity at least one, and every reciprocal
term has nonnegative real part when `Re(z)>1`. In particular, for an actual
zero `β+iγ`, `β≥3/4`, and `σ>1`, it proves

```text
1/(σ−β) ≤ Re Σρ Dχ,2+iγ(ρ)/(σ+iγ−ρ).
```

The selected-zero statement has no upper restriction on `σ`; use of the
local expansion additionally requires its closed-unit-disk condition.

[LFunctionZeroInequality](../TwinPrime/Analytic/LFunctionZeroInequality.lean)
combines the expansion with these signs. Its `primitiveLFunctionLogBudget`
is the explicit `K(q,t)` defined in section 5, and is proved nonnegative and
monotone in positive conductor. For primitive `q>1` and `1<σ≤9/8`, it proves

```text
Re(−Lχ′/Lχ(σ+it)) ≤ K(q,t)−Re Σρ Dχ,2+it(ρ)/(σ+it−ρ)
                 ≤ K(q,t).
```

If `β+it` is an actual zero with `β≥3/4`, the checked selected-zero form is

```text
Re(−Lχ′/Lχ(σ+it)) ≤ K(q,t)−1/(σ−β).
```

These one-sided formulas are unconditional analytic estimates. Sections 5–8
describe their checked application to zero exclusion and the possible exception.

## 4. Inducing `χ²` and retaining the principal pole

Put `η=χ²` modulo `q` and `ψ=η.primitiveCharacter`, of conductor
`d|q`. The conductor, positivity, primitivity, and induction identities are
`conductor_dvd_level`, `conductor_ne_zero`, `primitiveCharacter_isPrimitive`,
and `changeLevel_primitiveCharacter` in
[DirichletCharacter.Basic](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/DirichletCharacter/Basic.lean).
`DirichletCharacter.LFunction_changeLevel` in
[DirichletContinuation](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean)
gives `Lη(s)=Lψ(s)∏_{p|q}(1−ψ(p)p^(−s))`, assuming `ψ≠1` or `s≠1`.
Factors at primes dividing `d` are one.
[LFunctionEulerCorrection](../TwinPrime/Analytic/LFunctionEulerCorrection.lean)
now proves for `σ>1` the exact differentiated identity and norm bound

```text
Lη′/Lη(s) = Lψ′/Lψ(s) + Σ_{p|q} ψ(p)log(p)p^(−s)/(1−ψ(p)p^(−s)),
‖correction‖ ≤ Σ_{p|q} log(p) ≤ log q.
```

The bound follows from `‖ψ(p)p^(−s)‖≤1/2`, and the Euler denominators are
proved nonzero already for `σ≥1`. The source explicitly proves the
prime-factor logarithm bound and both signs: the correction is added to
`L′/L` and subtracted from `−L′/L`. The public primitive-character wrapper
allows every positive modulus, including principal characters. Primitivity
of `χ` does not imply that of `χ²`.

[LFunctionInducedBound](../TwinPrime/Analytic/LFunctionInducedBound.lean)
performs the actual primitive-character transfer in the needed one-sided
form. For any nonprincipal character `η` modulo positive `q`, and
`1<σ≤9/8`, it proves
`Re(−Lη′/Lη(σ+it))≤K(q,t)+log q`. For a principal character it retains the
full zeta term and gives the upper bound `Re(−ζ′/ζ(s))+log q`.

If `η` is principal, its primitive inducing function is zeta at conductor
one. [ZetaLogDerivative](../TwinPrime/Analytic/ZetaLogDerivative.lean) proves
the exact pole identity

```text
−ζ′/ζ(s) = 1/(s−1) − Z′/Z(s),               s≠1, Z(s)≠0.
```

and quantitative regularized growth and Cauchy derivative bounds. It also
proves `‖Z(s)−1‖≤2/3`, hence `‖Z(s)‖≥1/3`, on `‖s−1‖≤1/4`, and

```text
‖−ζ′/ζ(s)−1/(s−1)‖ ≤ 40       if 0<‖s−1‖≤1/8.
```

These are actual local estimates, including the regularized value at one.
They do not permit discarding the principal pole at `σ+2it` in 3-4-1.

[ZetaLocalExpansion](../TwinPrime/Analytic/ZetaLocalExpansion.lean) now gives
the corresponding all-height expansion over the actual zeros of `Z`.
The outer bound is `4(‖c‖+2)²` and the center norm is at least `1/4` for
`Re(c)=2`. Put

```text
J(t) = C [1+log 16+2log(‖2+it‖+2)],
C = 144(1+log 5/log(6/5)).
```

The actual zero terms of `Z` have nonnegative real part to the right of
one. For `1<σ≤9/8`, the checked conclusion is

```text
Re(−ζ′/ζ(σ+it)) ≤ Re(1/(σ−1+it))+J(t).
```

The module also bounds `J(t)` above by
`C[1+log 16+2log(|t|+4)]`. The principal pole is retained for every height.

## 5. Proved nonquadratic branch

[LFunctionNonquadraticZeroFree](../TwinPrime/Analytic/LFunctionNonquadraticZeroFree.lean)
proves the full L-function application of 3-4-1. Assume `χ` is primitive
modulo `q>1` and `χ²≠1`. Set

```text
C = 144(1+log 5/log(6/5)),
K(q,t) = C [1+log 16+2log q+log(‖2+it‖+2)],
Eₙ(q,t) = 120+4K(q,t)+K(q,2t)+log q.
```

The theorem `LFunction_ne_zero_of_nonquadratic` proves
`Lχ(β+it)≠0` whenever `β≥1−1/(20Eₙ(q,t))`.
Its proof supposes `ρ=β+it` is an actual zero with
`δ=1−β≤1/(20Eₙ(q,t))`. Qualitative nonvanishing gives `δ>0`.
Put `E=Eₙ(q,t)`. Since `E≥120`, this zero has `β≥3/4` and lies in the
closed radius-`5/4` disk centered at `2+it`. Put `a=1/(4E)` and `σ=1+a`. These evaluation
points lie in the closed unit disks centered at `2+it` and `2+2it`, and
`a≤1/8` permits the real zeta estimate in section 4.

The inducing primitive character of `χ²` is nonprincipal, has conductor
`d>1` dividing `q`, and obeys `K(d,2t)≤K(q,2t)`. Applying the checked
one-sided formulas, Euler correction, and zeta pole estimate gives

```text
Re(−Lχ′/Lχ(σ+it)) ≤ −1/(a+δ)+K(q,t),
Re(−Lχ²′/Lχ²(σ+2it)) ≤ K(q,2t)+log q,
Re(−ζ′/ζ(σ)) ≤ 1/a+40.
```

Consequently 3-4-1 implies

```text
4/(a+δ) ≤ 3/a+E.
```

But `a=1/(4E)` and `δ≤1/(20E)` make the left side at least `40E/3`,
whereas the right side is `13E`. This numerical contradiction is proved by
`four_three_pole_contradiction` in
[ZeroFreeArithmetic](../TwinPrime/Analytic/ZeroFreeArithmetic.lean), for
every `E>0` and `0≤δ≤1/(20E)`. The same module proves the positive parameter
bounds `a≤1/8` and `1/(20E)≤1/4` from `E≥120`.
The checked L-function assembly retains the actual zero multiplicity,
conductor comparison, all disk memberships, and both Euler-correction signs.

## 6. Proved quadratic branch away from small heights

For `χ²=1`, the third term of 3-4-1 contains the principal pole at `σ+2it`.
[LFunctionQuadraticZeroFree](../TwinPrime/Analytic/LFunctionQuadraticZeroFree.lean)
keeps that pole and defines

```text
Eᵩ(q,t) = 120+4K(q,t)+J(2t)+log q.
```

For any `E≥Eᵩ(q,t)`, it proves nonvanishing whenever

```text
β ≥ 1−1/(40E),                 |t| ≥ 1/(4E).
```

Indeed, with `a=1/(4E)`, the extra pole has real part
`a/(a²+4t²)≤1/(5a)`. A hypothetical zero with `δ≤1/(40E)` would give
`4/(a+δ)≤3/a+1/(5a)+E`. The left side is at least `160E/11`, whereas the
right side is `69E/5`. This strict numerical contradiction and its analytic
application are both proved. The larger-budget theorem is needed when
combining the height ranges; it does not silently reuse a threshold for a
different budget.

## 7. Proved near-one uniqueness, simplicity, and reality

[LFunctionConjugateZeros](../TwinPrime/Analytic/LFunctionConjugateZeros.lean)
proves `Lχ⁻¹(conj s)=conj(Lχ(s))` globally for nonprincipal characters, by
ordered sums in `Re(s)>1` and analytic uniqueness. If `χ²=1`, this gives
conjugation symmetry of `Lχ`, its derivative, and its actual zeros.
The same module proves that two distinct actual zeros contribute at least
the sum of their simple-zero reciprocal terms to the local divisor sum.
For a nonreal conjugate pair `β±it` inside `B̄(2,5/4)`, its contribution at
real `σ>1` is at least `2(σ−β)/((σ−β)²+t²)`.

[LFunctionNearOneZeros](../TwinPrime/Analytic/LFunctionNearOneZeros.lean)
sets `E₀(q)=40+K(q,0)`, `a=1/(4E₀)`, and `ε=1/(16E₀)=a/4`.
For a fixed primitive character modulo `q>1`, it proves that the rectangle

```text
Re(ρ) ≥ 1−ε,                    |Im(ρ)| ≤ ε
```

contains at most one zero. The actual local zero sum at `1+a` is at most
`1/a+E₀=5E₀`. Each zero in the rectangle contributes at least
`3/(4a)=3E₀`; two distinct zeros therefore contradict `6E₀≤5E₀`.
Multiplicity at least two gives the same contradiction using a single
weighted divisor term. The module proves both the actual divisor value
`D(ρ)=1` and `meromorphicOrderAt Lχ ρ=1`. The latter follows from the finite
order and `divisor_apply`, so infinite order cannot be hidden by `untop₀`.
This is a true simple-zero statement.

When `χ²=1`, conjugation preserves the rectangle, and uniqueness forces the
possible zero to be real. These are uniqueness statements for one fixed
character, not a Landau–Page assertion comparing different characters.

## 8. Proved combined primitive region

[LFunctionZeroFreeRegion](../TwinPrime/Analytic/LFunctionZeroFreeRegion.lean)
defines

```text
R(q,t) = Eₙ(q,t)+Eᵩ(q,t)+4E₀(q),
w(q,t) = 1/(40R(q,t)).
```

For every primitive character modulo `q>1`, any actual zero `β+it` with
`β≥1−w(q,t)` satisfies `χ²=1`, `t=0`, and
`meromorphicOrderAt Lχ (β:ℂ)=1`. The region contains at most one zero for
that character, even when the two candidate points use different height
budgets. These are the checked theorems
`LFunction_zero_in_region_real_simple` and `LFunction_zero_in_region_unique`.

There is no gap between the branches: `R≥Eₙ` makes the width fit the
nonquadratic region. The larger-budget quadratic theorem excludes
`|t|≥1/(4R)`. For a remaining zero, `R≥4E₀` gives
`|t|<1/(4R)≤1/(16E₀)`, and `w≤1/(16E₀)` supplies the near-one rectangle.
The result permits a real simple zero; it does not assert that one exists.

[ZeroFreeLogarithms](../TwinPrime/Analytic/ZeroFreeLogarithms.lean) proves the
uniform conductor-height comparison

```text
R(q,t) ≤ 100 C [1+log q+log(|t|+4)].
```

It uses `‖2+it‖≤|t|+2`,
`log(|2t|+4)≤2log(|t|+4)`, `C≥144`, and the exact expansion
`R=400+8K(q,t)+K(q,2t)+4K(q,0)+J(2t)+2log q`. Thus the same real-simple
and per-character uniqueness conclusions hold in the explicit logarithmic
region

```text
β ≥ 1−1/[4000 C (1+log q+log(|t|+4))].
```

The width comparison and both L-function corollaries are proved; no
asymptotic conductor-growth assumption is added.

## 9. Proved principal zeta region

[ZetaZeroFree](../TwinPrime/Analytic/ZetaZeroFree.lean) defines

```text
Eζ(t) = 120+4J(t)+J(2t).
```

It proves `Z(β+it)≠0` whenever `β≥1−1/(80Eζ(t))`, at every real height.
The function here is the actual entire regularization, with `Z(1)=1`.
The separate `riemannZeta_ne_zero_of_re_ge_one_sub_budget` corollary proves
nonvanishing of actual `ζ(β+it)` in the same region under the retained
condition `β+it≠1`.

The proof again uses actual divisor multiplicities. For a hypothetical
zero with `δ=1−β≤1/(80Eζ)`, small heights `|t|≤1/8` lie inside the proved
radius-`1/4` nonvanishing disk for `Z`. At larger heights set `a=1/(4Eζ)`;
then `|t|≥4a`, so both principal pole terms have real part at most
`1/(17a)`. Applying 3-4-1 at conductor one yields

```text
4/(a+δ) ≤ 3/a+5/(17a)+Eζ.
```

The left side is at least `320Eζ/21`, whereas the right side is `241Eζ/17`.
This gives the checked contradiction. The principal proof does not assume
the BV-derived prime number theorem or any prime-distribution input.

[ZeroFreeLogarithms](../TwinPrime/Analytic/ZeroFreeLogarithms.lean) also proves
`Eζ(t)≤100 C [1+log(|t|+4)]`. Consequently the regularization is nonzero in

```text
β ≥ 1−1/[8000 C (1+log(|t|+4))].
```

The actual-zeta logarithmic-region corollary explicitly retains `β+it≠1`;
the regularized corollary includes the pole and its nonzero value.

## 10. Remaining scope

The primitive `q>1` zero-free region with a possible per-character real
simple exception is now proved. No Siegel-type lower bound for `1−β` of
that exception has been established. Uniqueness across different characters
or moduli is not claimed. Independent centered Siegel–Walfisz still needs
quantitative control of the possible exception and uniform inversion/Perron
estimates, including its principal conductor-one case. The independent zeta
zero-free region is now proved, but a prime-distribution estimate has not
yet been obtained from it.

The actual near-one derivative and zero-to-value bounds now check with
cost `10 exp(2)log²q` for q≥256. Finite-conductor positive constants and
the conversion from a supplied Siegel value lower bound to an arbitrary-power
zero gap also check; the value bound remains explicit and unproved. The
four-factor positivity, finite weighted-sum lower bound, L-series identity,
and regularized residue limit are proved. The quantitative residue comparison
is still missing. See [SIEGEL_EXCEPTION_ROUTE.md](SIEGEL_EXCEPTION_ROUTE.md)
for these results and the next exceptional-value estimates, and
[SIEGEL_WALFISZ_ROUTE.md](SIEGEL_WALFISZ_ROUTE.md) for the larger
independent distribution route. None of these analytic developments
discharges the independent signed correlation input `(B*)`.
