# Current proof obligations

Status: **the twin prime conjecture is not proved**. This ledger tracks the
implementation of the root [PLAN.md](../PLAN.md). The completion condition is
unchanged: an unconditional mathematical proof and a Lean theorem with the exact
target type. Conditional theorems and finite experiments do not satisfy it.

Gate audit, 2026-09-05: the middle-prime class theorem is complete,
but the current proof search is at an arithmetic impasse. The
cofinal signed hypothesis in
[ConditionalSignedBilinear.lean](../TwinPrime/ConditionalSignedBilinear.lean)
and the alternative logarithmic gain in
[ConditionalClassicalCenter.lean](../TwinPrime/ConditionalClassicalCenter.lean)
are both still unproved. Independent reinspection found no
implementation-only step or assessed arithmetic input that closes
either premise. The complete certified positive margin remains zero.
Resuming substantive proof work requires a new arithmetic argument
or input that addresses this gap; another conditional endpoint
does not do so.

The current research priority is the remaining signed contribution in the
[explicit total budget](SIGNED_TOTAL_BUDGET.md). Progress there is measured
by an improved bound for the full loss, not by formal declaration counts.
Substantial additional formalization requires a paper calculation showing
the improvement with all residual terms included.
The [distribution and Fourier tests](DISTRIBUTION_AND_FOURIER_BUDGET.md)
now quantify the zero lower-sieve coefficient even under hypothetical
stronger distribution, the additive norm loss, and the persistent
fixed-shift exception. None supplies a positive total margin.
The [divisor-switching test](DIVISOR_SWITCH_BUDGET.md) also retains
the squarefree and shifted-power defects and the full divisor
hyperbola. Its unrestricted moment has a negative leading budget;
the proposed rough moment and switched upper bound give no saving.
The [character-bias assessment](CHARACTER_BIAS_BUDGET.md) gives a
positive complete budget under sufficiently close real zeros at
unbounded conductors. That zero-existence hypothesis is unproved.
The [combined Chen test](CHEN_WEIGHT_REVIEW.md#combining-the-existing-class-and-moment-inequalities)
also admits zero twin mass while respecting the listed class and
moment bounds. The unconditional margin remains zero.
The [fixed-pair extraction test](FIXED_PAIR_EXTRACTION_BUDGET.md)
also keeps the graph threshold and all weight/endpoint losses.
Its enlarged two-coordinate marginal functional has exact
optimum 2, failing the required strict threshold. Recovering
the omitted marginal tails would need a new arithmetic estimate.
The [Gowers-uniformity test](GOWERS_FIXED_SHIFT_BUDGET.md)
retains the model, mixed and residual pair terms. The direct
norm transfer loses a power of X; a sparse nonnegative comparison
has small norms of every prescribed finite set of orders and
zero shift-two mass. These norm data alone give no signed gain.
The [weighted-distribution follow-up](CUTOFF_SHIFT_ROUTE.md#6-current-cutoff-weighted-distribution-and-its-full-residual)
retains the factorable approximation cost, outer tail and
prime-quotient sieve defect, including for the new September
2026 convolution theorem. The [prime-factor endpoint test](PRIME_FACTOR_ENDPOINT_BUDGET.md)
gives exact discrete-cofactor plateaus; a continuous limiting
law cannot be extended uniformly to the required microscopic
precision. Neither assessment improves the total margin.

## Exact formal endpoint

`TwinPrime.twinPrimeConjecture_of_signed_bilinear` in
[ConditionalSignedBilinear.lean](../TwinPrime/ConditionalSignedBilinear.lean) fixes

```text
U(X) = V(X) = floor(X^(1/5)),  C = 2 * twinPrimeConstant > 0.
```

It concludes the repository's exact `TwinPrimeConjecture` with only B* as
an explicit hypothesis. The independent classical input is now supplied:

| Input | Required statement | Mathematical and formal status |
|---|---|---|
| SW | `PointwiseSiegelWalfisz`, the uniform centered primitive-character estimate for every positive pair of real logarithmic exponents | **Proved in Lean**, including conductor one and constants and thresholds uniform over the growing conductor range. [SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean) supplies the exact proposition; [ClassicalDistribution.lean](../TwinPrime/Analytic/ClassicalDistribution.lean) supplies maximal SW, the exact BV statement at `2X+2`, and quantitative Mertens. |
| B* | For every Y, there is X ≥ Y with B_U,V(X) ≥ −CX/2 | **Open signed fixed-shift estimate. No proof obtained.** |

The remaining B* premise is a theorem argument, not an axiom or an inferred
fact. A report listing only standard Lean axioms does not discharge it.

An alternative sufficient endpoint,
`TwinPrime.twinPrimeConjecture_of_cofinal_classicalCenter_log_gain` in
[ConditionalClassicalCenter.lean](../TwinPrime/ConditionalClassicalCenter.lean),
allows arbitrary eventually positive cutoffs with UV<=X^a for a fixed
0<=a<1/2. It assumes a cofinal bound B+J>=cX/log^k(2X+2), where c>0,
k is a fixed natural number, and J is the actual finite classical center.
The [center precision proof](CLASSICAL_CENTER_PRECISION.md) supplies
|W2-(B+J)|=o(X/log^k X) and Epp=o(X/log^k X) from proved inputs, so this
gain would force genuine twin pairs. The gain is **unproved**. This
alternative endpoint is conditional and does not discharge B* or M4-M6.

The subsequent [smoothing audit](SMOOTHED_SIGNED_GAIN_REVIEW.md) computes,
on paper, the actual displacement from full logarithmic cutoff averaging.
At the primary/quarter cutoffs it is -15CX/4+o(X), exactly offset by the
larger averaged center. A fixed-power window cancels that boundary term
but still needs a signed gain. The directly applicable shifted-prime
second moment gives only an O(X sqrt(log X)) absolute bound after Cauchy.
An exact finite witness shows smoothing can turn a zero bilinear coefficient
negative. No new Lean theorem or completed milestone is claimed for this audit.

The subsequent [middle-prime sieve bound](MIDDLE_PRIME_SIEVE_BOUND.md) controls
the whole negative class n=q*b with U<q<=W prime and b W-rough. On paper,
for W=floor(X^v), 1/5<v<3/10, its positive mass T satisfies
limsup T/X<=C[4 log(5v)-2 log((1/2-v)/(3/10))]. In particular,
v=21/100 gives T<=0.263 C X eventually. The finite Lean sieve uses the
actual shifted-Mangoldt weight. Its exact denominator is identified, and
the complete 3^omega-weighted error is proved negligible after every fixed
logarithmic loss under a fixed-power modulus cap below X^(1/2).
The full eventual 0.263 C X class bound is now a Lean theorem:
`eventually_middlePrimeMass_twentyOneHundredths_le` in
[MiddlePrimeSieveBound.lean](../TwinPrime/Analytic/MiddlePrimeSieveBound.lean).
It supplies the actual thresholds, denominator limit, prime main sum and
every weighted error, at the fixed level exponent 49999/100000. The sharp
general limiting K(v) formula above is still the paper corollary obtained
by taking that exponent up to one half; it is not required for the completed
0.263 theorem. The
[rough-composite calculation](ROUGH_COMPOSITE_SIEVE_BOUND.md) gives only
N_rough<=4CX-P+o(X), where P is the actual prime-input contribution.
It does not close the allowance. The signed composite-smooth-part
contribution remains unestimated.
This partial bound does not discharge B* or the cofinal logarithmic gain.
The total budget requires R=N_rough+N_comp-P_comp below 0.737 C X with
positive slack after errors. The presently certified total loss remains
at most C X+o(X), with no positive margin. The reviewed Buchstab and
scale-averaged multiplicative-correlation candidates do not improve it.

The [dispersion range-removal proof](DISPERSION_GCD_ROUTE.md) now sums the
diagonal budget over the exact growing box family and removes two distinct
large-gcd ranges. Only O(log X) boxes are nonzero, giving an O(X/log^2 X)
large-gcd dispersion budget. The actual original-factor large-gcd sum
is O(X/log^7 X). Inputs divisible by a prime square p² with p above the
same logarithmic cutoff also have factorwise absolute mass O(X/log^7 X).
The simultaneous residual has gcd≤ceil(log^10(4X+4)) and no prime square
above that cutoff; its difference from B is O(X/log^7 X). Every squarefree
input survives. The remaining signed sum is unestimated. The
[shifted-Möbius input audit](SHIFTED_MOBIUS_INPUT_AUDIT.md) identifies why
the inspected shift-average and conditional fixed-shift results do not
provide this estimate.
The [prime-beta reduction](BILINEAR_PRIME_BETA_ROUTE.md) removes proper
prime powers inside the beta coefficient at a uniform absolute cost
O(X log^2(4X+4)/sqrt(V)). The normalized error tends to zero at primary V,
even after multiplication by any fixed logarithmic power and for arbitrary
left cutoff U(X). Exact grouping connects the replacement to its convolution.
The original coefficient vanishes when its nontrivial small-prime part is
at most U. The prime-only coefficient has an exact smooth/rough formula
without squarefreeness assumptions. Neither result estimates the signed
mass of the surviving prime-weighted subrange; B* remains open.
The [cutoff-change proof](CUTOFF_SHIFT_ROUTE.md) controls another whole
signed contribution: B(U,U,X)-B(U,W,X)=o(X) for primary U and any W
with U(X)W(X)≤X^a eventually, for a fixed 0≤a<1/2. In particular W can
be floor(X^(1/4)). At this choice the moduli are at most X^(9/20) and
the even-modulus budget is O(X^(19/20)log²X). The final prime-only
replacement also differs from original B by o(X). Its mixed coefficient
retains m_U(a), not m_W(a); primes a with U<a≤W give a negative class.
The cutoff change has no factorwise absolute bound and is not automatically
valid after imposing other restrictions. No positive fraction of the full
main term has been saved, and B* remains an unproved theorem argument.
The previous SW-and-B* endpoint remains available as a general implication.
The previous
`twinPrimeConjecture_of_bv_and_bilinear` remains available with BV and B*
as arguments. The ordinary Mertens estimate
`MertensLogSix` is now a proved consequence of BV in
[PrimeToMertens.lean](../TwinPrime/Analytic/PrimeToMertens.lean). It yields
both totient limits and their constants through the checked
[classical reduction](CLASSICAL_REDUCTION.md). BV and the smoothed limit give
`A_U(X)/X → C`. BV and Möbius cancellation give both
`H_U(X)/X → 0` and `I_U,U(X)/X → 0`, including the full shared-prime correction,
and hence `K/X → 0`. The two limits supply the eventual `CX/8` budgets at a
common threshold. Cofinal B* then gives `W₂ ≥ CX/4`; the proved `Epp=o(X)`
removes the proper prime powers and reaches genuine twin pairs.

The original `twinPrimeConjecture_of_primary_estimates` remains available with
the A, K, B budgets as arguments. The more general
`twinPrimeConjecture_of_bilinear_estimates` permits arbitrary cutoff functions
and positive C with explicit elementary support conditions. None is an
unconditional twin-prime theorem.

`twinPrimeConjecture_of_classical_inputs_and_bilinear` remains available with
the two totient limits as separate assumptions, and
`twinPrimeConjecture_of_bv_mertens_and_bilinear` retains a separate Mertens
argument. The classical B* endpoint supplies the independent pointwise SW theorem
and all these classical bridges, retaining only B*.

The [prime-to-Mertens reduction](PNT_MERTENS_REDUCTION.md) now eliminates
the separate Mertens input in Lean. It proves the centered signed error,
hyperbola remainders, logarithmic unweighting, and actual contraction before
applying supremum absorption. The formal implication uses BV's maximal
ordinary prime error; the broader ordinary prime-error implication in the
paper note is not a standalone formal theorem. No new analytic assumption
has replaced the discharged Mertens argument.

The [BV implementation note](BV_REDUCTION.md) now records checked finite
character orthogonality, centered endpoint maxima, primitive replacement,
and explicit absorption of its error at the exact modulus range. Primitive
Gauss norms at composite moduli, the finite character-to-additive transfer,
exact conductor regrouping, logarithmic totient weights, and conductor Abel
summation also check. Additive and primitive-character large sieves are
proved with an explicit logarithmic loss, including the rational-frequency
family and phase bridge. Primitive-character interval cancellation,
logarithmic Type I bounds, rectangular first moments, and maximal and
adaptive disjoint-interval second moments now check. The exact staircase
identity also preserves the product cutoff. The combined maximal bilinear
first moment now follows in Lean, including the actual per-character finite
maximum. Its exact masked-box application proves the full finite Vaughan
Type II maximal mean. The complete Type I and numerical assembly now proves
the full maximal character mean and centered large-conductor tail. The
final asymptotic BV assembly at T=2X+2 now also checks; the independent
uniform centered small-conductor theorem now supplies its input;
see the [finite maximal route](BV_MAXIMAL_ROUTE.md).
The complete chain now discharges the named BV hypothesis.

The [Type I implementation route](BV_TYPEI_ROUTE.md) is now formalized:
BV-internal cutoffs near T^(1/8) make direct Pólya–Vinogradov bounds sufficient
in R≤sqrt(T), with middle exponent 15/16. `primitive_character_mean_value`
has only the explicit numerical conditions T≥256 and 1≤R≤sqrt(T), and
constant `C₀=5+16(2/log 2)^4`. The centered tail excludes conductor one;
the finite progression reduction retains the small-conductor mass, including
all short-modulus and empty-tail cases. The
[small-conductor audit](SIEGEL_WALFISZ_ROUTE.md) records available analytic
ingredients and the completed independent quantitative theorem.

The actual primitive L-function and pole-corrected zeta truncation bounds
now hold on Re(s)>0, using locally uniform ordered convergence and analytic
uniqueness. The zeta pole has regularized value one. Explicit primitive
L-function growth and Cauchy derivative bounds combine with a uniform
center lower bound to give a Jensen bound for zero multiplicities near
Re(s)=2. The actual three-four-one logarithmic-derivative inequality is
proved on Re(s)>1. Actual zero removal, polynomial bounds, and a normalized
holomorphic logarithm now give a quantitative expansion of L′/L over the
actual local divisor, with explicit conductor and height dependence.
Inducing Euler corrections have norm at most log q, the regular zeta
logarithmic derivative has norm at most 40 near its pole, and actual zero
terms have the required nonnegative real parts. These inputs now prove
quantitative zero exclusion for primitive nonquadratic characters, and
for quadratic characters outside a small height interval. Near one,
actual reciprocal contributions prove uniqueness and multiplicity one;
conjugation forces the quadratic-character exception to be real.

The one-sided consequence now retains a selected actual zero explicitly:
for primitive q>1, 1<σ≤9/8, and an actual zero β+it with β≥3/4,
`Re(−Lχ′/Lχ(σ+it)) ≤ K(q,t)−1/(σ−β)`, where
`K(q,t)=144(1+log 5/log(6/5)) [1+log 16+2log q+log(‖2+it‖+2)]`.
Its companion omits the selected term, and K is monotone in the positive
conductor. The nonquadratic branch uses
`E_N=120+4K(q,t)+K(q,2t)+log q`, while the quadratic branch retains the
principal pole and uses `E_Q=120+4K(q,t)+Kζ(2t)+log q`.
With `E₀=40+K(q,0)` and `R=E_N+E_Q+4E₀`, the region
`β≥1−1/(40R(q,t))` contains at most one zero of the fixed primitive
character. Any such zero has t=0, χ²=1, and actual meromorphic order one.
This is per-character uniqueness, not a theorem about exceptions across
different characters. The independent Siegel value theorem and an
arbitrary-power lower bound for the exceptional distance 1−β are now
proved below. Smoothed inversion and quantitative finite contour estimates
now check; their uniform asymptotic assembly and independent centered SW
are now proved in the [completed classical chain](CLASSICAL_DISTRIBUTION_THEOREM.md).

The principal case is handled independently: regularized zeta has no zeros
when `β≥1−1/(80Eζ(t))`, where `Eζ(t)=120+4Kζ(t)+Kζ(2t)`.
The regularized statement includes its nonzero value at one; the theorem
for the actual zeta function explicitly excludes its pole.

Both regions now have a checked logarithmic form. Put
`C_loc=144(1+log 5/log(6/5))`. The primitive width can be replaced by
`1/[4000C_loc(1+log q+log(|t|+4))]`, retaining the same per-character
real/simple/unique conclusion. Regularized zeta has no zeros in width
`1/[8000C_loc(1+log(|t|+4))]`; its actual-zeta corollary excludes s=1.

The [exceptional-zero continuation audit](SIEGEL_EXCEPTION_ROUTE.md) now records
a proved bound `|Lχ′(u)|≤10 exp(2)log²q` for primitive q≥256 and
`1−1/log q≤u≤1`, using actual truncation at M=q. The real-segment estimate
therefore proves `|Lχ(1)|≤10 exp(2)log²q(1−β)` for an actual real zero in
that interval. Qualitative nonvanishing also yields positive constants
uniform over each finite conductor range, for both values and real-zero gaps.
The formal conversion from a supplied Siegel value bound at exponent ε/2
to a gap at exponent ε has constant `cε²/[160 exp(2)]` at large q and a
proved finite-conductor minimum for the remaining q. The independent
[Siegel value theorem](../TwinPrime/Analytic/SiegelValue.lean) now supplies
that input: for every ε>0 there is one c>0 such that
`c q^(−ε)≤|Lχ(1)|` for every primitive quadratic character of conductor
q>1. The constant is uniform over q and χ, but no effective construction
is asserted. [SiegelZeroGapUnconditional.lean](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean)
therefore proves the arbitrary-power gap without a value-bound premise.

The actual four-factor Dirichlet convolution `ζ*aχ₁*aχ₂*a(χ₁χ₂)` now has
proved nonnegative real coefficients, coefficient one at n=1, and coefficients
at least one at every nonzero square. Its finite weighted sums are at least
one for every real exponent and cutoff X≥1. The actual L-series product
identity holds on Re(s)>1. Under the retained three nonprincipal hypotheses,
the entire regularization has nonzero value `Lχ₁(1)Lχ₂(1)Lχ₁χ₂(1)` and
the corresponding punctured residue limit. Complete-period cancellation
now gives actual pair and triple summatory bounds `3q√x` and
`10q²x^(2/3)(1+log x)`, without primitivity. The triple bound implies
`130q²x^(3/4)`; ordered Dirichlet convergence, holomorphy and analytic
uniqueness identify the triple series with the actual three L-functions
on Re(s)>3/4. Its reciprocal tail at one is at most `1300q²M^(−1/4)`.
The finite complex hyperbola formula then proves

```text
|S(x) − λx| ≤ (1+3250q²)x^(4/5)(1+log x)²,  x≥1,
λ = Lχ₁(1)Lχ₂(1)Lχ₁χ₂(1).
```

This bound requires all three common-modulus characters to be nonprincipal;
the distinct quadratic specialization discharges the product condition.
Subtracting λ from the positive-index coefficients gives the exact centered
prefix bound `441(1+3250q²)N^(9/10)`. Analytic uniqueness identifies its
ordered series with the actual pole-canceled product on Re(s)>9/10.
At 19/20≤β<1, its tail is at most
`18522(1+3250q²)N^(−1/20)`. Zeta truncation and finite positivity then
prove a quantitative residue lower bound whenever the actual product has
nonpositive real part at β, including an actual zero. A proved natural
cutoff has size at most `Aq^40` for an explicit absolute A.

Exact change-of-level identities preserve zeros and cost at most
`1+log Q` at one; every nonprincipal character satisfies
`|Lχ(1)|≤5+log Q`, including imprimitive characters. These estimates turn
the residue comparison at Q=q₀q into a lower bound for the target value.
For each ε, the proof fixes δ₀=min(1/20,ε/80). If a primitive quadratic
zero lies in [1−δ₀,1), its character is a fixed auxiliary. Otherwise the
proved primitive character modulo four and the actual real sign theorem
supply the needed product inequality. Power absorption and a finite-conductor
minimum give the uniform constant. Neither branch assumes the desired
value bound. The [exceptional-zero route](SIEGEL_EXCEPTION_ROUTE.md) records
this checked argument. The [Mellin contour route](MELLIN_CONTOUR_ROUTE.md)
now supplies actual smoothed inversion, quantitative contour estimates, and
finite unsmoothing. Its primitive-character estimate uses no supplied
zero-free premise. The ramp kernel and principal pole kernel are inverted
exactly; the latter gives `(x−1)^2/(2x)` for x≥1. Full complex
logarithmic-derivative bounds hold left of one. For q≤(log x)^B and
H=(log x)^K, the evaluation width is at least `k(log x)^(−1/2)` and
the primitive norm budget is at most `C log x`, with uniform positive
constants. Asymptotic error absorption, principal contour assembly, and
centered finite differences now prove the exact sharp-sum theorem. The
[classical proof map](CLASSICAL_DISTRIBUTION_THEOREM.md) records the
uniform parameter choices and the completed M3 chain. Only B* remains
as an argument of the classical B* endpoint.

## Obligations already discharged

The interval convention is always integer `X < n ≤ 2X`. `N2` counts genuine
twins, `W2` sums Λ(n)Λ(n+2), and `Epp` is the same sum restricted to inputs with
at least one nonprime member. These definitions do not incorporate a lower bound.

| Result | Checked declaration or module |
|---|---|
| N₂(X) = twinCount(2X) − twinCount(X), with monotonicity | `N2_eq_twinCount_sub`, `twinCount_mono` |
| Cofinal positive N₂ is equivalent to the conjecture | `twinPrimeConjecture_iff_cofinal_N2_pos` |
| W₂ − Epp is exactly the prime-pair logarithmic sum | `W2_sub_Epp_eq_prime_sum` |
| 0 ≤ Epp and W₂ − Epp ≤ log²(2X+2) N₂ | `Epp_nonneg`, `W2_sub_Epp_le_log_sq_mul_N2` |
| Epp ≤ 4√(2X+2) log²(2X+2), hence Epp/X → 0 | `Epp_le_sqrt_mul_log_sq`, `tendsto_Epp_div` |
| Cofinal W₂ ≥ cX, c > 0, implies the conjecture | `twinPrimeConjecture_of_cofinal_W2_linear` |
| The fifth-root cutoffs satisfy the required support conditions | [Cutoff.lean](../TwinPrime/Analytic/Cutoff.lean) |
| Exact cutoff Vaughan identity | `Analytic.vaughanIdentity`, `vaughanIdentity_apply_of_lt` |
| Explicit c and β, support c(q)=0 for q>UV, β(r)=0 for r≤V | [Vaughan.lean](../TwinPrime/Analytic/Vaughan.lean) |
| abs(c(q)) ≤ log q, 0 ≤ β(r) ≤ log r | `abs_vaughanCoefficient_le_log`, `vaughanBeta_nonneg`, `vaughanBeta_le_log` |
| Truncated sums with real division inside every logarithm | [TruncatedMangoldt.lean](../TwinPrime/Analytic/TruncatedMangoldt.lean) |
| Exact identity W₂ = A + H − I + B | `Analytic.correlation_decomposition` |
| A and I as sums over moduli at most U and UV | `mixedCorrelation_eq_progressions`, `typeITerm_eq_progressions` |
| B as the exact finite factor-pair sum with both cutoffs and the hyperbolic boundary | [FactorRanges.lean](../TwinPrime/Analytic/FactorRanges.lean), `bilinearTerm_eq_pair_sum` |
| d ≤ 2X/(V+1), r ≤ 2X/(U+1) for every retained pair | `bilinearPairs_left_le_div`, `bilinearPairs_right_le_div` |
| The four-row error budget reaches the exact target | `four_obligation_budget`, `twinPrimeConjecture_of_bilinear_budget` |
| Exact totient formula (Q), including shared prime factors | `totientTypeIMain_eq_primePowerCorrection` in [MoebiusTotient.lean](../TwinPrime/Analytic/MoebiusTotient.lean) |
| Exact recurrence for Fₚ and its complete finite expansion | `oddMoebiusTotientSumDivisible_recurrence`, `oddMoebiusTotientSumDivisible_expansion` |
| F→0 implies the entire shared-prime correction tends to zero for U→∞, with no restriction on V | `tendsto_sharedPrimeCorrection` in [MoebiusTotientAsymptotics.lean](../TwinPrime/Analytic/MoebiusTotientAsymptotics.lean) |
| Sum of odd Λ(b)/φ(b) ≤ 6 log²(V+1); F log²→0 implies Q(U,U)→0 for growing U | [TotientMainAsymptotics.lean](../TwinPrime/Analytic/TotientMainAsymptotics.lean) |
| Exact shifted progression errors, reduced-residue estimates including q=1, and weighted modulus sums | [PrimeDistribution.lean](../TwinPrime/Analytic/PrimeDistribution.lean) |
| U² lies eventually in the BV range for every fixed logarithmic loss | [GrowthBounds.lean](../TwinPrime/Analytic/GrowthBounds.lean) |
| All even-modulus exceptions fit a proved sublinear budget | [EvenModuli.lean](../TwinPrime/Analytic/EvenModuli.lean), [EvenAsymptotics.lean](../TwinPrime/Analytic/EvenAsymptotics.lean) |
| A/X→C from the two explicit classical inputs | `tendsto_mixedCorrelation_div_of_inputs` in [MixedCorrelation.lean](../TwinPrime/Analytic/MixedCorrelation.lean) |
| Exact Type I main coefficient and sublinear distribution remainder under BV | [TypeICorrelation.lean](../TwinPrime/Analytic/TypeICorrelation.lean) |
| Discrete Abel summation and logarithmic weight bound from cumulative errors | [PartialSummation.lean](../TwinPrime/Analytic/PartialSummation.lean) |
| Logarithmic cancellation transfers to the fifth-root cutoff | [CutoffLogarithms.lean](../TwinPrime/Analytic/CutoffLogarithms.lean) |
| Finite H estimate and H/X→0 from BV and weighted F decay | [LogarithmicCorrection.lean](../TwinPrime/Analytic/LogarithmicCorrection.lean) |
| K/X→0 from BV and F(t)log²(t+1)→0 | `tendsto_typeICorrection_div_of_inputs` in [TypeICorrection.lean](../TwinPrime/Analytic/TypeICorrection.lean) |
| Bilinear coefficient vanishes on primes, equals Λ−log on rough inputs, with explicit divisor and prime-power bounds | [BilinearSign.lean](../TwinPrime/Analytic/BilinearSign.lean) |
| τ(n)³≤4096n, hence τ(n)≤16n^(1/3) | [DivisorGrowth.lean](../TwinPrime/Analytic/DivisorGrowth.lean) |
| Removing prime powers from the bilinear term costs o(X), uniformly in eventually positive cutoffs | [BilinearExceptional.lean](../TwinPrime/Analytic/BilinearExceptional.lean) |
| Exact ordinary-to-odd-totient convolution, preserving real logarithm arguments | [MoebiusSmoothing.lean](../TwinPrime/Analytic/MoebiusSmoothing.lean) |
| Absolute and logarithmically weighted summability of the correction; its sum is exactly 2C₂ | [SmoothingSummability.lean](../TwinPrime/Analytic/SmoothingSummability.lean) |
| Ordinary Mertens log⁶ bound gives explicit ordered reciprocal tails of order log⁻⁵ | [MoebiusAbel.lean](../TwinPrime/Analytic/MoebiusAbel.lean) |
| M(N)=o(N) implies the ordered reciprocal Möbius sum tends to zero, using an exact hyperbola identity | [MoebiusHyperbola.lean](../TwinPrime/Analytic/MoebiusHyperbola.lean) |
| Harmonic convolution fixes the smoothed constant 1 and logarithmic moment −1 from the ordinary Mertens input | [MoebiusBoundary.lean](../TwinPrime/Analytic/MoebiusBoundary.lean) |
| Dominated convergence transfers both ordinary limits to the required odd totient limits | [SmoothingLimits.lean](../TwinPrime/Analytic/SmoothingLimits.lean) |
| A and K follow from BV and the single named ordinary Mertens hypothesis | [MertensReduction.lean](../TwinPrime/Analytic/MertensReduction.lean) |
| Exact finite rough-parity identity, including prime squares, and explicit conditional alternative | [RoughParity.lean](../TwinPrime/RoughParity.lean) |
| Modulus one of BV gives the ordinary prime estimate with every fixed logarithmic saving | [BombieriVinogradovPsi.lean](../TwinPrime/Analytic/BombieriVinogradovPsi.lean) |
| Logarithmic Leibniz rule and exact centered identity μ*a=μ log²−2c ε | [MoebiusSelberg.lean](../TwinPrime/Analytic/MoebiusSelberg.lean) |
| Exact factor-box restriction, weighted dispersion inequality, and a sublinear diagonal contribution; signed off-diagonal retained | [Dispersion.lean](../TwinPrime/Analytic/Dispersion.lean) |
| Unique right-closed factor-box partition, cardinal bound, and exact global bilinear identity | [DispersionPartition.lean](../TwinPrime/Analytic/DispersionPartition.lean) |
| Summed diagonal o(X) after every fixed logarithmic loss; explicit off-diagonal root budget | [DispersionAggregate.lean](../TwinPrime/Analytic/DispersionAggregate.lean), [DispersionGlobal.lean](../TwinPrime/Analytic/DispersionGlobal.lean) |
| Elementary large-gcd rectangle count, exact signed off-diagonal split, and O(X/log X) full large-gcd root budget | [DispersionLargeGcd.lean](../TwinPrime/Analytic/DispersionLargeGcd.lean), [DispersionGcdCutoff.lean](../TwinPrime/Analytic/DispersionGcdCutoff.lean), [DispersionGcdGlobal.lean](../TwinPrime/Analytic/DispersionGcdGlobal.lean) |
| Original-factor gcd split with exact coefficients; actual large-gcd sum O(X/log^6 X), and (B−Bsmall)/X→0 | [DispersionBilinearGcd.lean](../TwinPrime/Analytic/DispersionBilinearGcd.lean), [BilinearGcdReduction.lean](../TwinPrime/Analytic/BilinearGcdReduction.lean) |
| Exact three-level active band with at most 3D boxes; stronger O(X/log^2 X) dispersion and O(X/log^7 X) original-gcd errors | [DispersionActiveBand.lean](../TwinPrime/Analytic/DispersionActiveBand.lean), [DispersionActiveBudget.lean](../TwinPrime/Analytic/DispersionActiveBudget.lean) |
| Large-prime-square factorwise absolute mass, exact simultaneous residual, explicit O(X/log^7 X) difference, and survival of every squarefree input | [DispersionSquareFactor.lean](../TwinPrime/Analytic/DispersionSquareFactor.lean), [BilinearStructuredCore.lean](../TwinPrime/Analytic/BilinearStructuredCore.lean) |
| Every fixed logarithmic power is absorbed by the primary-cutoff denominator | [DispersionGrowth.lean](../TwinPrime/Analytic/DispersionGrowth.lean) |
| Integer prime errors extend to real endpoints with explicit floor-error constants | [PrimeReal.lean](../TwinPrime/Analytic/PrimeReal.lean) |
| The prime reciprocal center and O(log⁻⁵) error follow from the O(x/log⁶x) prime error | [PrimeReciprocal.lean](../TwinPrime/Analytic/PrimeReciprocal.lean), [PrimeReciprocalReal.lean](../TwinPrime/Analytic/PrimeReciprocalReal.lean) |
| Exact hyperbola summation for arbitrary integer cutoffs and real product endpoints | [Hyperbola.lean](../TwinPrime/Analytic/Hyperbola.lean) |
| Local upper bounds plus an eventual strict supremum contraction imply a global upper bound | [SupremumContraction.lean](../TwinPrime/Analytic/SupremumContraction.lean) |
| Absolute reciprocal mass of the centered coefficient is at most D(2+log N)², unconditionally | [SelbergCoefficientBounds.lean](../TwinPrime/Analytic/SelbergCoefficientBounds.lean) |
| The exact Möbius and prime hyperbola formulas include the actual coefficients, real quotients, and overlap constants | [SelbergSummatory.lean](../TwinPrime/Analytic/SelbergSummatory.lean) |
| BV supplies the weighted prime asymptotic, including the linear term and real endpoint corrections | [LogFactorial.lean](../TwinPrime/Analytic/LogFactorial.lean), [PrimeLog.lean](../TwinPrime/Analytic/PrimeLog.lean) |
| The centered signed Selberg sum is O(x/log⁵x), derived from BV | [SelbergCenteredError.lean](../TwinPrime/Analytic/SelbergCenteredError.lean), [PrimeToSelberg.lean](../TwinPrime/Analytic/PrimeToSelberg.lean) |
| The Möbius hyperbola tail and overlap cost O(x/log⁴x), using only the trivial Mertens bound | [SelbergMoebiusError.lean](../TwinPrime/Analytic/SelbergMoebiusError.lean) |
| Reciprocal-logarithm kernel and exact real logarithmic unweighting, including the final fractional interval | [LogKernel.lean](../TwinPrime/Analytic/LogKernel.lean), [MoebiusLogWeight.lean](../TwinPrime/Analytic/MoebiusLogWeight.lean) |
| Local boundedness and the actual short hyperbola-head estimate for the weighted Mertens supremum | [WeightedMertens.lean](../TwinPrime/Analytic/WeightedMertens.lean) |
| Fixed parameter choice, actual eventual contraction, and quantitative Mertens cancellation | [ContractionParameters.lean](../TwinPrime/Analytic/ContractionParameters.lean), [MertensContraction.lean](../TwinPrime/Analytic/MertensContraction.lean) |
| BV implies MertensLogSix; the refined twin-prime endpoint retains only BV and B* | [PrimeToMertens.lean](../TwinPrime/Analytic/PrimeToMertens.lean), [ConditionalBilinear.lean](../TwinPrime/ConditionalBilinear.lean) |
| Exact progression-to-character decomposition and centered finite endpoint maxima | [CharacterSums.lean](../TwinPrime/Analytic/CharacterSums.lean), [CharacterMaximal.lean](../TwinPrime/Analytic/CharacterMaximal.lean) |
| Primitive replacement retains the principal main term and costs only the explicitly bounded noncoprime mass | [CharacterExceptions.lean](../TwinPrime/Analytic/CharacterExceptions.lean), [CharacterPrimitiveReduction.lean](../TwinPrime/Analytic/CharacterPrimitiveReduction.lean) |
| The total replacement error is at most X/log^A X eventually for Q≤X^(1/2)/log^(A+2)X, uniformly over all endpoints | [CharacterExceptionGrowth.lean](../TwinPrime/Analytic/CharacterExceptionGrowth.lean) |
| Primitive Gauss sums have squared norm q for every positive modulus, including composite q and q=1 | [PrimitiveGauss.lean](../TwinPrime/Analytic/PrimitiveGauss.lean) |
| Unit-group Parseval and the finite q/φ(q) transfer from additive sums to primitive character sums | [CharacterLargeSieveTransfer.lean](../TwinPrime/Analytic/CharacterLargeSieveTransfer.lean) |
| Exact conductor regrouping, retaining the principal conductor and every inducing multiplicity | [CharacterConductor.lean](../TwinPrime/Analytic/CharacterConductor.lean) |
| Absolute summability of the reciprocal-totient correction and the uniform logarithmic multiple weight | [TotientReciprocal.lean](../TwinPrime/Analytic/TotientReciprocal.lean) |
| Exact maximal progression endpoint reduced to primitive conductor mass with one logarithmic loss | [ConductorReduction.lean](../TwinPrime/Analytic/ConductorReduction.lean) |
| Finite conductor Abel identity and tail bound from a cumulative quadratic estimate | [ConductorAbel.lean](../TwinPrime/Analytic/ConductorAbel.lean) |
| Finite additive kernel bounded by interval length and reciprocal circle distance | [AdditiveKernel.lean](../TwinPrime/Analytic/AdditiveKernel.lean) |
| Finite Schur and duality bounds for complex matrices with an explicit absolute Gram row bound | [FiniteLargeSieve.lean](../TwinPrime/Analytic/FiniteLargeSieve.lean) |
| Harmonic reciprocal mass for separated positive and signed real points | [SeparatedReciprocal.lean](../TwinPrime/Analytic/SeparatedReciprocal.lean) |
| Reciprocal-product rational spacing and uniqueness of reduced unit frequencies across moduli | [RationalFrequencySeparation.lean](../TwinPrime/Analytic/RationalFrequencySeparation.lean) |
| Additive large sieve for separated frequencies, with proved Gram rows and explicit harmonic loss | [AdditiveLargeSieve.lean](../TwinPrime/Analytic/AdditiveLargeSieve.lean) |
| Rational additive and weighted primitive-character large sieves, with explicit constant N−M+Q²(1+2log(Q+1)) | [RationalLargeSieve.lean](../TwinPrime/Analytic/RationalLargeSieve.lean) |
| Pólya–Vinogradov with bound √q H_q for primitive characters at every q>1 | [CharacterInterval.lean](../TwinPrime/Analytic/CharacterInterval.lean) |
| Logarithmic character cancellation and finite Type I outer bounds, including zero endpoints | [CharacterLogInterval.lean](../TwinPrime/Analytic/CharacterLogInterval.lean) |
| Primitive inversion reindexing and rectangular bilinear first moments from weighted Cauchy–Schwarz | [CharacterBilinear.lean](../TwinPrime/Analytic/CharacterBilinear.lean) |
| Binary-tree energy and independently selected prefix endpoints with squared depth loss | [DyadicMaximal.lean](../TwinPrime/Analytic/DyadicMaximal.lean) |
| Exact dyadic interval covers, no reuse across disjoint intervals, and adaptive weighted variation | [DyadicIntervalCover.lean](../TwinPrime/Analytic/DyadicIntervalCover.lean) |
| Primitive-character maximal prefix and adaptive disjoint-interval second moments without a new analytic input | [CharacterMaximalLargeSieve.lean](../TwinPrime/Analytic/CharacterMaximalLargeSieve.lean) |
| Exact nonincreasing-boundary staircase and clamped mn≤t specialization | [DyadicStaircase.lean](../TwinPrime/Analytic/DyadicStaircase.lean) |
| Fixed disjoint interval second moments without a depth or interval-count loss | [IntervalFamilyLargeSieve.lean](../TwinPrime/Analytic/IntervalFamilyLargeSieve.lean) |
| Weighted first moments of varying rectangle families and the explicit staircase constant | [WeightedBilinear.lean](../TwinPrime/Analytic/WeightedBilinear.lean) |
| Disjoint left children and correction intervals at each staircase level | [DyadicStaircaseGeometry.lean](../TwinPrime/Analytic/DyadicStaircaseGeometry.lean) |
| Exact grouping of every staircase correction by height and the resulting norm bound | [DyadicStaircaseLevels.lean](../TwinPrime/Analytic/DyadicStaircaseLevels.lean) |
| Arbitrary antitone boundaries in a weighted bilinear first moment, derived from fixed-interval second moments | [DyadicStaircaseFirstMoment.lean](../TwinPrime/Analytic/DyadicStaircaseFirstMoment.lean) |
| Actual primitive-character product-cutoff maxima with factor 2(k+1)(j+1), including inverse characters | [CharacterMaximalBilinear.lean](../TwinPrime/Analytic/CharacterMaximalBilinear.lean) |
| Finite box polynomial and its C=Q²L specialization | [BilinearBoxPolynomial.lean](../TwinPrime/Analytic/BilinearBoxPolynomial.lean) |
| Exact global power-of-two partition with disjoint cells and unique positive index membership | [DyadicNatPartition.lean](../TwinPrime/Analytic/DyadicNatPartition.lean) |
| Exact two-variable dyadic partition for coefficients with bounded support | [DyadicBilinearPartition.lean](../TwinPrime/Analytic/DyadicBilinearPartition.lean) |
| Strict lower-cutoff and upper-support masks, their norm bounds, and dyadic coefficient energies | [VaughanBoxCoefficients.lean](../TwinPrime/Analytic/VaughanBoxCoefficients.lean) |
| Full finite Vaughan character identity retaining the low term, and exact Type II pair sums | [CharacterVaughan.lean](../TwinPrime/Analytic/CharacterVaughan.lean) |
| Actual masked Vaughan box maximal bounds and their polynomial specialization | [CharacterVaughanBox.lean](../TwinPrime/Analytic/CharacterVaughanBox.lean) |
| Uniform vanishing of discarded box sums and maxima, with exact active side and depth bounds | [VaughanActiveBoxes.lean](../TwinPrime/Analytic/VaughanActiveBoxes.lean) |
| Exact active-box identity and control of the full Type II maximum by active box maxima | [CharacterVaughanDyadic.lean](../TwinPrime/Analytic/CharacterVaughanDyadic.lean) |
| Full finite primitive-character Type II maximal mean, with explicit 2D⁴ log(T)L_Q loss and half-cutoff polynomial | [CharacterVaughanMean.lean](../TwinPrime/Analytic/CharacterVaughanMean.lean) |
| Elementary uncentered character maxima and their exact agreement with centered maxima away from the principal character | [CharacterTrivialBounds.lean](../TwinPrime/Analytic/CharacterTrivialBounds.lean) |
| Exact supported convolution reindexing and both Type I factorizations with natural quotient endpoints | [CharacterVaughanTypeI.lean](../TwinPrime/Analytic/CharacterVaughanTypeI.lean) |
| Exact primitive-character cardinality bounds and weighted counting, including empty ranges | [PrimitiveCharacterCounting.lean](../TwinPrime/Analytic/PrimitiveCharacterCounting.lean) |
| Uniform Type I pointwise and finite-maximum bounds and the full four-term maximum inequality | [CharacterTypeIBounds.lean](../TwinPrime/Analytic/CharacterTypeIBounds.lean) |
| Weighted Type I, low-term, and full explicit character mean with modulus one treated separately | [CharacterTypeIMean.lean](../TwinPrime/Analytic/CharacterTypeIMean.lean) |
| Eighth-root floor, reciprocal-square-root, and modulus power comparisons | [BVInternalCutoffs.lean](../TwinPrime/Analytic/BVInternalCutoffs.lean) |
| Explicit dyadic-depth and modulus logarithm comparisons for T≥256 | [BVLogComparisons.lean](../TwinPrime/Analytic/BVLogComparisons.lean) |
| Complete numerical mean-budget absorption with constant 5+16(2/log 2)^4 and six logarithms | [VaughanMeanParameters.lean](../TwinPrime/Analytic/VaughanMeanParameters.lean) |
| Exact bridge from the uncentered cumulative mean to the centered reciprocal-conductor tail | [ConductorMean.lean](../TwinPrime/Analytic/ConductorMean.lean) |
| Uniform centered small-conductor input bounds the clipped mass by R₀E | [SmallConductorMean.lean](../TwinPrime/Analytic/SmallConductorMean.lean) |
| Full proved maximal character mean, its actual centered large-conductor tail, and finite progression reduction | [VaughanMeanValue.lean](../TwinPrime/Analytic/VaughanMeanValue.lean) |
| Exact uniform centered pointwise and maximal small-conductor propositions, stated as definitions | [SiegelWalfisz.lean](../TwinPrime/Analytic/SiegelWalfisz.lean) |
| Uniform pointwise-to-maximal SW implication, including conductor one and short endpoints | [SiegelWalfiszMaximal.lean](../TwinPrime/Analytic/SiegelWalfiszMaximal.lean) |
| Logarithmic ceiling cutoff, exact endpoint range comparisons, and small-conductor budget | [BVSmallConductorGrowth.lean](../TwinPrime/Analytic/BVSmallConductorGrowth.lean) |
| Uniform asymptotic large-conductor absorption at T=2X+2 with explicit constant | [BVConductorGrowth.lean](../TwinPrime/Analytic/BVConductorGrowth.lean) |
| Complete maximal and pointwise SW implications to the exact quantified maximal BV statement | [BombieriVinogradovFromSW.lean](../TwinPrime/Analytic/BombieriVinogradovFromSW.lean) |
| Finite complex Dirichlet tails and ordered convergence on Re(s)>0; L-function identification and truncation on Re(s)>1 | [CharacterDirichletTail.lean](../TwinPrime/Analytic/CharacterDirichletTail.lean) |
| Conditional twin-prime endpoint from independent pointwise SW and B* | [ConditionalSiegelWalfisz.lean](../TwinPrime/ConditionalSiegelWalfisz.lean) |
| Locally uniform primitive character-series convergence, holomorphy, and actual L-function truncation on Re(s)>0 | [CharacterDirichletContinuation.lean](../TwinPrime/Analytic/CharacterDirichletContinuation.lean) |
| Uniform norm lower bound 1/4 for every character L-function on Re(s)≥2 | [LFunctionLowerBound.lean](../TwinPrime/Analytic/LFunctionLowerBound.lean) |
| Explicit primitive L-function growth and Cauchy bounds for all derivatives | [LFunctionGrowth.lean](../TwinPrime/Analytic/LFunctionGrowth.lean) |
| Local analytic zero-multiplicity bound with logarithmic conductor and height dependence | [LFunctionZeroCount.lean](../TwinPrime/Analytic/LFunctionZeroCount.lean) |
| Actual logarithmic-derivative series, zeta majorant, and three-four-one positivity on Re(s)>1 | [LFunctionLogDerivative.lean](../TwinPrime/Analytic/LFunctionLogDerivative.lean) |
| Sharp finite Euler bounds and pole-corrected zeta partial sums | [ZetaTruncation.lean](../TwinPrime/Analytic/ZetaTruncation.lean) |
| Regularized locally uniform convergence and actual pole-corrected zeta truncation on Re(s)>0 | [ZetaContinuation.lean](../TwinPrime/Analytic/ZetaContinuation.lean) |
| Normalized holomorphic logarithm on a ball, with its exact derivative | [HolomorphicLog.lean](../TwinPrime/Analytic/HolomorphicLog.lean) |
| Explicit logarithmic-derivative bound with constant 144 and logarithmic budget conversion | [AnalyticLogDerivativeBound.lean](../TwinPrime/Analytic/AnalyticLogDerivativeBound.lean) |
| Actual divisor polynomial and removable quotient, with factorization at every point | [HolomorphicZeroRemoval.lean](../TwinPrime/Analytic/HolomorphicZeroRemoval.lean) |
| Actual multiplicity count, polynomial norm bounds, and outer-disk quotient bound | [ZeroFactorBounds.lean](../TwinPrime/Analytic/ZeroFactorBounds.lean) |
| Exact logarithmic derivative of the divisor polynomial and a given zero-removal quotient | [ZeroFactorLogDerivative.lean](../TwinPrime/Analytic/ZeroFactorLogDerivative.lean) |
| Quantitative expansion over the actual zeros, with constant 144(1+log 5/log(6/5)) | [LocalLogDerivativeExpansion.lean](../TwinPrime/Analytic/LocalLogDerivativeExpansion.lean) |
| Primitive L-function expansion with logarithmic conductor and height bound | [LFunctionLocalExpansion.lean](../TwinPrime/Analytic/LFunctionLocalExpansion.lean) |
| Exact inducing logarithmic derivative and Euler correction bounded by log q | [LFunctionEulerCorrection.lean](../TwinPrime/Analytic/LFunctionEulerCorrection.lean) |
| Exact zeta pole identity, growth/derivative bounds, local nonvanishing, and regular-part bound 40 | [ZetaLogDerivative.lean](../TwinPrime/Analytic/ZetaLogDerivative.lean) |
| Actual L-function divisor support, positive multiplicities, and real-part contribution of a selected zero | [LFunctionZeroSigns.lean](../TwinPrime/Analytic/LFunctionZeroSigns.lean) |
| One-sided negative logarithmic-derivative bounds retaining a selected actual zero | [LFunctionZeroInequality.lean](../TwinPrime/Analytic/LFunctionZeroInequality.lean) |
| Numerical three-four-one contradiction and explicit parameter-range comparisons | [ZeroFreeArithmetic.lean](../TwinPrime/Analytic/ZeroFreeArithmetic.lean) |
| One-sided bound for every nonprincipal induced character, with the principal zeta term retained separately | [LFunctionInducedBound.lean](../TwinPrime/Analytic/LFunctionInducedBound.lean) |
| Regularized zeta expansion and logarithmic-derivative bound retaining the pole at every height | [ZetaLocalExpansion.lean](../TwinPrime/Analytic/ZetaLocalExpansion.lean) |
| Nonprincipal character conjugation and actual two-zero and conjugate-pair contributions | [LFunctionConjugateZeros.lean](../TwinPrime/Analytic/LFunctionConjugateZeros.lean) |
| Quantitative nonquadratic primitive L-function zero-free region | [LFunctionNonquadraticZeroFree.lean](../TwinPrime/Analytic/LFunctionNonquadraticZeroFree.lean) |
| Quadratic zero exclusion away from small heights, valid for every enlarged budget | [LFunctionQuadraticZeroFree.lean](../TwinPrime/Analytic/LFunctionQuadraticZeroFree.lean) |
| Per-character near-one uniqueness, actual order one, and reality for quadratic characters | [LFunctionNearOneZeros.lean](../TwinPrime/Analytic/LFunctionNearOneZeros.lean) |
| Full primitive L-function zero-free region with at most one simple real quadratic exception | [LFunctionZeroFreeRegion.lean](../TwinPrime/Analytic/LFunctionZeroFreeRegion.lean) |
| All-height zero-free region for regularized zeta, and actual zeta away from the pole | [ZetaZeroFree.lean](../TwinPrime/Analytic/ZetaZeroFree.lean) |
| Explicit logarithmic conductor/height widths, with primitive real/simple/unique and zeta nonvanishing corollaries | [ZeroFreeLogarithms.lean](../TwinPrime/Analytic/ZeroFreeLogarithms.lean) |
| Real-segment derivative bound and actual zero-to-value estimate with the coarse conductor budget | [LFunctionZeroValue.lean](../TwinPrime/Analytic/LFunctionZeroValue.lean) |
| Actual truncation at M=q gives logarithmic growth and a 10 exp(2)log²q derivative bound near one | [LFunctionNearOneGrowth.lean](../TwinPrime/Analytic/LFunctionNearOneGrowth.lean) |
| Actual zero-to-value bound with log²q loss, including the possible logarithmic-region zero | [LFunctionLogarithmicZeroValue.lean](../TwinPrime/Analytic/LFunctionLogarithmicZeroValue.lean) |
| Positive uniform L(1) and real-zero-gap constants for each finite conductor range | [LFunctionFiniteConductors.lean](../TwinPrime/Analytic/LFunctionFiniteConductors.lean) |
| Uniform arbitrary-power zero gap conditional on an explicit Siegel value lower bound | [SiegelZeroGap.lean](../TwinPrime/Analytic/SiegelZeroGap.lean) |
| Actual four-factor convolution is multiplicative and nonnegative, with every nonzero square coefficient at least one | [QuadraticProductCoefficients.lean](../TwinPrime/Analytic/QuadraticProductCoefficients.lean) |
| Actual four-factor L-series identity, entire regularization, nonzero value at one, and punctured residue limit | [QuadraticProductLSeries.lean](../TwinPrime/Analytic/QuadraticProductLSeries.lean) |
| Actual finite real/complex weighted sums, nonnegativity, monotonicity, and lower bound one | [QuadraticProductPartialSums.lean](../TwinPrime/Analytic/QuadraticProductPartialSums.lean) |
| Exact complex real-endpoint hyperbola identity and generic square-root convolution bound | [ComplexHyperbola.lean](../TwinPrime/Analytic/ComplexHyperbola.lean), [ConvolutionHyperbolaBound.lean](../TwinPrime/Analytic/ConvolutionHyperbolaBound.lean) |
| Nonprincipal complete-period cancellation and exact prefix reduction modulo q | [CharacterPeriodSum.lean](../TwinPrime/Analytic/CharacterPeriodSum.lean) |
| Absolute pair/triple coefficient masses with explicit logarithmic factors | [CharacterConvolutionMass.lean](../TwinPrime/Analytic/CharacterConvolutionMass.lean) |
| Actual pair/triple character cancellation and explicit three-quarter-power bound | [CharacterConvolutionCancellation.lean](../TwinPrime/Analytic/CharacterConvolutionCancellation.lean), [CharacterConvolutionPower.lean](../TwinPrime/Analytic/CharacterConvolutionPower.lean) |
| Power-bounded finite Dirichlet tails, locally uniform ordered limits, holomorphy, and analytic identification | [PowerDirichletTail.lean](../TwinPrime/Analytic/PowerDirichletTail.lean), [PowerDirichletContinuation.lean](../TwinPrime/Analytic/PowerDirichletContinuation.lean) |
| Actual triple L-function product identified on Re(s)>3/4, with reciprocal tail at one | [CharacterConvolutionContinuation.lean](../TwinPrime/Analytic/CharacterConvolutionContinuation.lean) |
| Reciprocal-power sums, exact zeta-convolution main-term decomposition, and floor/strip bounds | [ReciprocalPowerSums.lean](../TwinPrime/Analytic/ReciprocalPowerSums.lean), [ZetaConvolutionHyperbola.lean](../TwinPrime/Analytic/ZetaConvolutionHyperbola.lean), [ZetaConvolutionPowerBounds.lean](../TwinPrime/Analytic/ZetaConvolutionPowerBounds.lean) |
| Four-fifths-power summatory error about the actual ordered limit and actual four-factor residue | [ZetaConvolutionAsymptotic.lean](../TwinPrime/Analytic/ZetaConvolutionAsymptotic.lean), [CharacterConvolutionAsymptotic.lean](../TwinPrime/Analytic/CharacterConvolutionAsymptotic.lean) |
| Positive pole term and quantitative real zeta truncation below one | [ZetaRealTruncation.lean](../TwinPrime/Analytic/ZetaRealTruncation.lean) |
| Exact centered coefficients, nine-tenths-power prefix bound, entire pole cancellation, and ordered continuation | [QuadraticCenteredCoefficients.lean](../TwinPrime/Analytic/QuadraticCenteredCoefficients.lean), [QuadraticCenteredFunction.lean](../TwinPrime/Analytic/QuadraticCenteredFunction.lean), [QuadraticCenteredContinuation.lean](../TwinPrime/Analytic/QuadraticCenteredContinuation.lean) |
| Explicit natural residue cutoff, half-error budget, and fortieth-power conductor bound | [ResidueCutoff.lean](../TwinPrime/Analytic/ResidueCutoff.lean), [ResidueConductorBound.lean](../TwinPrime/Analytic/ResidueConductorBound.lean) |
| Actual weighted residue comparison under a nonpositive product real part, including actual zeros | [QuadraticResidueComparison.lean](../TwinPrime/Analytic/QuadraticResidueComparison.lean) |
| Ordered nonprincipal character continuation and the imprimitive bound \|Lχ(1)\|≤5+log q | [LFunctionPeriodBound.lean](../TwinPrime/Analytic/LFunctionPeriodBound.lean) |
| Logarithmic inducing multiplier bound, exact zero preservation, and positive-half-plane zero equivalence | [LFunctionInducedValue.lean](../TwinPrime/Analytic/LFunctionInducedValue.lean) |
| Primitive conductor, nonprincipal, quadratic, and distinctness transport to the common product modulus | [CharacterCommonLevel.lean](../TwinPrime/Analytic/CharacterCommonLevel.lean) |
| Actual real signs and transport of a primitive quadratic interval exclusion to induced characters | [LFunctionRealSign.lean](../TwinPrime/Analytic/LFunctionRealSign.lean), [QuadraticNoZeroTransport.lean](../TwinPrime/Analytic/QuadraticNoZeroTransport.lean) |
| Explicit primitive nonprincipal quadratic character of conductor four | [QuadraticAuxiliaryCharacter.lean](../TwinPrime/Analytic/QuadraticAuxiliaryCharacter.lean) |
| Auxiliary value comparison, logarithmic power absorption, and finite/cofinal conductor assembly | [QuadraticAuxiliaryComparison.lean](../TwinPrime/Analytic/QuadraticAuxiliaryComparison.lean), [SiegelValuePower.lean](../TwinPrime/Analytic/SiegelValuePower.lean), [SiegelValueFromComparison.lean](../TwinPrime/Analytic/SiegelValueFromComparison.lean) |
| Independent uniform Siegel value bound, with both branches of the auxiliary-zero dichotomy discharged | [SiegelValue.lean](../TwinPrime/Analytic/SiegelValue.lean) |
| Uniform arbitrary-power exceptional-zero gap without a supplied value estimate | [SiegelZeroGapUnconditional.lean](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean) |
| Radius-17/16 local expansions with constant 288, actual divisor multiplicities, and principal zero count | [WideAnalyticLogDerivativeBound.lean](../TwinPrime/Analytic/WideAnalyticLogDerivativeBound.lean), [WideLocalLogDerivativeExpansion.lean](../TwinPrime/Analytic/WideLocalLogDerivativeExpansion.lean), [WideLFunctionLocalExpansion.lean](../TwinPrime/Analytic/WideLFunctionLocalExpansion.lean), [WideZetaLocalExpansion.lean](../TwinPrime/Analytic/WideZetaLocalExpansion.lean) |
| Actual uniform zero-free rectangles, zero-sum norm estimates, and full complex strip bounds left of one | [ZeroFreeRectangle.lean](../TwinPrime/Analytic/ZeroFreeRectangle.lean), [ZeroSumNorm.lean](../TwinPrime/Analytic/ZeroSumNorm.lean), [LogDerivativeStrip.lean](../TwinPrime/Analytic/LogDerivativeStrip.lean) |
| Exact ramp and principal pole Mellin transforms, vertical integrability, and actual inverses | [MellinRampKernel.lean](../TwinPrime/Analytic/MellinRampKernel.lean), [MellinPoleKernel.lean](../TwinPrime/Analytic/MellinPoleKernel.lean) |
| Justified Dirichlet-series interchange and actual smoothed Mangoldt-character inversion, including conductor one | [MangoldtMellinInversion.lean](../TwinPrime/Analytic/MangoldtMellinInversion.lean) |
| Exact finite unsmoothing and short-interval Mangoldt error at most (h+1)log(x+h) | [SmoothedPartialSum.lean](../TwinPrime/Analytic/SmoothedPartialSum.lean) |
| Both inverse-integral tails, finite rectangle shift, and horizontal and vertical norm estimates | [MellinTruncation.lean](../TwinPrime/Analytic/MellinTruncation.lean), [MellinRectangle.lean](../TwinPrime/Analytic/MellinRectangle.lean) |
| Uniform polylogarithmic-conductor evaluation width and O(log x) primitive norm budget | [SiegelWalfiszStripWidth.lean](../TwinPrime/Analytic/SiegelWalfiszStripWidth.lean), [SiegelWalfiszStripBudget.lean](../TwinPrime/Analytic/SiegelWalfiszStripBudget.lean) |
| Actual uniform smoothed primitive-character contour estimate, with no supplied zero-free or distribution premise | [SmoothedMangoldtContour.lean](../TwinPrime/Analytic/SmoothedMangoldtContour.lean) |
| Actual principal regularized inverse, both tails, and centered contour estimate | [PrincipalMellinInversion.lean](../TwinPrime/Analytic/PrincipalMellinInversion.lean), [SmoothedPrincipalContour.lean](../TwinPrime/Analytic/SmoothedPrincipalContour.lean) |
| Principal bounds at the common width and uniform arbitrary-logarithmic error absorption | [PrincipalStripParameters.lean](../TwinPrime/Analytic/PrincipalStripParameters.lean), [ContourParameterBounds.lean](../TwinPrime/Analytic/ContourParameterBounds.lean), [ContourBudgetAbsorption.lean](../TwinPrime/Analytic/ContourBudgetAbsorption.lean) |
| Independent centered smoothed Siegel–Walfisz, including conductor one | [SmoothedSiegelWalfisz.lean](../TwinPrime/Analytic/SmoothedSiegelWalfisz.lean) |
| Centered finite differences, all endpoint errors, and the exact sharp-sum Siegel–Walfisz theorem | [CenteredUnsmoothing.lean](../TwinPrime/Analytic/CenteredUnsmoothing.lean), [SiegelWalfiszTheorem.lean](../TwinPrime/Analytic/SiegelWalfiszTheorem.lean) |
| Maximal SW, exact BV, and quantitative Mertens with no distribution hypotheses | [ClassicalDistribution.lean](../TwinPrime/Analytic/ClassicalDistribution.lean) |
| Twin-prime implication with only the cofinal signed estimate B* assumed | [ConditionalSignedBilinear.lean](../TwinPrime/ConditionalSignedBilinear.lean) |

The prime-power estimate is stronger than the plan's elementary logarithmic
counting estimate. It uses Mathlib's already proved Chebyshev bound on ψ−θ.
Thus the final three-estimate endpoint has no remaining prime-power hypothesis.
The exact algebraic identity and A/K/B definitions use signed arithmetic sums;
in particular, B is not defined to make the desired inequality true.

## Milestone status

| Milestone | Status |
|---|---|
| M0: corrections and computational repairs | Implemented; original numerical tables preserved. |
| M1: finite endpoint and decomposition | Implemented, including the general finite totient identity (Q) and coefficient bounds. |
| M2: conditional theorem | Implemented, including the fixed cutoffs and existing twin constant; prime-power input discharged. |
| M3: classical analytic side | **Implemented.** Independent centered pointwise SW now follows from actual inversion, the principal contour, uniform error absorption, and centered finite differences. Its maximalization supplies the exact BV input, and BV supplies Mertens and all the Möbius/totient, weighted progression, shared-prime, and Euler-product bridges for (A) and (K). The [source-to-lemma map](CLASSICAL_DISTRIBUTION_THEOREM.md) records the completed chain. |
| M4: new estimate | The exact O(log X) active box family, summed diagonal saving, large-gcd removals, and large-prime-square removal are formalized. The dispersion large-gcd root budget is O(X/log^2 X). The original signed sum differs from its simultaneous small-gcd/no-large-square residual by O(X/log^7 X). Every squarefree input survives, and the remaining signed sum and small-gcd dispersion budget are unestimated. The source audits identify unsupported transfers. B* remains open. **These range estimates do not close the total budget.** |
| M5: alternatives | Finite rough-parity identity and conditional endpoint implemented. A specific Chen weight has now been evaluated, with a rigorously negative lower-bound-minus-leakage margin. The circle-method interface remains a paper alternative. No alternative has been promoted as resolving its new sign estimate. |
| M6: unconditional proof | **Not completed.** No unconditional `twin_prime_conjecture` theorem is present. |

## Verification and provenance

Source baseline: `5cf66a63bbc33b36f3c8d90373d2f6cce108f72a`.
Lean: `4.32.0`, compiler commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Mathlib manifest revision: `81a5d257c8e410db227a6665ed08f64fea08e997`.
Later dated results extend this historical source baseline.

Run the root build and [Axioms.lean](../scripts/Axioms.lean); the latter also
prints the conditional theorem's type. Both type inspection and axiom inspection
are necessary. The project does not use proof holes or new axioms for these results.

The latest full `lake build` passed, reporting 8936 jobs. The integrated
`lake env lean scripts/Axioms.lean` audit passed for all 1396 selected declarations,
using only `propext`, `Classical.choice`, and `Quot.sound`. The printed B*
endpoint retains that signed hypothesis. The alternative logarithmic-gain
endpoint retains its displayed signed gain and numerical cutoff assumptions.
The printed SW,
BV, and Mertens theorem types have no distribution arguments. Earlier
endpoints retaining SW or BV remain available as general implications. The separate
type for `MaximalBombieriVinogradov.mertensLogSix` has only BV as its input.
Separate mathematical reviews
found no mismatch in the hyperbola normalization, harmonic boundary constant,
dominated-convergence majorants, exceptional removal, rough-parity identity,
or dispersion signs, cutoffs, and diagonal constants. The assembled
BV-to-Mertens chain was independently reviewed for signs, real endpoints,
local boundedness, and hypothesis scope, in addition to its Lean verification.
The finite BV foundations were separately reviewed for principal centering,
primitive multiplicities, both maxima, composite-modulus Gauss normalization,
and uniform absorption of the replacement error.
The conductor and large-sieve chain was independently reviewed for its exact
multiplicities, rational spacing, phase and inverse conventions, Gram duality,
empty ranges, and explicit harmonic loss. The checked primitive-character
large-sieve type has no distribution or maximal-mean-value argument.
The new interval cancellation, adaptive dyadic second moments, and exact
product-cutoff staircase were checked independently for constants, endpoint
choices, no reuse of cover blocks, and the final natural interval boundaries.
The maximal first-moment and full finite Type II chains were independently
reviewed for the exact level decomposition, fixed versus adaptive intervals,
strict support masks, low von Mangoldt term, inactive-box vanishing,
half-cutoff polynomial, and both factors of D². No hidden maximal or
distribution hypothesis was found in their final types.
The full Vaughan mean and centered conductor tail were independently reviewed
for the Type I support and natural quotients, exact character counting,
conductor-one treatment, actual finite maxima, eighth-root floor comparisons,
six logarithmic factors, and fixed-in-T coefficients in conductor summation.
Their final types have only numerical range conditions. The finite progression
criterion retains its uniform small-conductor estimate as an explicit hypothesis,
and covers Q=0 and Q<R₀ through the clipped small range and conditional tail.
The final SW-to-BV chain was independently reviewed for its ceiling cutoff,
error and conductor exponents, actual T=2X+2 endpoint, uniform thresholds,
and both empty-range cases. Pointwise-to-maximal SW retains conductor one
and handles every short endpoint without a distribution estimate. The
Dirichlet-tail review checked complex-power variation, anchored finite Abel
boundaries, and ordered convergence. Positive-half-plane identification now
uses proved local uniformity and analytic uniqueness. The actual L-function
truncation type requires primitive q>1 and Re(s)>0; the pole-corrected zeta
type requires Re(s)>0 and s≠1. Its regularized version includes s=1 with
value one, and only eventually positive truncations are used for holomorphy.
The center lower bound, Cauchy derivative estimates, and Jensen bound were
reviewed for all constants, disk margins, and zero multiplicities. The
three-four-one proof retains the full zeta term, character square, double
phase, and signs. No distribution hypothesis occurs in these analytic
theorems. No circular BV or Mertens input enters the SW-to-BV implication.
The normalized logarithm, exact zero removal, polynomial and quotient bounds,
actual-divisor logarithmic derivative, Jensen budget conversion, and primitive
specialization were independently reviewed for their domains, multiplicities,
constants, and evaluation-point nonvanishing. The Euler correction review
retained all prime factors and the change of sign for negative logarithmic
derivatives. The regularized zeta bound includes the pole, while the raw
identity excludes it. The selected-zero inequality retains its actual zero
hypothesis and the range 1<σ≤9/8. The scalar contradictions are now applied
to both character-square cases and to zeta. The complete regions, near-one
actual order one, per-character uniqueness, and logarithmic-width comparisons
were independently reviewed for their branch boundaries, reciprocal directions,
and principal poles. The new character-convolution chain was independently
reviewed for complete-period cancellation, real floor endpoints, absolute
coefficient masses, all-N prefix bounds, the ordered rather than absolute
convergence domain, and identification of the actual three L(1) values.
The four-factor error retains all floor, overlap and tail terms; their
constants sum to 1+25C with C=130q². All 85 public theorems from that
convolution checkpoint remain in the integrated axiom report. Their actual-character types retain only
the stated nonprincipal and numerical range restrictions, with no
unproved distribution, mass, growth or residue-identification premise.
The preceding 84-theorem checkpoint was separately reviewed for centered
coefficient identities, pole cancellation, quantitative real tails, residue
signs, exact inducing factors, common-level conductor distinctions, and the
auxiliary character. The final dichotomy fixes its auxiliary data before
quantifying over target characters. Its power absorption includes q₀^(−ε),
and its finite minimum covers every q≤q₀. The printed uniform value and
zero-gap types have no supplied value-bound hypothesis. Every one of the
18 new modules passed standalone checking without linter warnings, and
all 84 public theorems occur in the integrated audit.
The preceding checkpoint added 102 public theorems in 16 modules. Every new
module passed standalone checking without warnings and the full root build.
The audit includes every new public theorem. Printed types confirm that
actual Mangoldt inversion includes conductor one and that the uniform
primitive smoothed contour estimate has no supplied value, zero-free,
inversion, or distribution premise. The primitive strip-budget constant
is uniform over the polylogarithmic conductor family. Source review covered the
series interchange, contour orientation and normalization, both tail
terms, zero separation and multiplicity, width halvings, and finite floor
endpoints. The completed SW checkpoint added 43 public theorems in ten modules,
completing the principal contour assembly, common-width comparison,
uniform three-error absorption, centered smoothed SW, and exact sharp SW.
The finite difference uses h=x/(log x)^(A+2) and smoothed exponent 2A+4;
its short-interval and principal errors are retained explicitly. The common
threshold works at x+h because x+h≥x, and the conductor bound transfers
monotonically. Source review covered these steps and the actual endpoint types.
All 43 new public theorems occur in the integrated audit and all ten
modules compile without new warnings. This checkpoint has implementation-source review and Lean verification, without a separate independent mathematical
review of the assembled SW theorem. The classical B* endpoint takes only B*.
The preceding checkpoint added 62 public theorems in eight modules for the
exact dispersion partition, summed diagonal, large-gcd off-diagonal,
logarithmic cutoff, and original-factor gcd reduction. Every new theorem
is in the integrated axiom audit, and every new module compiles without
warnings. Independent source review checked right-closed endpoints,
growing cardinalities, both ordered off-diagonal orientations, exact
signed coefficients, and both different gcd restrictions. The original
factor split includes d=r. No estimate for the remaining small-gcd sum
or root budget appears as a proved assertion.
The preceding checkpoint added 45 public theorems in four modules. The strict
product band has at most three exponent levels, and zero-entry transport
identifies each full sum with its restricted sum. Independent review checked
the count, improved logarithmic losses, two square-factor allocations,
hyperbola count, and factorwise absolute mass. The simultaneous residual
uses that absolute mass on the overlapping restriction; it never restricts
a signed-tail estimate without justification. Its printed difference bound
is (24*(2/log 2)+8)/log^7(4X+4), and its normalized difference tends to zero.
Every squarefree input survives the restrictions. All 45 theorems are in
the audit, and the four new modules compile without warnings. The separate
[centering review](DISPERSION_CENTERING_REVIEW.md) is a paper calculation,
with the assembled center estimate unformalized and the variance unproved.
The preceding checkpoint added 52 public theorems in seven modules for the
[prime-beta reduction](BILINEAR_PRIME_BETA_ROUTE.md). Independent review
checked the exact low-divisor restriction, repeated prime factors, uniform
reciprocal tail, hyperbola count and constant four, arbitrary left cutoff,
all fixed logarithmic powers, and exact product grouping. All 52 theorems
are audited. All seven modules compile without warnings. This supplies
an absolute o(X) replacement error and exact signed identities, not a
lower bound for the surviving weighted prime sum.
The latest checkpoint adds 38 public theorems in seven modules for the
[signed right-cutoff change](CUTOFF_SHIFT_ROUTE.md). It proves complete
mixed-cutoff Type I decay below every fixed product exponent a<1/2,
using the independently proved BV and Mertens inputs. The quarter-cutoff
example and its prime-only beta replacement are unconditional o(X)
difference limits. Independent review checked the exact sign, shared-prime
correction, both modulus parities, growing endpoints and product ranges,
and the retained m_U coefficient. All 38 theorems are audited and the seven
modules compile without warnings. The result controls a signed aggregate;
it supplies no absolute mass bound for the removed band or positive B* margin.
The latest quantitative refinement adds 17 public theorems in seven modules;
see [exact finite centering](CLASSICAL_CENTER_PRECISION.md). It keeps J=XS+FM-XQ
and proves |W2-(B+J)|=o(X/log^k X) for every fixed natural k below a fixed
product exponent 1/2. Independent review checked all signs, the constants
8 and 3, the natural exponent k=0, the full even-modulus budgets, the exact
centered cutoff change, and both unconditional cutoff applications. The
quarter prime-beta replacement preserves this precision. The alternative
endpoint still assumes a cofinal cX/log^k X signed gain. No such gain is proved.
The preceding middle-prime sieve checkpoint proved the actual finite
class estimate, exact modulus multiplicities,
the full weighted progression-error limit, and the denominator asymptotic
S(z)/log z->1/C. The correction has proved absolute convergence and total
mass 1/C; harmonic dominated convergence requires no extra logarithmic
moment. Uniform substitution into growing sieve families retains the full
weighted error. The current checkpoint supplies the specific integer
thresholds, their uniform logarithmic rounding, centered Abel summation,
proper-prime-power and totient replacements, and the actual prime main
sum. The fixed level a=49999/100000 has an exact rational certificate
below 0.263, so the complete eventual class bound now has no supplied
arithmetic hypothesis. The printed endpoint type confirms this scope.
All 66 public theorems added in this completion occur in the integrated
audit; the eleven additional modules compile without warnings.

This completes the class estimate, while the certified positive margin
in the [total budget](SIGNED_TOTAL_BUDGET.md) remains zero. The remaining
signed R must be below 0.737 C X with fixed positive cofinal slack after
the full residual. The Buchstab and scale-averaged correlation assessments
are paper analyses and provide no such improvement. They do not justify
substantial additional formalization at this checkpoint.
A source scan covers
281 project Lean files, including the root import file, and finds no proof holes, project axiom declarations,
`native_decide`, `unsafe`, or `implemented_by`. Existing linter warnings remain
in older sieve/parity files; no proof error was reported.

The computational regression suites contain 7 twin-sieve tests, 6 parity tests,
and 11 Python correlation/sign tests. The latter include 8,000 exact finite
Vaughan checks and independent coefficient checks. The focused
`compute/type_i_switch_check.py` also passes exact integer logarithm-coefficient
checks of the finite Type I switch and positive off-diagonal witness.
The separate [smoothing diagnostic](../compute/smoothing_check.py) passes
4,800 exact averaging and 9,600 exact prime-beta convolution checks, plus
the 381-to-383 and 1011-to-1013 negative-change witnesses with exact finite
compensation. The latter uses the exact primary and quarter cutoffs.
These are finite checks supporting the paper audit, not asymptotic evidence.
The local [correlation summary](../compute/correlation_results/2026-09-04/summary.json)
and [factor boxes](../compute/correlation_results/2026-09-04/boxes.csv) record
script/interpreter hashes, the dirty source state, precision, and exact coefficient
hashes. Binary64 displayed values are diagnostics, not certified analytic bounds.
See [compute/CORRELATION.md](../compute/CORRELATION.md) for reproduction commands.

The repaired endpoint returns π₂(5)=2 under final limits 5 and 6, including the
same reciprocal contribution. Zero-denominator parity ratios are explicit.
The existing powers-of-ten twin tables use even endpoints, and the saved parity
table has no zero odd counts; these fixes require no changes to those entries.
The full large enumerations were not rerun. Pre-existing release binaries are
preserved; verified repaired binaries are under each crate's `target/verified`.

## Limits of the new signed calculations

[BILINEAR_SIGN_REVIEW.md](BILINEAR_SIGN_REVIEW.md) contains a paper absolute-mass
bound with exponent 3/4. The Lean library now proves the sufficient removal
estimate `abs(B−Bprime) ≤ (2/log2)Y^(1/2)log³Y + 32Y^(5/6)log²Y = o(X)`,
where Y=2X+2 and Bprime is restricted to non-prime-powers n with prime n+2.
This uses a different, simpler divisor bound. The remaining composites include
both coefficient signs; their aggregate is not bounded to the margin in B*.

[FAILED_APPROACHES.md](FAILED_APPROACHES.md) records precise counterexamples,
including a three-point switch preserving finite Type I moments. The switched
weights are a finite model, not the actual von Mangoldt sequence and not a
model satisfying the full asymptotic BV input. The example rejects the stated
finite-moment shortcut only; it is not an impossibility proof for all approaches.

[ASYMPTOTIC_SIEVE_REVIEW.md](ASYMPTOTIC_SIEVE_REVIEW.md) gives the complete
Friedlander–Iwaniec application table and the first unavailable distribution
range. Its bilinear hypothesis is not silently identified with PLAN's B*.

[CHEN_WEIGHT_REVIEW.md](CHEN_WEIGHT_REVIEW.md) selects an actual Chen weight,
keeps its square correction and exact interval, and evaluates its compatible
mass and leakage bounds. Their coefficient difference is
`−4 log 2−2J−4<0`. The review also exhibits a zero-twin assignment satisfying
the listed aggregate inequalities, without claiming a model of actual primes
or of the full progression data.
