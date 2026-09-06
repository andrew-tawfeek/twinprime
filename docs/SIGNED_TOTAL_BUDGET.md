# Total signed budget after the middle-prime bound

Checkpoint: 2026-09-05. The ultimate target remains a proof of twin-prime
infinitude. This ledger measures an improvement by a positive margin in
the complete inequality below. A separate class bound or a conditional
reduction is not a resolution of the conjecture.

## 1. Exact quantities and every residual

Set U=floor(X^(1/5)), W=floor(X^(21/100)), C=2 C2>0, and
L=log(2X+2). Use the unrestricted smooth/rough partition from
[the middle-prime proof](MIDDLE_PRIME_SIEVE_BOUND.md): n=ab, with a
W-smooth and b W-rough. There is no additional squarefree or gcd cut.
Write T for the complete middle-prime mass, N_rough for the rough
composite loss, and N_comp and P_comp for the negative and positive
composite-smooth-part masses. Define

\[
 R=N_{\rm rough}+N_{\rm comp}-P_{\rm comp},\qquad
 B'=P_{\rm comp}-N_{\rm rough}-T-N_{\rm comp}=-T-R.
\]

The finite center is the actual
[classicalCorrelationCenter](../TwinPrime/Analytic/ClassicalCorrelationCenter.lean)
J=XS(U)+F(U)M(U,X)-XQ(U,W). Let B be the original bilinear sum at
these same cutoffs. Put

\[
 r_{\rm cl}=W_2-(B+J),\qquad r_\beta=B-B'.
\]

The genuine weighted twin sum is exactly Q_tw=W2-Epp, by
[Correlation](../TwinPrime/Correlation.lean). Therefore

\[
 \boxed{Q_{\rm tw}=J-T-R+r_{\rm cl}+r_\beta-E_{\rm pp}.}       \tag{1}
\]

No main term, composite contribution, or prime-power term is omitted.
Concrete nonnegative budgets for the two signed errors are

\[
 \begin{split}
 D_{\rm cl}(X)
 &=8L\sum_{1\le d\le UW}E_d(2X+2)
   +3(UW+1)L\,\mathrm{evenProgressionBound}(X),\\
 D_\beta(X)&=|B-B'|
   \le K X\log^2(4X+4)/\sqrt W,
 \end{split}                                                 \tag{2}
\]

where K is a fixed positive constant from the
[prime-beta replacement](../TwinPrime/Analytic/PrimeBetaReduction.lean).
The finite center theorem gives |r_cl|<=D_cl, and |r_beta|=D_beta.
At these powers UW<=X^(41/100), the existing distribution and even-modulus
estimates give D_cl=o(X/log^k X) for every fixed natural k. The same
precision follows for D_beta from its power saving and for Epp from
[PrimePowerLogPrecision](../TwinPrime/Analytic/PrimePowerLogPrecision.lean).

For a linear budget define

\[
 E_{\rm tot}=D_{\rm cl}+D_\beta+E_{\rm pp}+|J-CX|=o(X).
\]

The last term uses the established classical main-term limits. It is
retained as its actual finite value; no arbitrary logarithmic rate for
|J-CX| is asserted. The Selberg remainder used to bound T is already
absorbed in the eventual class bound and is not counted a second time.

## 2. What the class bound changes, and what it does not

The middle-prime estimate gives T<=0.263 C X eventually. Consequently

\[
 \boxed{Q_{\rm tw}\ge0.737CX-R-E_{\rm tot}.}                  \tag{3}
\]

A sufficient new estimate is, for a fixed delta>0 on cofinally many
scales,

\[
 R\le(0.737-\delta)CX,
 \quad\text{with }E_{\rm tot}\le\tfrac12\delta CX
 \text{ eventually}.                                       \tag{4}
\]

This would give a positive genuine twin sum. It has not been proved.
For a smaller logarithmic gain, use (1) with exact J and the explicit
D_cl+D_beta+Epp; replacing J by CX with only an o(X) error is inadequate.

The present budget is:

| Quantity | Certified information | Consequence for the final margin |
|---|---|---|
| Main center | J=CX+o(X) | Available leading mass is C X. |
| Middle-prime loss | T<=0.263 C X eventually | Leaves the conditional allowance in (3). |
| Remaining signed loss | R=N_rough+N_comp-P_comp | No independent bound below 0.737 C X is known here. |
| Total signed loss | T+R<=C X+o(X), from (1) and Q_tw>=0 | The certified positive margin is zero. |
| Explicit residuals | E_tot=o(X) | They preserve a fixed positive margin, but do not create one. |

Thus the new class estimate isolates a loss, but does not reduce the best
certified leading coefficient for the total loss below one. In particular,
it must not be reported as a gain of 0.263 C X in the final inequality.
The upper bound for T is not a lower bound for T and cannot be subtracted
from a bound for T+R to improve R.

## 3. Positive composite mass cannot be discarded

Let P be the actual prime-input sum
sum_(X<n<=2X,n prime) log(n)Lambda(n+2), and put H=P+N_rough.
The [rough-composite sieve calculation](ROUGH_COMPOSITE_SIEVE_BOUND.md)
gives the following paper consequence of the cited lower linear sieve;
this lower bound is not a Lean export:

\[
 4C\log(29/21)\le\liminf H/X\le\limsup H/X\le4C.
\]

Set Z=W2-P. Then 0<=Z<=Epp, and (1)'s underlying exact identity gives

\[
 P_{\rm comp}-N_{\rm comp}
   =H+T-J+Z-r_{\rm cl}-r_\beta.                             \tag{5}
\]

Hence favorable composite mass is already of leading size:

\[
 P_{\rm comp}-N_{\rm comp}
 \ge (4\log(29/21)-1)CX+T-o(X).
\]

The coefficient is about 0.29109. This observation does not improve (3):
combining (5) with H=P+N_rough recovers the identity
R+T=J-P-Z+r_cl+r_beta. Using the independent sieve upper and lower
bounds separately is weaker. No positive margin may be counted twice by
reusing these same correlated masses.

## 4. Criterion for further formalization

Before substantial additional Lean work, a proposed analytic step must
show on paper its new bound for R, or directly for T+R, including every
new restricted range, endpoint, replacement error and signed contribution.
For a bound R<=rho C X+E_new, the displayed leading margin is
0.737-rho and the residual is E_tot+E_new. If that expression has no
proved positive cofinal margin, it is not a sufficient improvement.
An estimate merely equivalent to positivity of Q_tw is a restatement,
not new arithmetic evidence.

The next investigation must address the signed aggregate and retain
P_comp. Completing classical identities or increasing the number of
formal declarations is not the progress metric for this remaining step.

## 5. A quantitative test of least-prime Buchstab decomposition

This paper test starts from H, uses full log(n) weights, and removes the
inputs whose least prime lies between X^(21/100) and X^w. The exact
least-prime partition is disjoint. Replacing rough beta'_W(n) by log(n)
has the explicit defect bound in
[the rough-composite note](ROUGH_COMPOSITE_SIEVE_BOUND.md), at most
2K X log(2X+2)/W. Omitting the prime two costs at most log(2X+2) in the
unweighted shifted-Mangoldt sum and O(log^2 X) after its log weight.
These residuals are o(X) and do not alter the following leading constants.

For 21/100<w<1/4, the standard upper linear sieve charges the removed
least-prime strips at most

\[
 2CX\int_{21/100}^{w}\frac{dt}{t(1/2-t)}+o(X)
 =4CX\log\frac{w(29/100)}{(21/100)(1/2-w)}+o(X).
\]

Here the sequence inside the strip q has main mass X/phi(q), level D/q,
and sieve threshold q. The parameter (1/2-t)/t lies between one and two;
the upper-sieve main factor is 2 exp(gamma)/s. Supported moduli qd<=D
retain their progression errors, which BV absorbs. The product normalization
is the same C as in the middle-prime calculation. One can use a fixed
power level below one half first and then take that exponent up to one
half; no uniform distribution assertion at the limiting exponent is assumed.

The available lower mass before removing these strips is
4C log(29/21) X+o(X). Subtracting the charged strips leaves exactly

\[
 4CX\log\frac{1/2-w}{w}+o(X).
\]

This lower budget tends to zero as w increases to 1/4. The subsequent
strips are still nonnegative losses, so this use of ordinary upper and
lower linear sieves cannot supply a positive lower bound after they are
removed. The calculation matches the vanishing of the standard lower-sieve
function for s<=2. The precise sieve functions are in
[Tao, Theorem 2 and equations (10)–(11)](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/).
Retaining P_comp via (5) only restores the same complete first moment;
it does not add an independent saving.

For clarity, the aggregate bounds established so far are compatible with
the following values in units of C X:

| P | T | N_rough | N_comp | P_comp | R | T+R |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1/4 | 2 | 0 | 5/4 | 3/4 | 1 |

They obey T<=0.263, the upper and lower bounds on H, and the favorable
composite-mass inequality, while the final margin is zero. This is a
counterexample to deriving a gain from these aggregate inequalities,
not a model of the actual prime sequence.

This candidate therefore does not justify substantial additional
formalization. A different mechanism must supply new information about
the signed aggregate or the prime/composite distinction on the surviving
rough support.

## 6. A different mechanism: scale averages and rough parity modes

Logarithmic averaging in scale is compatible with the cofinal target.
For positive integers Z define H_Z=sum_(Z<=X<=Z^2) 1/X and

\[
 \langle R\rangle_Z=\frac1{C H_Z}
      \sum_{Z\le X\le Z^2}\frac{R(X)}{X^2}.
\]

Averaging (3) with the same positive weights retains the full budget.
The averaged E_tot/(C X) tends to zero. An independent bound
<R>_(Z_j)<=0.737-eta for a fixed eta>0 and unbounded Z_j would therefore
give positive averaged genuine twin mass and at least one good integer
scale in each such window. This is a sufficient new estimate, not one
proved by averaging the present inequalities.

There is an exact obstruction to simply inserting a multiplicative
correlation theorem. If R(X)=sum_(X<n<=2X) r_X(n)Lambda(n+2), interchanging
the finite sums gives

\[
 \sum_{Z\le X\le Z^2}\frac{R(X)}{X^2}
 =\sum_n\Lambda(n+2)
    \sum_{\substack{Z\le X\le Z^2\\X<n\le2X}}
       \frac{r_X(n)}{X^2}.
\]

The inner coefficient still depends on the moving cutoffs, the truncated
Moebius sum m_U(a), and the signed composite mass. Freezing those
coefficients would introduce a new error which has not been bounded.

A separate exact observation makes a direct prime-selector approach
worth distinguishing from that failed insertion. Eventually W<X and
W^5>2X+2. Every W-rough integer m with W<m<=2X+2 then has
1<=Omega(m)<=4. Put g_j(m)=1_(m W-rough) i^(j Omega(m)) for j=0,1,2,3.
For fixed W these are 1-bounded multiplicative functions. On the stated
domain, which contains both n and n+2 from the dyadic block,

\[
 1_{m\text{ prime}}=\frac14\sum_{j=0}^3 i^{-j}g_j(m).
\]

This identity is restricted to W<m<=2X+2; it is not valid for primes
m<=W. Multiplying the two selectors gives an exact expression for Q_tw in
sixteen correlations, with their phases and the full weights
log(n)log(n+2) retained. Thus rough support itself is not outside every
multiplicative encoding. This approach would bypass the partition by R,
but it still has to prove a positive value for the complete phase sum.

The inspected logarithmic correlation theorem gives absolute error
epsilon log(omega), with the threshold depending on epsilon. Its finite
formulation permits the bounded multiplicative functions to vary with
the scale. It requires pretentious distance at least A against every
character of period at most A and twist |t|<=Ax. For this family, every
such distance is at least sum_(p<=min(W,x)) 1/p, since g_j(p)=0 there.
Thus the hypothesis holds uniformly for every fixed A as W and x tend
to infinity. No unproved qualitative nonpretentiousness hypothesis is
being used. The theorem does not give the relative control at unweighted scale
X/log^2 X needed to detect a positive linear weighted twin sum; no
prime-pair asymptotic is being assumed. On windows with omega<=sqrt(X),
the two logarithmic weights are comparable to log^2 X, so the needed
unweighted correlation accuracy is at the scale log(omega)/log^2 X,
not merely o(log(omega)). Comparability of these positive weights would
transfer a positive lower bound for the complete nonnegative selector.
For the individual complex modes, transferring cancellation to the
weighted sums instead requires uniform partial-sum or Abel estimates;
comparability alone does not supply them.
[Tao, Theorems 1.2–1.3 and Remark 1.4](https://arxiv.org/pdf/1509.05422).

The nonnegative g_0g_0 rough-pair contribution is itself compatible with
an absolute o(log(omega)) bound. No cited result makes all nonzero modes
negligible at the sparse scale; doing so would be an additional unproved
correlation estimate. A successful argument must retain and combine
every mode at the needed precision.

The quantitative fixed-shift theorem also applies at an absolute scale:
its distance M is at least sum_(p<=W) 1/p, so exp(M) is bounded below by
a constant times log W. Part (ii) yields normalized error O(Lcal^(-c))
outside a set of logarithmic density O(Lcal^(-c)), where Lcal<=log X
and c is a small fixed positive constant. This does not give the required
log^(-2) X precision. Its separate main-term case (i) requires g_1(p)=1
on a specified intermediate prime range, whereas the present functions
vanish throughout that range for large X. It cannot supply the missing
main terms. The direct selector avoids the growing-affine-factor issue
of the [earlier audit](SHIFTED_MOBIUS_INPUT_AUDIT.md), but leaves this
relative-error obstruction.
[Tao–Teravainen, Theorem 3.1 and Remark 3.2](https://arxiv.org/html/2512.01739v2#S3).
The hybrid Moebius–Mangoldt theorem still averages over shifts; averaging
again over scales does not isolate shift two.
[Lichtman–Teravainen, Theorem 1.2](https://arxiv.org/html/2111.08912v2#S1).

This materially different mechanism supplies no new positive budget
margin from the inspected statements. Its missing ingredient is relative
correlation control on the sparse, fixed-shift support, with all phase
or composite-smooth contributions retained. No further formalization of
this candidate is justified by a paper improvement at this checkpoint.

## 7. Distribution and additive Fourier budget tests

The [distribution and Fourier review](DISTRIBUTION_AND_FOURIER_BUDGET.md)
tests two further ways of obtaining the remaining arithmetic information.
It retains all major-arc, endpoint, diagonal, even-input, prime-power,
and progression residuals before assessing a possible gain.

| Test | Complete-budget consequence | First missing improvement |
|---|---|---|
| Hypothetical one-variable distribution through exponent theta<=1 | The prime-isolating lower-sieve coefficient is 2 exp(-gamma) f(2 theta)=0. | A positive actual-sequence term beyond this lower-sieve budget. |
| Additive Fourier magnitude bound | Cauchy-Schwarz permits a minor-arc loss of order X log X, larger than C X. | A signed bound N_X>=-(1-delta) C X at shift two, for some delta>0 cofinally. |
| Diagonal subtraction and positive kernels | The exact coefficient is unchanged; an explicit positive comparison density permits cancellation of its entire C X major-arc total. | Additional arithmetic control not contained in the listed aggregate positivity and energy data. |
| Almost-all-shift estimates | A sole exceptional nonzero shift 2 at every scale fits every stated fixed logarithmic saving. | A bound excluding shift 2 from the persistent exceptional set. |

The Fourier route would directly improve T+R if its missing one-sided
estimate were proved. It does not need a further independent saving of
0.263 C X, and that class bound cannot be counted again. The review's
comparison densities and error arrays are not models of the actual
primes or all their distribution data.

These tests provide no positive total margin. They therefore do not
justify new conditional Lean endpoints or a larger formalization of
the same missing estimate. The next promotable result must add a
specific signed arithmetic bound to the complete inequality.

## 8. Divisor switching and rough moment targets

The [divisor-switching assessment](DIVISOR_SWITCH_BUDGET.md) uses the
actual shift-two Titchmarsh divisor theorem. The global minorant
Lambda(n)>=(4-tau(n))log(n)/2 gives a lower expression whose leading
term is -kappa X log^2 X/2. More generally, any fixed global polynomial
prime minorant in tau has a negative weighted average of that larger
scale. Those unrestricted moments cannot give the required saving.

After retaining squarefree rough inputs with prime shifted output,
write M for their log(n)log(n+2) mass and D for their divisor moment.
The square and shifted-power removals have explicit o(X) budgets.
The optimal lower bound from these two moments is
Q_tw>=max(0,2M-D/2). Thus an independent cofinal estimate
D<=4M-2delta C X would improve the full signed budget.

The exact hyperbola decomposition keeps both prime and semiprime
divisors below sqrt(n). A switched elementary Selberg upper bound
for just the balanced prime-divisor region has coefficient at least
5.12, larger than the available upper coefficient 4 for M. Its
pointwise replacement only restores a zero budget. The favorable
multiplicity correction and the semiprime-divisor residual cannot
be omitted or counted as an independent gain.

This is a new specification of the missing restricted arithmetic,
not a proof of it. The unrestricted divisor theorem does not evaluate
that rough moment. The certified positive total margin is unchanged
at zero, and the test does not justify further formalization.

## 9. Combining Chen and rough moments does not create a margin

The [joint Chen review](CHEN_WEIGHT_REVIEW.md#combining-the-existing-class-and-moment-inequalities)
now keeps the direction of each shift explicit. Chen's central prime
has a rough successor; the divisor assessment's central prime has a
rough predecessor. Once the cutoffs exceed 3, those central primes
lie in different residue classes modulo 3. Their composite masses
cannot be identified. With the original lower-integer intervals
and common log-product weights, their genuine twin masses agree
exactly; aligning the central-prime intervals instead costs a
bounded endpoint correction.

A joint leading-coefficient assignment satisfies the listed Chen,
rough-moment, hyperbola and middle-prime inequalities with zero
twin mass. It has M=2, D=8, T_middle=0, N_rough=2,
P_comp=1, N_comp=0 and R=1, in units of CX.
It is an aggregate feasibility test, not actual prime or BV data.

A new joint upper estimate would need to improve the combined
leakage Da+Sp+Spp below (kappa+4 log(29/21))CX, with positive
cofinal slack and all errors included. That estimate is not
supplied by either component calculation. The full margin remains zero.

## 10. Exceptional-character bias has a conditional positive budget

The [character-bias assessment](CHARACTER_BIAS_BUDGET.md) displays
an exact nonnegative convolution model and retains its full composite
defect. It then uses a published fixed-shift correlation theorem
under an explicit exceptional-zero hypothesis.

If a primitive quadratic character of conductor q has a real zero
beta=1-1/(eta log q), eta>=10, the selected theorem gives, at X=q^10,

\[
 Q_{\rm tw}\ge CX-3KXe^{-\sqrt{\log\eta}}-E_{\rm pp}.
\]

Both prefix endpoints lie in the source's scale window. For a
fixed sufficiently large eta_0, an unbounded supply of conductors
with eta>=eta_0 would give Q_tw>=CX/2 cofinally. The actual
signed-loss budget would then be

\[
 T+R\le CX/4+|J-CX|+D_{\rm cl}+D_\beta.
\]

This would be a saving for the complete sum. Epp is retained in
the genuine-prime bound and cancels in the separate W2-based
signed-loss transfer; the 0.263 class estimate is not reused.

The required supply of zeros is unproved. The checked Siegel
value and power-gap bounds do not assert zero existence, and
a single exceptional zero gives only a bounded scale window.
The complementary case without such zeros at large conductors
still has no positive twin-prime estimate here. Thus this new
mechanism has a verified conditional budget but adds no
unconditional margin and does not discharge M4-M6.

## 11. Extracting the fixed pair from tuple sieves

The [fixed-pair extraction assessment](FIXED_PAIR_EXTRACTION_BUDGET.md)
addresses an issue beyond the already excluded standard M2 search.
For an admissible k-tuple, the graph joining offsets at difference
2 is a matching plus isolated vertices. If it has e edges,
forcing a twin edge by a prime-count first moment requires
exceeding alpha=k-e>=ceil(k/2). The exact identity is
E=P-alpha+Z_empty; its favorable remainder contains the missing
pair correlations.

The standard Maynard estimates give a lower edge budget
A_N[(theta/2-delta) sum J_i-alpha I]-|r2|-alpha|r1|.
It is negative even for theta<=1. A finite transfer to two
adjacent dyadic Q_tw sums retains the maximum weight and all
translated endpoints, but cannot make this budget positive.
Signed polarization retains an additional nonnegative defect.

For the larger two-coordinate domain in Polymath8b Theorem 3.14,
with its actual vanishing-marginal conditions, a direct norm
identity and an attaining step function prove exact optimum 2.
The theorem still requires a ratio strictly above 2/theta.
Using the full marginals would create an apparent gain, but
adds an unevaluated arithmetic sum whose progression moduli
can exceed the assumed range. That term is not a supplied saving.

These precise criteria add no positive total margin. The norm
calculation is a paper result about the specified functional;
it is not a universal parity theorem, an upper bound for actual
twin mass, or a new Lean endpoint. The full signed estimate
and M4-M6 remain unresolved.

## 12. Gowers uniformity leaves the fixed-shift arithmetic open

The [Gowers-uniformity assessment](GOWERS_FIXED_SHIFT_BUDGET.md)
uses the quantitative theorem with its actual exceptional-character
correction. The pattern theorem requires independent linear
coefficient vectors, which the forms n and n+2 do not have.

With a common corrected model, exact masks and a cyclic group of
prime order p comparable to X, its finite replacement is
Q_tw=M+H+K-Epp. Here M is the model pair mass, H contains both
mixed terms, and K is the residual pair term. The complete bound is

\[
 Q_{\rm tw}\ge CX-D_{\rm model}-D_{\rm mixed}
       -p^{3/2}\|f\|_{U^2}\|g\|_{U^2}-E_{\rm pp}.
\]

Neither model nor mixed error is silently declared negligible.
Padding and interval masking preserve the supplied norm rate
up to a logarithm, but the remaining power loss is too large.
Even granting all other errors o(X), this transfer would need
norm bounds o(p^(-1/4)) to make its residual term o(X).

A sparse comparison construction has nonnegative weights,
exact mean one, height O(log N), support size asymptotic to
N/log N, and zero product at shift two. Its centered norms are
O_S(log N N^(-1/2^s)) simultaneously for each 1<=s<=S, for every
fixed finite S. The interval version retains its four boundary
weights. This is a counterexample to an inference from those norm
and density data alone, not a model of all prime distribution data.

A new arithmetic bound H+K>=-(1-delta)CX cofinally, together with
D_model+Epp=o(X), would improve the complete signed loss to

\[
 T+R\le(1-\delta)CX+
       |J-CX|+D_{\rm model}+D_{\rm cl}+D_\beta.
\]

Epp cancels only in this W2-based transfer; the middle-prime
class bound is not added as a second saving. The new arithmetic
bound is unproved. The certified positive total margin remains
zero, so this assessment justifies no additional Lean endpoint.

## 13. Weighted distribution and microscopic factor endpoints

The [current-cutoff distribution assessment](CUTOFF_SHIFT_ROUTE.md#6-current-cutoff-weighted-distribution-and-its-full-residual)
now retains a full factorable-approximation budget on the actual
prime-quotient part of R. A decomposition into factorable weights
leaves an exact residual with elementary bound

\[
 E_r\le2X\log^2(2X+2)\sum_a|r(a)|/a.
\]

A broadened forbidden-support family has positive limiting
harmonic coefficient mass. It prevents justification of o(X)
deletion through this bound alone; it is not a lower bound on
the actual discarded prime-shift contribution. The coefficient
sum in any termwise application and the outer a>D tail are
also retained.

At level D=X^(5/8-epsilon), the forced-prime-quotient range
a>2X/W^2 leaves quotient sieve parameter at most 3/14+o(1).
Even an admissible modulus weight does not supply the missing
prime quotient. The new September 2026 convolution theorem
has stronger levels for an unrestricted integer factor paired
with a prime, but omits our simultaneous smooth coefficient
and shifted-prime condition. The tested lower-sieve use gives
zero leading coefficient even after granting those extra inputs.

The materially different [prime-factor endpoint assessment](PRIME_FACTOR_ENDPOINT_BUDGET.md)
has the exact identity H_K=Q_tw+D_K. H_K counts prime outputs
with P+(n)>n/K, and D_K keeps every odd cofactor 3<=k<K with
q and kq+2 both prime. For 1<K<=3, D_K=0 and H_K=Q_tw.
Thus the microscopic endpoint law has discrete plateaus.
Two distinct endpoint widths below log(3)/log(2X) cannot both
obey the continuous limiting prediction with o(1/log X) error.

For larger K, a lower tail bound creates a total gain only after
the entire D_K is subtracted:

\[
 T+R=J-H_K+D_K+r_{\rm cl}+r_\beta-E_{\rm pp}.
\]

The finite probability-to-log-weight conversion is explicit.
The source's fixed-parameter correlations and weak convergence
provide neither the necessary microscopic lower estimate nor
the cofactor leakage bound. The complete positive margin
remains zero. No new Lean endpoint is promoted.
