# Raising the right cutoff below the square-root product level

Checkpoint: 2026-09-05. All seven modules below passed the full root build
(8909 jobs). All 38 new public theorems occur in the integrated audit of
1238 unique selected declarations, with only Classical.choice, propext and
Quot.sound and zero errors. The 254-file project source scan is clean.
The independent mathematical review found no
missing distribution input, sign error, or lost even-modulus term. B* remains
open.

| New module | Scope |
|---|---|
| [PowerLevelDistribution](../TwinPrime/Analytic/PowerLevelDistribution.lean) | Polynomial slack implies the actual BV range and normalized progression-error decay. |
| [MixedEvenBudget](../TwinPrime/Analytic/MixedEvenBudget.lean) | The complete even-modulus error for independently chosen cutoffs. |
| [QuarterCutoff](../TwinPrime/Analytic/QuarterCutoff.lean) | Fourth-root floors, ordering, and the product exponent 9/20. |
| [BilinearCutoffShift](../TwinPrime/Analytic/BilinearCutoffShift.lean) | Exact finite signed identity, both error budgets, and mixed main-term decay. |
| [MixedTypeICorrelation](../TwinPrime/Analytic/MixedTypeICorrelation.lean) | Actual Type I progression error below the square-root product level. |
| [QuarterBilinearReduction](../TwinPrime/Analytic/QuarterBilinearReduction.lean) | Unconditional generic cutoff-change limit, fourth-root specialization, and prime-beta replacement. |
| [MixedPrimeBetaSmallPart](../TwinPrime/Analytic/MixedPrimeBetaSmallPart.lean) | Exact mixed smooth/rough coefficient and middle-prime negative class. |

## 1. An exact signed cutoff change

Use the repository's actual shifted correlation terms

\[
 B(U,V;X)=\sum_{X<n\le2X}\Lambda(n+2)(\mu_{>U}*\beta_V)(n),
 \qquad \beta_V(r)=\sum_{\substack{b\mid r\\b>V}}\Lambda(b).
\]

For natural cutoffs V,W<=X, with no positivity assumption on U,
[BilinearCutoffShift](../TwinPrime/Analytic/BilinearCutoffShift.lean) proves

\[
 B(U,V;X)-B(U,W;X)=I(U,V;X)-I(U,W;X).                 \tag{1}
\]

Both low-Mangoldt terms vanish on X<n<=2X, and the remaining common terms in
the two finite Vaughan identities cancel. The signs in (1) are essential.
When V<=W, this changes the Mangoldt-divisor band V<b<=W inside beta. It does
not merely delete right factors r in that interval: beta changes also for
large r divisible by such b.

## 2. Why classical BV and Mertens control this change

Put Y=2X+2 and write Q(U,V) for the exact totient Type I main coefficient.
For UV<=X, [MixedTypeICorrelation](../TwinPrime/Analytic/MixedTypeICorrelation.lean)
proves

\[
 |I(U,V;X)-XQ(U,V)|
 \le 2\log Y\sum_{1\le q\le UV}E_q(Y)+E_{\rm even}(U,V,X), \tag{2}
\]

where E_q is the actual maximal progression error and

\[
 E_{\rm even}=(UV+1)\log Y\,(2\sqrt Y\log Y).
\]

[MixedEvenBudget](../TwinPrime/Analytic/MixedEvenBudget.lean) bounds this by
4Y^(a+1/2)log^2 Y whenever UV<=Y^a and a>=0. Thus its normalized limit is zero
for a<1/2. Even moduli are retained, including their power-of-two contribution.
[PowerLevelDistribution](../TwinPrime/Analytic/PowerLevelDistribution.lean)
proves that UV<=X^a, a<1/2, eventually lies below every required BV range
sqrt(X)/log^B X; the polynomial slack absorbs each fixed logarithmic loss.
The normalized first term of (2) also tends to zero.

The main coefficient is not factored by assuming coprimality. Its proved
formula is

\[
 Q(U,V)=F(U)\sum_{\substack{b\le V\\b\ {\rm odd}}}
                  \frac{\Lambda(b)}{\phi(b)}
          -\operatorname{sharedPrimeCorrection}(U,V),
 \quad
 F(U)=\sum_{\substack{d\le U\\d\ {\rm odd}}}\frac{\mu(d)}{\phi(d)}.
\]

The second factor is at most 6log^2(V+1). Quantitative Mertens gives
F(U)log^2(U+1)->0, and the shared-prime correction tends to zero as U->infinity,
with the other cutoff arbitrary. For U=primaryCutoff(X)=floor(X^(1/5)) and
W<=X, the exact floor bound X<(U+1)^5 implies
log(W+1)<=5log(U+1). Hence Q(U,W)->0.
The inputs used here are the actual unconditional theorems in
[ClassicalDistribution](../TwinPrime/Analytic/ClassicalDistribution.lean).

Consequently the generic assembly states, for any natural-valued W(X),

\[
 UW\le X^a\ \hbox{eventually},\quad 0\le a<\tfrac12
 \quad\Longrightarrow\quad
 \frac{I(U,W;X)}X\longrightarrow0,\qquad
 \frac{B(U,U;X)-B(U,W;X)}X\longrightarrow0.             \tag{3}
\]

The product hypothesis itself implies W<=X eventually. At the level of
exponents this permits W=floor(X^theta) for 0<=theta<3/10; this observation
uses the generic theorem, not a separately exported family of power cutoffs.

## 3. The explicit fourth-root example

[QuarterCutoff](../TwinPrime/Analytic/QuarterCutoff.lean) defines
W=floor(X^(1/4)) and proves, for X>=1,

\[
 U\le W\le X,\qquad UW\le X^{9/20}.
\]

The BV slack is 1/20, and the even budget is at most
4(2X+2)^(19/20)log^2(2X+2)=o(X). The final assembly specializes (3) and combines
it with the previously proved prime-only beta replacement:

\[
 B(U,U;X)-B'(U,W;X)=o(X),\qquad
 B'(U,W;X)=\sum_{X<n\le2X}\Lambda(n+2)(\mu_{>U}*\beta'_W)(n).
                                                               \tag{4}
\]

Here beta'_W(r)=sum_(p|r, p>W prime)log p. Its replacement error is uniformly
O(X log^2(4X+4)/sqrt(W)), even for arbitrary left-cutoff functions. The
normalized replacement error remains zero after multiplication by any fixed
natural power of log(4X+4). No such strengthened rate is asserted here for
the total cutoff change in (3).

The later [finite-center refinement](CLASSICAL_CENTER_PRECISION.md)
does prove this precision for the centered change (B+J)(U,U)-(B+J)(U,W),
retaining the exact finite main coefficients. It does not infer that rate
for the uncentered difference from the limits used in (3).

Equations (3)-(4) control complete signed sums. They do not bound the absolute
mass of the removed divisor band or allow arbitrary further restrictions on
it. The prime-only replacement separately has an absolute factorwise bound.

## 4. The remaining coefficient and first unsupported application

The left cutoff remains U. For positive a,b, U<=W, a W-smooth and b W-rough,
the newly checked mixed-cutoff identity gives, in paper notation,

\[
 (\mu_{>U}*\beta'_W)(ab)
 =P_W(ab)-m_U(a)\log\operatorname{rad}(b),\qquad
 m_U(a)=\sum_{\substack{d\mid a\\d\le U}}\mu(d).        \tag{5}
\]

Here P_W(n)=1_(n prime and n>W)log n. The Lean statement uses beta'_W(b);
the proved distinct-prime-log formula identifies this with log rad(b) in the
paper notation. It restricts divisors d<=U<=W to a and needs no squarefreeness.
The separate exact middle-prime theorem gives -beta'_W(b) when a is prime
and 1<=U<a<=W, because m_U(a)=1. Thus m_U cannot be replaced by m_W;
the coefficient is strictly negative when b>1, and zero at b=1.

For W>=2, the range

\[
 \left\lceil2X/W^2\right\rceil\le a
 \le\left\lfloor2X/(W+1)\right\rfloor,\qquad
 b>1,\quad X<ab\le2X
\]

forces a W-rough b to be prime, since a composite would exceed W^2. The exact
remaining contribution from W-smooth a>1 in this range is therefore

\[
 -\sum_a m_U(a)\sum_{\substack{p>W\ {\rm prime}\\X<ap\le2X}}
                       \log p\,\Lambda(ap+2).        \tag{6}
\]

At the quarter cutoff, a ranges approximately from X^(1/2) to X^(3/4), and
p from X^(1/4) to X^(1/2). Modulus a is generally too large for BV. Switching
to modulus p leaves the W-smooth condition and m_U(a) inside the progression.
Expanding m_U gives moduli pd as large as X^(7/10), and still leaves a
smooth-supported quotient. The first unsupported step is estimating that
weighted, restricted progression by the unweighted BV error, even in boxes
where pd lies within the BV level.

Thus (4) reduces B* to a more restrictive coefficient without proving its
needed lower bound. An o(X) replacement transfers bounds with fixed positive
slack; it does not preserve an exact threshold without accounting for the
error. The [earlier sign and sieve limitations](BILINEAR_PRIME_BETA_ROUTE.md)
continue to apply.

## 5. Primary-source applicability check

The following are checks of specific theorem statements, not a claim that
every possible application or paper has been excluded.

**Pascadi, version 2, 29 June 2025.** Theorem 1.3 gives fixed-residue prime
progression errors O_A(x/log^A x) up to level x^(5/8-epsilon) with
triply-well-factorable weights, or x^(3/5-epsilon) with specified upper linear
sieve weights. Definition 1.1 requires a convolution into 1-bounded sequences
for every factorization of the level into three lengths. It does not permit
arbitrary smooth-supported weights, or insert a prime restriction on the
quotient. Theorem 1.5 distributes smooth numbers themselves; it does not add
the factor Lambda(ap+2). These are distinct coefficient conditions, not just
level restrictions.
[Primary text, Definition 1.1 and Theorems 1.3/1.5](https://arxiv.org/html/2505.00653v2#S1).

Here is a direct support obstruction for the proposed weight, independently
of the paper's proof. Fix 0<epsilon<1/80 and level D=X^(5/8-epsilon). Choose
seven distinct primes r_i in [X^(7/80),2X^(7/80)], and put a=product r_i.
For sufficiently large X, each pair product is <=U and each triple product
is >U. Thus m_U(a)=1-7+21=15, a has size X^(49/80), and a<=D. In the balanced
three-factor split D_i=D^(1/3), each factor can contain at most two r_i.
Seven prime factors cannot fit, so every such convolution vanishes at a.
Any weight nonzero at a therefore fails the required factorability; rescaling
the weight does not fix this. A prime quotient of size X^(31/80) exceeds W,
so this nonzero coefficient pattern survives the cutoff shift. This makes no
claim that the associated ap+2 is prime.

**Pascadi, version 3, 29 June 2025.** Theorem 1.5 of the earlier smooth-number
paper treats 1-bounded completely multiplicative functions supported on
smooth integers, subject to a Siegel-Walfisz criterion and an explicit
smoothness range, with level x^(66/107-epsilon). Our truncated weight is not
even multiplicative: for distinct primes r,s<=U<rs,
m_U(r)=m_U(s)=0 but m_U(rs)=-1. A prime shift weight is an additional
unsupported insertion. The theorem therefore does not apply directly to (6).
[Primary text, Theorem 1.5](https://arxiv.org/html/2304.11696v3#S1).

**Bharadwaj-Rodgers, version 4, 9 April 2026.** Proposition 2 and Lemma 8
give unconditional shifted-prime factor correlations for continuous tests
supported where the sum of selected prime-factor logarithmic coordinates is
strictly below 1/2. This does not cover the entire smooth factor a in (6),
whose size starts at order X^(1/2), nor impose a unique prime quotient while
retaining m_U(a). The paper explicitly distinguishes these correlations from
a largest-prime-factor asymptotic.
[Primary text, Section 1.3](https://arxiv.org/html/2402.11884v4#S1.SS3).

## 6. Current-cutoff weighted distribution and its full residual

This follow-up uses the completed middle-prime cutoff
W=floor(X^(21/100)), U=floor(X^(1/5)). It tests whether
stronger distribution controls the remaining signed class,
rather than just lowering the middle-prime upper constant.
All statements below are paper assessments, not new Lean inputs.

Let A be the odd W-smooth a in the forced-prime-quotient range

\[
 a>2X/W^2,\qquad a\le2X/(W+1).
\]

For sufficiently large X these a are composite. Set

\[
 P_a=\sum_{\substack{p>W\ {\rm prime}\\X<ap\le2X}}
                         \log p\,\Lambda(ap+2),\qquad
 R_A=\sum_{a\in A}m_U(a)P_a,\qquad R_{\rm out}=R-R_A.
                                                        \tag{7}
\]

These definitions use the signed R in the
[complete budget](SIGNED_TOTAL_BUDGET.md). In this range a
W-rough quotient is prime: it is at most W^2, whereas a
composite W-rough quotient exceeds W^2. Thus (7) is an
actual part of R, including both signs. R_out retains every
other class, including even smooth parts and outer tails.

### 6.1 The cost of a factorable approximation

For any proposed finite decomposition

\[
 m_U(a)1_A(a)=\sum_j c_j\gamma_j(a)+r(a),
\]

with the gamma_j supported on odd a at a level D<X, put
Pi_j=sum_a gamma_j(a)P_a. The exact replacement is

\[
 R_A=\sum_jc_j\Pi_j+\sum_a r(a)P_a.
\]

Since the residual has support a<=X eventually, its
unconditional elementary error is

\[
 E_r=\log^2(2X+2)\sum_a|r(a)|(X/a+1)
 \le2X\log^2(2X+2)\sum_a\frac{|r(a)|}{a}.                \tag{8}
\]

Complex coefficients are allowed in this identity. Taking
real parts, the complete lower budget is

\[
 Q_{\rm tw}\ge0.737CX-R_{\rm out}
              -\Re\sum_jc_j\Pi_j-E_r-E_{\rm tot}.         \tag{9}
\]

No term in (9) has been made small by merely asserting the
existence of a factorable decomposition. Even if a theorem
gave |Pi_j-M_j|<=D_j, its accumulated cost would be
sum_j |c_j|D_j. An atomic decomposition can have a large
coefficient sum, so applying a uniform theorem separately
to its atoms does not preserve its saving automatically.
Moreover Pi_j contains the prime-restricted quotient;
it is not the ordinary progression sum in that theorem.

The support obstruction in Section 5 can be enlarged to
test the elementary deletion bound (8). Choose seven
distinct primes

\[
 X^{17/200}<r_i\le X^{7/80},\qquad a=r_1\cdots r_7.
\]

Each pair product is below U and each triple product
is above U, so m_U(a)=1-7+21=15. These a have exponents
between 119/200 and 49/80, lie in A eventually, and lie
below D=X^(5/8-epsilon) for 0<epsilon<1/80.
No balanced three-factor split of D can hold seven such
prime factors: each factor can hold at most two.
The balanced two-factor split also fails, since each
factor can hold at most three. Thus every ordinary or
triply well-factorable weight at that level vanishes there.

For this enlarged set B_X, reciprocal-prime summation gives

\[
 \sum_{a\in B_X}\frac{m_U(a)}a
 \longrightarrow\frac{15}{7!}\log^7(35/34)>0.            \tag{10}
\]

Indeed sum_(X^(17/200)<p<=X^(7/80))1/p tends to log(35/34),
and repeated-prime terms in its seventh power tend to zero.
Consequently deleting all this forbidden support does not
give the o(log^(-2) X) harmonic residual sufficient for
E_r=o(X) through (8). This is not a lower bound on the
actual discarded prime-shift mass. A sharper arithmetic
deletion bound could be better than the elementary bound.

The tail a>D is another residual: the actual range A
extends to exponent 79/100. It cannot be included in a
level-D application without a separate argument.

### 6.2 Even admissible moduli leave a quotient selector

For a in A_D=A intersect [1,D], let B_a be the integers
b>W with X<ab<=2X. For any valid upper/lower sieve weights
rho_(a,d)^+ and rho_(a,d)^- supported on d<=D/a, define

\[
 S_a^\pm=
 \sum_{\substack{d\le D/a\\d\mid\prod_{p\le W}p}}
 \rho_{a,d}^{\pm}
 \sum_{\substack{b\in B_a\\d\mid b}}\log b\,\Lambda(ab+2).
\]

The pointwise sieve inequalities imply
E_a^+=S_a^+-P_a>=0 and E_a^-=P_a-S_a^->=0.
Writing m_U=m_+-m_- with both parts nonnegative, the exact
signed identity on A_D is

\[
 \sum_{a\in A_D}m_U(a)P_a
 =\sum_{a\in A_D}(m_+(a)S_a^+-m_-(a)S_a^-)
  -\sum_{a\in A_D}(m_+(a)E_a^++m_-(a)E_a^-).             \tag{11}
\]

The last term is favorable but unestimated. It is a
quotient-sieve defect, not Epp. The progression
moduli in the preceding sums are ad<=D; terms with even
ad require their own nonprimitive-residue treatment.
Endpoint and logarithmic-weight conversions also remain
part of the actual progression-error budget.

Even granting all those errors at the strongest tested
Pascadi level, the quotient sieve parameter satisfies

\[
 \frac{\log(D/a)}{\log W}
 \le\frac{\log(DW^2/(2X))}{\log W}
 =\frac3{14}-\frac{\varepsilon}{21/100}+o(1)<1.           \tag{12}
\]

This is below the threshold 2 for a positive lower
linear-sieve coefficient. Thus the signed favorable
mass cannot be recovered by that lower-sieve evaluation.
This tests the stated evaluation, not every possible
use of weighted distribution or of the defect in (11).

### 6.3 Product moduli and the September 2026 convolution input

[Maynard I, Theorem 1.1](https://arxiv.org/pdf/2006.06572)
does allow absolute progression errors, and hence arbitrary
bounded masks, on its restricted product-modulus set.
It requires

\[
 Q_1Q_2^2<X^{1-100\varepsilon},\quad
 Q_1^{12}Q_2^7<X^{4-100\varepsilon},\quad
 Q_1^{20}Q_2^{19}<X^{10-100\varepsilon}.
\]

Multiplying the first and third constraints gives
(Q_1Q_2)^21<X^(11-200epsilon). The limiting product
exponent is 11/21, attained in the closed limiting
constraints at exponents (1/21,10/21); the second
constraint then has exponent 82/21<4.
This lies below A's starting exponent 29/50.

[Yang, version 2, 3 September 2026, Theorem 1.4](https://arxiv.org/html/2608.13299v2)
states convolution distribution at level X^(ell(nu)-epsilon),
with well-factorable modulus weights, where

\[
 \ell(\nu)=
 \begin{cases}
  1/4+\nu,&3/8\le\nu\le1/2,\\
  1/2+\nu/2,&1/2\le\nu\le1.
 \end{cases}
\]

Its equation (1.2) pairs an unrestricted integer l~X^nu
with a prime p. It contains neither m_U(l) times a
smoothness mask nor Lambda(lp+2). The arbitrary f(l)
statement in Lemma 2.7 is the older square-root-level
result. The proof's equation (4.9) keeps one variable
unweighted for the subsequent Poisson summation; its
arbitrary coefficient on the other variable does not
allow both our smooth coefficient and the prime selector.
The coefficient gamma_d in (1.1) weights an extra modulus.

Even if one additionally supplied compatible dimension-one
sieve densities, our smooth mask and lower-sieve remainder
bounds, direct isolation of a prime lp+2 would require
sifting to sqrt(2X+2). On the forced-quotient exponents
29/50<=nu<=79/100, the limiting parameter would be

\[
 s=2\ell(\nu)-2\varepsilon
     =1+\nu-2\varepsilon<2.
\]

The usual lower coefficient f(s) would still be zero.
This last calculation explicitly grants inputs absent
from the theorem; it is not an application of it.

None of these tests improves (9) below a positive
complete-budget threshold. A separate, materially
different [prime-factor endpoint assessment](PRIME_FACTOR_ENDPOINT_BUDGET.md)
retains discrete cofactors and shows why a microscopic
continuous-distribution shortcut also fails. The
unconditional total margin remains zero.
