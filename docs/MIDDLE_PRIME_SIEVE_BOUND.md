# An aggregate sieve bound for the negative middle-prime class

Checkpoint: 2026-09-05. The complete bound T_(21/100)<=0.263 C X is
proved on paper and in Lean, using the actual class and all its errors.
The general sharp limiting constant below has the cited paper derivation;
the formal proof uses a fixed power level and the existing Selberg sieve.
Section 7 states the exact formal scope. The remaining signed estimate
B* is open, and the [total budget](SIGNED_TOTAL_BUDGET.md) still has no
certified positive margin.

## 1. Actual sum and conclusion

Let X tend to infinity through positive integers, fix

\[
 \frac15<v<\frac3{10},\qquad
 U=\lfloor X^{1/5}\rfloor,\qquad W=\lfloor X^v\rfloor,
 \qquad C=2\,\mathrm{twinPrimeConstant}.
\]

An integer b is W-rough if it is positive and every prime divisor of b is
strictly greater than W. Retain the actual prime-only beta coefficient

\[
 \beta'_W(b)=\sum_{\substack{p\mid b\\p>W\text{ prime}}}\log p.
\]

Define the nonnegative mass

\[
 T_v(X)=
 \sum_{\substack{U<q\le W\\q\text{ prime}}}
 \ \sum_{\substack{X<qb\le2X\\b\ W\text{-rough}}}
       \Lambda(qb+2)\,\beta'_W(b).                         \tag{1}
\]

There is no squarefreeness restriction on b. The mixed-cutoff identity in
[MixedPrimeBetaSmallPart](../TwinPrime/Analytic/MixedPrimeBetaSmallPart.lean)
gives coefficient -beta'_W(b) on this class, so its signed contribution is
exactly -T_v(X). Distinct q give disjoint input classes: the only prime at
most W dividing qb is q, and its exponent is one.

The conclusion proved below is

\[
 \limsup_{X\to\infty}\frac{T_v(X)}X\le C K(v),\qquad
 K(v)=2\int_{1/5}^{v}\frac{1-t}{t(1/2-t)}\,dt
     =4\log\frac{v}{1/5}-2\log\frac{1/2-v}{3/10}.       \tag{2}
\]

The restriction v<3/10 makes this compatible with the existing signed
cutoff reduction: UW<=X^(1/5+v) has fixed polynomial slack below X^(1/2).
It does not assert that (1) is the entire negative part of B'.

## 2. Fixed s=2 and the correct local density

Choose a fixed, sufficiently large B for the BV error estimate used below,
and set

\[
 D=\frac{X^{1/2}}{(\log X)^B},\qquad
 D_q=D/q,\qquad z_q=D_q^{1/2},\qquad Y=2X+2.
\]

All sieve levels and thresholds may be real. The remainder condition
d<=D_q means the exact integer endpoint d<=floor(D/q).
Uniformly for U<q<=W, we have q>X^(1/5), q<=X^v, and

\[
 D_q\ge\frac{X^{1/2-v}}{(\log X)^B}\longrightarrow\infty,
 \qquad z_q<X^{3/20}<q,\qquad z_q<W
\]

for sufficiently large X. The floor in W does not affect the last
inequality, since W>=X^v/2 eventually. We sieve only by the **odd** primes
below z_q. Every W-rough b survives this smaller sieve. This uses the upper
sieve at the fixed admissible parameter s=log(D_q)/log(z_q)=2; it does not
apply an s>=1 theorem at the possibly smaller value
(1/2-log(q)/log(X))/v.

For each q use the finite nonnegative sequence

\[
 a_q(b)=1_{X<qb\le2X}\Lambda(qb+2),\qquad A_q=X/\phi(q).
\]

Put P(z)=product_(2<p<z) p. If d divides P(z_q), then (d,q)=1 and d is
odd. Consequently the exact progression identity is

\[
 \begin{split}
 \sum_{\substack{b\ge1\\d\mid b}}a_q(b)
 &=\psi(Y;qd,2)-\psi(X+2;qd,2)\\
 &=\frac{X}{\phi(q)\phi(d)}+r_X(qd),                  \tag{3}\\
 r_X(m)&=\psi(Y;m,2)-\psi(X+2;m,2)-X/\phi(m).
 \end{split}
\]

Thus the needed multiplicative sieve density is g(p)=1/(p-1) for odd
primes. It is independent of q on the entire support being used. If one
sieved through q instead, the local density at p=q would be 1/q; that
exception is avoided here by z_q<q. The prime 2 is excluded from P(z), so
the invalid value g(2)=1 is never used. All von Mangoldt prime powers remain
in (3). Enlarging to the odd-prime sifted set is an upper bound, so no
separate parity or prime-power error has been dropped.

For the repository's actual maximal progression error E_m(Y), (3) gives

\[
 |r_X(m)|\le2E_m(Y)\qquad(m\text{ odd}).               \tag{4}
\]

The endpoints X+2 and 2X+2 have difference exactly X; there is no interval
length approximation in this main term.

## 3. The external upper-sieve input and its main constant

The input is the standard upper linear sieve at s>=1 under the
dimension-one product condition. It gives main term A_q V(z)(F(s)+O(epsilon))
and a remainder with weights supported on d<=D_q, d|P(z), uniformly bounded
by a constant J_epsilon independent of X and q. The well-factorable version
allows at most exp(epsilon^(-3)) bounded components. Its functions satisfy
sF(s)=2 exp(gamma) for s<=3. This is stated precisely in
[Lichtman, Theorem 2.10, equations (2.3)--(2.5), version 2](https://arxiv.org/html/2109.02851v2#S2.SS2),
which cites Iwaniec and *Opera de Cribro*, Theorem 12.20. We use its ordinary
upper-sieve consequence, not Lichtman's stronger distribution theorem.

The weighted formulation follows from the pointwise upper-sieve inequality:
multiply it by a_q(b)>=0 and sum. Inserting (3) splits the result into
A_q times the sieve-density sum and the actual remainders. In particular,
A_q is a chosen main mass, not an assumption that the actual total mass is
already known with no error; d=1 is included in (3)--(4).

The product condition and normalization follow from ordinary Mertens:

\[
 \begin{split}
 V(z)&=\prod_{2<p<z}\left(1-\frac1{p-1}\right)\\
 &=\prod_{2<p<z}\frac{p(p-2)}{(p-1)^2}
       \prod_{2<p<z}\left(1-\frac1p\right)
 \sim\frac{Ce^{-\gamma}}{\log z}.                    \tag{5}
 \end{split}
\]

The same factorization gives the required dimension-one ratio estimate,
with an absolute constant. Since min_q z_q tends to infinity, (5) is
uniform in the q under consideration. At s=2, F(2)=exp(gamma), and therefore

\[
 V(z_q)F(2)\sim\frac{C}{\log z_q}
                 =\frac{2C}{\log(D/q)}.             \tag{6}
\]

Fix epsilon first. The upper sieve, (4), and the inclusion of the W-rough
set give

\[
 \sum_{\substack{X<qb\le2X\\b\ W\text{-rough}}}\Lambda(qb+2)
 \le \bigl(2C+O(\epsilon)+o_X(1)\bigr)
       \frac{X}{\phi(q)\log(D/q)}
   +2J_\epsilon
       \sum_{\substack{d\le D/q\\d\mid P(z_q)}}E_{qd}(Y).       \tag{7}
\]

Both the o_X(1) and the sieve threshold are uniform in q. Constants may
depend on the fixed v and epsilon, but not on q or X.

## 4. Finite aggregation of the actual BV remainder

Prime factorization proves beta'_W(b)<=log b: each retained prime has
exponent at least one, and log b is the sum with those exponents. Equality
with log b is not assumed for repeated factors. On X<qb<=2X, we thus have
beta'_W(b)<=log(2X/q)<=log(2X).

Multiplying (7) by log(2X/q) gives the finite bound

\[
 \begin{split}
 T_v(X)\le{}&\bigl(2C+O(\epsilon)+o_X(1)\bigr)X
       \sum_{\substack{U<q\le W\\q\text{ prime}}}
       \frac{\log(2X/q)}{\phi(q)\log(D/q)}\\
 &+2J_\epsilon\log(2X)
       \sum_{\substack{U<q\le W\\q\text{ prime}}}
       \sum_{\substack{d\le D/q\\d\mid P(z_q)}} E_{qd}(Y).     \tag{8}
 \end{split}
\]

There are two valid aggregation bounds, with different support requirements.

* If the restriction d|P(z_q) is retained, every prime factor of d is less
  than z_q<q. Thus q is the unique largest prime factor of m=qd, including
  d=1. Each positive modulus m<=D occurs at most once. The last double sum
  in (8) is at most sum_(1<=m<=D) E_m(Y).
* If that restriction has been discarded, uniqueness cannot be claimed.
  Nevertheless, each m<=floor(D) has at most two distinct prime divisors
  above U, since floor(D)<(U+1)^3. The unrestricted double sum is therefore
  at most twice the same progression-error sum. This bound preserves the
  exact endpoint d<=floor(D/q), and also allows d divisible by q.

Either gives an error at most 4 J_epsilon log(2X) sum_(m<=D) E_m(Y);
the retained-support version gives the factor 2. Ordinary BV makes this
o(X). More explicitly, take any fixed A>1 and choose B sufficiently large
that D lies below the BV level for Y. Then sum_(m<=D) E_m(Y)
is O_A(X/log^A X). The factor J_epsilon is fixed before X tends to infinity,
so it causes no uniformity problem. No distribution estimate for a new
prime-pair sequence is required: every error in (8) is the actual
single-prime progression error at qd.

## 5. Prime summation and exact numerical bounds

Put t=log(q)/log(X). Uniformly for q in the summation range,

\[
 \frac{\log(2X/q)}{\log(D/q)}
 =\frac{1-t+\log2/\log X}
        {1/2-t-B\log\log X/\log X}
 \longrightarrow\frac{1-t}{1/2-t}.                  \tag{9}
\]

The denominator stays bounded away from zero because v<3/10. Replacing
1/phi(q)=1/(q-1) by 1/q costs o(1): the remaining factor is bounded and
sum_(q>U) 1/[q(q-1)] tends to zero. Prime partial summation then gives

\[
 \sum_{\substack{U<q\le W\\q\text{ prime}}}
 \frac{\log(2X/q)}{\phi(q)\log(D/q)}
 \longrightarrow
 \int_{1/5}^{v}\frac{1-t}{t(1/2-t)}\,dt.             \tag{10}
\]

The floor endpoints have logarithmic coordinates tending to 1/5 and v.
For example, (10) follows from PNT and integration by parts against
sum_(q<=y) 1/q; its limiting measure in the coordinate t is dt/t.
Finally use (8), let X tend to infinity, and then let epsilon decrease to
zero. Integrating 2/t+1/(1/2-t) proves (2).

At the quarter cutoff,

\[
 K(1/4)=4\log(5/4)+2\log(6/5)
          =1.257217318844748\ldots>1.                \tag{11}
\]

At v=21/100,

\[
 K(21/100)=4\log(21/20)+2\log(30/29)
          =0.262963760029089\ldots<\frac{263}{1000}. \tag{12}
\]

The decimal values are only illustrations. The last strict inequality has
the following exact certificate. For x>=0,

\[
 \log(1+x)\le x-x^2/2+x^3/3,
\]

because the derivative of the right side minus log(1+x) is x^3/(1+x)>=0,
and their difference is zero at x=0. Applying this at 1/20 and 1/29 gives

\[
 K(21/100)
 \le\frac{1171}{6000}+\frac{4961}{73167}
 =\frac{12827173}{48778000}
 =\frac{263}{1000}-\frac{1441}{48778000}
 <\frac{263}{1000}.                                \tag{13}
\]

Thus the rigorous asymptotic upper budget for this entire class is less
than 0.263 C X at v=0.21. The estimate is O(X), not o(X).

## 6. What remains after this class is bounded

The existing [cutoff reduction](CUTOFF_SHIFT_ROUTE.md) gives, in this fixed
power range, B(U,U;X)=B'(U,W;X)+o(X), and the classical center tends to C X.
For the following paper partition take X>W and U>=1, as holds eventually,
and write each input uniquely as n=ab with a W-smooth and b W-rough. The
checked mixed coefficient identity retains m_U(a), not m_W(a).

* If a=1 and n is prime, the prime term cancels beta'_W(n). If a=1 and n is
  composite, the contribution is -beta'_W(n)Lambda(n+2). Denote this
  nonnegative loss by N_rough.
* If 1<a<=U, the contribution vanishes because m_U(a)=0.
* If a is prime and U<a<=W, the loss is exactly T_v(X).
* If a>U is composite and W-smooth, the coefficient is
  -m_U(a)beta'_W(b). Separate its negative mass N_comp using max(m_U(a),0),
  and its positive mass P_comp using max(-m_U(a),0), with the actual product
  interval and shifted weight in both sums. Cases b=1 have beta'_W(b)=0.

This gives the paper identity

\[
 B'(U,W;X)=P_{\rm comp}-N_{\rm rough}-T_v(X)-N_{\rm comp}.       \tag{14}
\]

The present estimate does not bound the other three masses to the required
allowance. A subsequent [rough-composite calculation](ROUGH_COMPOSITE_SIEVE_BOUND.md)
gives N_rough<=4CX-P+o(X) and a lower bound on N_rough+P; neither supplies
the remaining signed gain. Previously
removed gcd, large-square, and prime-power ranges must be accounted for
with their actual error bounds if they are also imposed on this partition.
In particular, squarefree rough composites and composite smooth parts with
positive m_U(a) remain genuine negative classes.

For a fixed positive linear gain, a sufficient further estimate is,
cofinally in X and with fixed delta>0,

\[
 N_{\rm rough}+N_{\rm comp}-P_{\rm comp}
 \le \bigl((1-K(v))C-\delta\bigr)X.                 \tag{15}
\]

Together with (2) and the o(X) errors, (15) leaves a positive margin in W2.
At v=0.21, the conservative remaining allowance is 0.737 C X minus a
positive margin. At v=1/4, this particular bound for T already exceeds
C X, so it leaves no positive allowance without compensating positive
contributions or a stronger bound. Neither case proves (15).

For merely a logarithmic cofinal gain, one must instead compare the actual
total B'+J with its exact finite center at that smaller scale, as in
[ClassicalCenterPrecision](../TwinPrime/Analytic/ClassicalCenterPrecision.lean).
An O(X) limsup bound with an unspecified o(X) error cannot by itself certify
a gain of size X/log^k X.

## 7. Verified formal scope and source map

The actual eventual bound T_(21/100)<=0.263 C X is now a Lean theorem:
`eventually_middlePrimeMass_twentyOneHundredths_le` in
[MiddlePrimeSieveBound](../TwinPrime/Analytic/MiddlePrimeSieveBound.lean).
It has no supplied arithmetic or distribution premise. Its proof uses
one fixed level exponent a=49999/100000, strictly below one half.

The more general checked statement gives, for every 1/5<v<a<1/2 and
every epsilon>0, eventually

\[
 T_v(X)/X\le C K_a(v)+\varepsilon,\qquad
 K_a(v)=2\left[\frac1a\log\frac{v}{1/5}
  +\frac{1-a}{a}\log\frac{a-1/5}{a-v}\right].
\]

The limiting sharp formula (2) follows on paper by taking a up to one
half. That final limit in a is not a separate Lean export; it is not
needed for the completed 0.263 bound.

The formal route uses the existing Selberg sieve and has four parts:

* [MiddlePrimeSieve](../TwinPrime/Analytic/MiddlePrimeSieve.lean) identifies
  the actual nonnegative class and its signed contribution. Together with
  [LargePrimeModuli](../TwinPrime/Analytic/LargePrimeModuli.lean) and
  [MiddlePrimeSieveError](../TwinPrime/Analytic/MiddlePrimeSieveError.lean),
  it retains the entire supported modulus error, including 3^omega(d).
  [SquarefreeWeightedDistribution](../TwinPrime/Analytic/SquarefreeWeightedDistribution.lean)
  proves that weighted error negligible from actual unconditional BV.
* [MiddlePrimeSieveDenominator](../TwinPrime/Analytic/MiddlePrimeSieveDenominator.lean),
  [MiddlePrimeSieveCorrection](../TwinPrime/Analytic/MiddlePrimeSieveCorrection.lean),
  [MiddlePrimeSieveMass](../TwinPrime/Analytic/MiddlePrimeSieveMass.lean), and
  [HarmonicConvolutionLimit](../TwinPrime/Analytic/HarmonicConvolutionLimit.lean)
  prove the exact denominator and its limit S(z)/log z->1/C.
  [MiddlePrimeSieveAsymptotic](../TwinPrime/Analytic/MiddlePrimeSieveAsymptotic.lean)
  supplies uniform substitution into growing sieve families.
* [MiddlePrimeSieveThreshold](../TwinPrime/Analytic/MiddlePrimeSieveThreshold.lean)
  proves every support, level and growth condition for the actual integer
  threshold max(1,sqrt(floor(X^a)/q)).
  [MiddlePrimeSieveWeight](../TwinPrime/Analytic/MiddlePrimeSieveWeight.lean)
  controls its logarithmic rounding uniformly; the real quotient and
  natural quotient give the same floor of the square root.
  [MiddlePrimePowerSieve](../TwinPrime/Analytic/MiddlePrimePowerSieve.lean)
  specializes the full class inequality and complete weighted error limit.
* [PrimeReciprocalAbel](../TwinPrime/Analytic/PrimeReciprocalAbel.lean),
  [PrimeReciprocalLogScale](../TwinPrime/Analytic/PrimeReciprocalLogScale.lean), and
  [MiddlePrimeIntegral](../TwinPrime/Analytic/MiddlePrimeIntegral.lean)
  evaluate the actual Mangoldt sum. The signed-weight estimates in
  [PrimeReciprocalReplacement](../TwinPrime/Analytic/PrimeReciprocalReplacement.lean)
  remove proper prime powers and replace phi(p) by p, with their errors.
  [MiddlePrimeReciprocalBound](../TwinPrime/Analytic/MiddlePrimeReciprocalBound.lean)
  controls the reciprocal prime mass used in uniform rounding.
  [MiddlePrimeMainLimit](../TwinPrime/Analytic/MiddlePrimeMainLimit.lean)
  assembles the actual prime main sum, and
  [MiddlePrimeSieveConstant](../TwinPrime/Analytic/MiddlePrimeSieveConstant.lean)
  supplies the exact rational certificate below 0.263.

No upper linear-sieve theorem is assumed in this formal route. The paper
argument in Sections 2-5 remains a separate derivation of the sharper
limiting constant. Neither argument estimates the remaining signed R;
see the [complete budget](SIGNED_TOTAL_BUDGET.md).

## 8. Why the denominator limit needs no extra analytic hypothesis

Write f(n) for the odd-squarefree coefficient in S(z), with f(0)=0,
and h=normalizedMoebius*f. The checked local values are

\[
 h(2)=-\tfrac12,\qquad
 h(p)=\frac2{p(p-2)},\qquad h(p^2)=-\frac1{p(p-2)}\quad(p>2),
\]

with higher prime powers zero and h(2^k)=0 for k>=2. The absolute local
excess is at most 9/p^2. A convergent Euler-factor majorant proves
sum |h(n)|<infinity. The signed local factor at an odd prime is
1+1/[p(p-2)], the reciprocal of the twin-constant factor. Together with
the factor 1/2 at two, the already checked product gives sum h(n)=1/C.

The inverse relation between normalizedMoebius and 1/n gives exactly

\[
 S(z)=\sum_{1\le d\le z}h(d)H_{\lfloor z/d\rfloor}.
\]

For d<=z and z>=1, the ratio H_floor(z/d)/(1+log z) lies in [0,1].
For each fixed positive d it tends to one. Dominated convergence therefore
uses |h(d)| as its majorant and gives S(z)/(1+log z)->1/C. No logarithmic
moment of h is assumed. Replacing 1+log z by log z and taking reciprocals
gives the two limits used above. A single eventual bound holds for every
z above its threshold, which justifies simultaneous substitution in the
growing family when its minimum active z tends to infinity.

## 9. Completed prime-summation implementation

For fixed u=1/5<v<a<1/2, put L=log X and
g(t)=(1-t)/(t(a-t)). The shortest formal route to the outer sum uses the
existing [real reciprocal Mangoldt estimate](../TwinPrime/Analytic/PrimeReciprocalReal.lean)
A(y)=sum_(n<=y) Lambda(n)/n=log y+c+O(log^(-5) y), with the proved
unconditional BV theorem supplied. No separate prime-harmonic Mertens
theorem is required.

The checked finite bridge is centered Abel summation: if
|A(y)-log y-c|<=M on [A0,B0], then for a continuously differentiable f,

\[
 \left|\sum_{A_0<n\le B_0}\frac{\Lambda(n)}n f(n)
       -\int_{A_0}^{B_0}\frac{f(y)}y\,dy\right|
 \le M\left(|f(A_0)|+|f(B_0)|+
                   \int_{A_0}^{B_0}|f'(y)|\,dy\right).
\]

Take A0=X^u, B0=X^v, and f(y)=g(log y/L)/L. The main integral becomes

\[
 I(u,v,a)=\int_u^v g(t)\,dt
 =\frac1a\log\frac vu+
   \frac{1-a}{a}\log\frac{a-u}{a-v}.
\]

The endpoint weights and total variation are O(1/L), so the stated
reciprocal estimate gives Abel error O(L^(-6)). One must use the full
variation: g is not assumed monotone throughout the allowed range.
Real-endpoint Abel summation already uses the exact outer floors.

The [nonprime Mangoldt tail](../TwinPrime/Analytic/NonprimeMangoldtTail.lean)
removes proper prime powers at cost O(U^(-1/2)/L). Replacing p-1 by p
costs O(1/U). The proved logarithm-of-floor bound controls
log D-aL for D=floor(X^a); the fixed gap a-v keeps the denominators
positive. The extra log 2 in log(2X/p) contributes O(1/L).

For z_q=floor(sqrt(D/q)), the smallest threshold grows like
X^((a-v)/2), and the logarithm-of-floor comparison is uniform in q.
The inequalities z_q<q and z_q<=W follow from a<1/2, u=1/5 and v>u;
q z_q^2<=D holds with the integer cutoffs. These checks, the centered
Abel bridge, and the full assembly are now Lean theorems. At the fixed
level a=49999/100000, the exact cubic logarithm certificate gives

\[
 K_a(21/100)\le
 \frac{961951827676901725}{3657898403618589003}<\frac{263}{1000}.
\]

The strict margin absorbs every vanishing class error and proves the
stated eventual 0.263 C X bound. The signed contribution from the other
classes remains a separate, unproved estimate.
