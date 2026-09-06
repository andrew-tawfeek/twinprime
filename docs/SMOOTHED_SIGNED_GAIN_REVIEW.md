# Testing smoothing and averaging for the signed gain

Checkpoint: 2026-09-05. This investigation obtains a concrete obstruction
to treating full cutoff smoothing as a small-error replacement. It does not
prove B* or the logarithmic gain in
[ConditionalClassicalCenter](../TwinPrime/ConditionalClassicalCenter.lean).
The general calculations below are paper proofs using the classical inputs;
they are not new Lean theorems. No Lean source changed in this checkpoint.

The main result is a signed displacement with a nonzero leading constant.
Put C=2*twinPrimeConstant, R=floor(X^r), W=floor(X^v), where
0<r<=v and r+v<1/2. Logarithmically average the left cutoff over 1<=t<R.
Then

\[
 \frac{\overline B_{R,W}(X)-B(R,W;X)}X
       \longrightarrow-\frac{C(1-v)}r.                 \tag{1}
\]

This uses no asymptotic for W2. At r=1/5,v=1/4 the displacement is -15C/4,
while the averaged classical center tends to 19C/4 after division by X.
The larger center compensates for the decrease in B. Averaging the correctly
centered expression creates no positive gain by itself.

## 1. Exact coefficient and finite error

For R>=2 set

\[
 \alpha_t=\frac{\log((t+1)/t)}{\log R}\quad(1\le t<R),
 \qquad \psi_R(d)=\frac{\log(R/d)}{\log R}\quad(1\le d\le R).
\]

The weights are positive and telescope to one. Interchanging two finite
sums, and telescoping the inner sum starting at d, proves

\[
 \overline m_R(n)=\sum_{1\le t<R}\alpha_t m_t(n)
  =\sum_{\substack{d\mid n\\d\le R}}\mu(d)\psi_R(d)
  =\frac{\Lambda_R(n)}{\log R},\qquad
 \Lambda_R(n)=\sum_{\substack{d\mid n\\d\le R}}
                        \mu(d)\log(R/d).                \tag{2}
\]

The endpoint d=R has zero weight. If W>=R, every d<=R has no prime factor
above W. Dividing n by such a d therefore leaves its prime-only beta weight
unchanged. Combining this fact with mu*beta'_W=P_W gives the global identity

\[
 \overline b'_{R,W}(n)=P_W(n)-\overline m_R(n)\beta'_W(n), \tag{3}
\]

where P_W(n)=1_(n prime,n>W)log n. This argument includes repeated factors.
It does not require first decomposing n into smooth and rough parts.

Here Bbar denotes sum alpha_t*B(t,W;X) with the original beta, and Jbar
denotes the corresponding average of J(t,W;X). The prime-only average is
distinguished by a prime mark, as in (3). The existing
[finite center bound](../TwinPrime/Analytic/ClassicalCorrelationCenter.lean),
triangle inequality and positivity of alpha_t give

\[
 |W_2-(\overline B+\overline J)|\le
 8L\sum_{q\le RW}E_q(2X+2)+3(RW+1)L\,
                      \mathrm{evenProgressionBound}(X),\quad L=\log(2X+2),
                                                               \tag{4}
\]

when RW<=X. Each individual modulus cap tW is at most RW, and each even
budget is enlarged monotonically; no limit is interchanged with a growing
average. With RW below a fixed power smaller than 1/2, (4) is o(X/log^k X)
for every fixed k by the proved finite-center precision. The uniform
prime-beta replacement bound survives averaging as well when W grows as
a positive power. These observations establish the needed o(X) errors
for both sides of (1).

## 2. The lower-cutoff boundary changes the main term

Write

\[
 K_X=\sum_{X<n\le2X}\log n,\quad
 S_R=\sum_{\substack{d\le R\\d\text{ odd}}}
              \frac{\mu(d)}{\phi(d)}\log(R/d),\quad
 T_R=\sum_{\substack{d\le R\\d\text{ odd}}}
              \frac{\mu(d)}{\phi(d)}\log^2(R/d).
\]

Combining log(t/d)+log(n/t)=log(n/d) in the mixed and logarithmic terms
before averaging gives the exact center

\[
 \overline J_{R,W}=
 \left(\frac{K_X}{\log R}-X\right)S_R
       +\frac{X}{\log R}T_R-X\overline Q_{R,W}.          \tag{5}
\]

Here Q is the full Type I main coefficient. Its already established
shared-prime formula, averaged with the same weights, is

\[
 \overline Q_{R,W}=
 \frac{S_R}{\log R}H(W)
 -\sum_{1\le t<R}\alpha_t\operatorname{sharedCorrection}(t,W),
 \qquad H(W)=\sum_{\substack{b\le W\\b\text{ odd}}}\frac{\Lambda(b)}{\phi(b)}.
                                                               \tag{6}
\]

The ingredients for the limit in (5) are as follows.

1. The proved smoothed totient limit gives S_R->C. For real y>=1 define
   S(y) with the same formula and d<=y. Finite integration gives
   T_R=2 integral_1^R S(y)dy/y. The real extension also tends to C:
   S(y)-S(floor y)=F(floor y)log(y/floor y), and F is bounded. Splitting
   this logarithmic integral at a fixed large threshold proves
   T_R/log R->2C.
2. X log X<=K_X<=X log(2X), and log R/log X->r. Thus
   K_X/(X log R)->1/r.
3. The difference H(W)-sum_(n<=W)Lambda(n)/n is bounded. Indeed its exact
   prime-power expansion is
   sum_(odd p^j<=W)log p/[p^j(p-1)]-sum_(2^j<=W)log2/2^j.
   Its absolute value is at most sum_(odd p)log p/(p-1)^2+log2, a convergent
   series. The classical reciprocal-Mangoldt asymptotic therefore yields
   H(W)/log W->1. This elementary totient bridge is a paper derivation,
   not a separately exported Lean theorem.
4. The bounds underlying
   [MoebiusTotientAsymptotics](../TwinPrime/Analytic/MoebiusTotientAsymptotics.lean)
   give a bounded function g(t)->0 such that
   |sharedCorrection(t,W)|<=g(t), uniformly in W. Explicitly one may take
   g(t)=sum_(odd p,j>=1)log p*|F_p(t)|/[p*phi(p^j)]; the same summable
   majorant used there proves this limit. The alpha-weight of every fixed
   initial segment tends to zero. Splitting at that segment shows the
   last term of (6) tends to zero.

Consequently Qbar->Cv/r, and (5) gives

\[
 \overline J_{R,W}/X\longrightarrow
 C(1/r-1)+2C-Cv/r=C\left(1+\frac{1-v}{r}\right).       \tag{7}
\]

The sharp center J(R,W;X)/X tends to C: the mixed smoothed term tends to C,
F(R)log X->0, and Q(R,W)->0 by the known logarithmic Mertens and shared-prime
bounds. Subtracting the sharp and averaged approximations to the same W2
in (4) proves (1), with the stated negative sign. Prime-only beta gives
the same displacement, since both replacement errors are o(X).

The invalid shortcut is averaging pointwise sharp-center limits and claiming
Jbar=CX+o(X) without a uniform integrable bound. Bounded t occupy vanishing
average weight but their logarithmic terms can have order X log X. Formula
(5) retains their combined contribution.

## 3. A power window avoids that boundary but leaves the sign problem

For integers 2<=S<R, average over S<=t<R with denominator log(R/S).
The coefficient is exactly

\[
 m_{S,R}(n)=\frac{\Lambda_R(n)-\Lambda_S(n)}{\log(R/S)}. \tag{8}
\]

Its divisor weight equals one below S, tapers logarithmically on (S,R], and
vanishes above R. The exact center is

\[
 J_{S,R,W}=\frac{\log R\,\overline J_{R,W}
                       -\log S\,\overline J_{S,W}}{\log(R/S)}.
\]

If S=floor(X^s), 0<s<r, (7) makes the additional boundary terms cancel,
and J_(S,R,W)/X->C. This is a legitimate o(X) change of the complete sharp
bilinear sum. It still requires an independent estimate of its signed gain.

The second-moment improvement from smoothing is real. Granville,
Koukoulopoulos and Maynard analyze smoothed divisor moments, including
linear smoothing with an ordinary second moment of order x/log R and its
finite counting error. Those unweighted moments alone do not include our
shifted-prime factor.
[Primary paper, Theorem 1.3 and (1.9)](https://smf.emath.fr/system/files/filepdf/ens_ann-sc_54_1089-1177.pdf).

A directly applicable weighted result is Goldston-Yildirim's Theorem 1.4:
take k=3, r=2, shifts (0,2), multiplicities (2,1), and BV level 1/2.
For a fixed power X^epsilon<<R<<X^(1/4-epsilon), it gives

\[
 \sum_{X<n\le2X}\Lambda(n+2)
       \left(\frac{\Lambda_R(n)}{\log R}\right)^2
     =(C+o(1))\frac X{\log R}.                       \tag{9}
\]

This is an actual fixed-shift moment. Subtracting the two endpoint formulas
selects the stated dyadic interval with the same R.
[Primary source, Theorem 1.4](https://arxiv.org/pdf/math/0111212).

Our attempted use of (9) takes absolute values and beta'_W(n)<=log(2X).
Cauchy-Schwarz, together with sum Lambda(n+2)=O(X), gives only

\[
 \sum_{X<n\le2X}\Lambda(n+2)|\overline m_R(n)|\beta'_W(n)
   \ll \frac{X\log X}{\sqrt{\log R}}.
\]

For polynomial R this is O(X sqrt(log X)), so it does not fit a signed
budget of order X. A fixed-power window has the same order by bounding
(Lambda_R-Lambda_S)^2 with twice the two endpoint squares. A sharper
composite-supported positive-part estimate is still missing.

## 4. Exact finite sign check

Smoothing is not a pointwise improvement of the bilinear contribution.
Take X=300, R=W=10, n=381=3*127, with n+2=383 prime. At the sharp cutoff
m_10(3)=0, so the prime-beta coefficient is zero. Full logarithmic averaging
has mbar_10(3)=log3/log10, giving the strictly negative coefficient
-log3*log127/log10. Multiplication by the actual shifted weight log383
preserves this sign. The finite A+H-I contribution increases by exactly
the opposite amount. This last statement concerns the exact finite
decomposition, not the progression main approximation J.

There is also a witness at the exact primary/quarter cutoffs: X=1000,
R=3, W=5, n=1011=3*337, and n+2=1013 prime. The integer inequalities
3^5<=1000<4^5 and 5^4<=1000<6^4 verify the floors, and (RW)^2<1000.
The sharp prime-beta coefficient is zero; its full logarithmic average
is -log337. The finite A+H-I term again increases by the opposite amount.

[smoothing_check.py](../compute/smoothing_check.py) verifies this witness
and the compensation with exact integer coefficients of logarithmic
monomials. It also checks 4,800 averaging identities and 9,600 prime-beta
convolution identities independently by divisor enumeration. No floating
point sign or asymptotic claim is used. Both witnesses are checked. Reproduce with
`python compute/smoothing_check.py`; independent execution passed.

## 5. Other concrete positivity mechanisms checked

For the proposed Mellin residue approach, D2(s)=sum Lambda(n)Lambda(n+2)n^(-s) converges
absolutely when Re(s)>1. Generic inversion represents its weighted sums,
but supplies no positive singularity at s=1. Its coefficients do not
identify a multiplicative L-series: a(1)=0, while a(2),a(3)>0 and a(6)=0.
The existing single-prime L-function estimates cannot be substituted for
an analytic continuation or nonzero singular term of D2.
Such a singularity is an input to this proposed argument, not a necessary
condition for every possible logarithmic gain.

The finite Fourier identity instead selects frequency 2 of a squared
Mangoldt exponential sum. Total nonnegative energy does not give a
positive lower bound for that Fourier coefficient. For example,
|1+e(3alpha)|^2 is nonnegative with frequency-2 coefficient zero. A signed
minor-arc bound preventing cancellation is still missing for this
major/minor-arc route. Logarithmic
averaging retains the same fixed frequency.

A distinct dispersion candidate does accept our coefficient class.
Fouvry-Radziwill Theorem 1.2 allows divisor-bounded factors and prime
moduli without a Siegel-Walfisz premise. In a rectangular subbox use
alpha_a=m_U(a) restricted to W-smooth squarefree a and a bounded prime
quotient coefficient; fix residue -2. Encoding the shifted prime q=ap+2
requires Q comparable to X=AP. The theorem requires
P<=Q^(-11/12)X^(17/36-epsilon), whose right side is then of size
X^(-4/9-epsilon). The application fails on its length condition.
[Primary source, Theorem 1.2](https://arxiv.org/html/1811.08672#S1.SS1).

For instance the range a of size X^(3/5), p of size X^(2/5) contains the
coefficient pattern a=r1*r2*r3 with distinct primes ri in (2U,3U], where
U=X^(1/5) and W=X^(1/4). Then m_U(a)=1 and all ri<=W eventually. This
squarefree pattern survives the existing gcd/square exclusions. No claim
that a particular ap+2 is prime is needed to test the theorem's range.
Using modulus p instead leaves a modulus-dependent shifted-prime weight
outside the fixed-convolution statement.

The inspected Wright extension retains M>Q(MN)^epsilon in Theorem 2.3,
so it also cannot reach this level-one encoding. This is a check of its
statement's applicability, not an independent validation of the preprint.
[Primary source, version 2, August 2026](https://arxiv.org/html/2604.25177v2#S2).

The next missing estimate remains signed and specific to the actual
composite-supported prime-beta weight. None of these checks proves the
required cofinal positive gain. M4-M6 remain incomplete.

## 6. Quadratic optimality does not supply the positive part

A follow-up audit of the power window found no improvement to the signed
budget. Barban-Vehov quadratic optimality, including its negative secondary
term, concerns the ordinary kernel 1/[d,e]. Expansion against Lambda(n+2)
instead leads to the odd-modulus kernel 1/phi([d,e]), together with the
even-modulus error. The secondary term cannot simply be transferred between
these kernels. The power-weighted versions remain quadratic estimates.
[Carneiro-Chirre-Helfgott-Mejia-Cordero, Theorem 1.1 and Corollary 1.3](https://arxiv.org/pdf/2005.03162),
[An, Theorem 1.1 and Corollary 1.2](https://arxiv.org/pdf/2206.10104).

There is a separate pointwise obstruction even if a suitable weighted square
estimate is supplied. Write Delta=log(R/S), m=m_(S,R), and
h(n)=Lambda(n+2)beta'_W(n)>=0. For primes ell,p with S<ell<R<=W<p,

\[
 m(\ell p)=\frac{\log(\ell/S)}{\Delta}\in(0,1),\qquad
 m_+(\ell p)-m(\ell p)^2=m(\ell p)(1-m(\ell p))>0.
\]

Thus m^2 is not a majorant for the needed positive part on composites.
The direct pointwise upper bound has the additional correction
sum_(n composite,0<m(n)<1) m(n)(1-m(n))h(n). This sum is not bounded here;
removing it through compensation from other ranges would require another
signed argument. Its semiprime subrange retains log p Lambda(ell p+2).

An exact witness uses X=100000, S=3=floor(X^(1/10)), R=10=floor(X^(1/5)),
and W=17=floor(X^(1/4)), with (RW)^2<X. The composite
n=100055=5*20011 lies in (X,2X], and 20011 and n+2=100057 are prime.
Its weighted defect is

\[
 (m_+(n)-m(n)^2)h(n)=
 \frac{\log(5/3)\log2\log20011\log100057}{\log^2(10/3)}>0.
\]

The exact checker [smoothing_check.py](../compute/smoothing_check.py) now
checks this third witness. After clearing the positive denominator, m has
numerator log5-log3 and 1-m has numerator log2. Integer-power comparisons
verify the floors; all primality and logarithmic signs are checked exactly.
This single witness rejects the pointwise inference, not an asymptotic
estimate of the correction.

Nor can polynomial combinations of the same normalized cutoff observables
alone make a pointwise prime minorant positive at primes: every squarefree
W-rough composite has m_(S,R)=1 for every R<=W and beta'_W(n)/log n=1,
the same tuple as a prime above W. The existing
[finite Type I switch](FAILED_APPROACHES.md) already realizes both cases
with prime shifts. This observation does not preserve the full distribution
data or the actual Mangoldt weights under switching.

Independent review also found no weakened definition or vacuity in the
[Lean logarithmic-gain endpoint](../TwinPrime/ConditionalClassicalCenter.lean).
The endpoint still requires an unproved cofinal gain; the moment audit has
not supplied it. No Lean source changed and no milestone is promoted.
