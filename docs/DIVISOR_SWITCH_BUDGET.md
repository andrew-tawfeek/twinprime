# Divisor switching and the remaining signed budget

Checkpoint: 2026-09-05. This paper test uses the actual shift two.
It adds no Lean hypothesis or endpoint. The verified middle-prime
bound remains T<=0.263 C X, and the
[complete budget](SIGNED_TOTAL_BUDGET.md) still has zero certified
positive margin. Here C=2 C2, Y=2X+2, L=log Y and W=floor(X^(21/100)).

## 1. The unrestricted divisor moment is available, but gives the wrong sign

Define

\[
 A(X)=\sum_{X<n\le2X}\Lambda(n+2)\log n,\qquad
 D_\tau(X)=\sum_{X<n\le2X}\Lambda(n+2)\tau(n)\log n.
\]

For every integer n>=2,

\[
 \Lambda(n)\ge \tfrac12(4-\tau(n))\log n.             \tag{1}
\]

There is equality at primes and prime squares. Every other composite
has at least four divisors, so the right side is nonpositive.
Multiplication by the actual nonnegative shifted weight and exact
prime-power removal give

\[
 Q_{\rm tw}(X)\ge 2A(X)-\tfrac12D_\tau(X)-E_{\rm pp}(X). \tag{2}
\]

No second square correction is added to Epp. In a prime-indicator
derivation, half the weighted prime-square input mass and the mass
with prime input and proper-prime-power output are disjoint parts
already contained in Epp.

The needed unrestricted divisor asymptotic is a proved external result,
not a conjectural prime-pair formula:
[Assing–Blomer–Li, *Uniform Titchmarsh divisor problems*, Theorem 1.1](https://arxiv.org/pdf/2005.13915).
The theorem already uses Lambda. With its sigma=1 and shift f=-2,
put

\[
 \kappa=\frac12\prod_{p>2}\left(1+\frac1{p(p-1)}\right)
        =\frac{\zeta(2)\zeta(3)}{3\zeta(6)}>0,\qquad
 d=2\gamma\kappa+2\kappa',
\]

where kappa' is the derivative at s=0 of the paper's Euler product
c_s(2). Its unweighted dyadic consequence is

\[
 \sum_{X<n\le2X}\Lambda(n+2)\tau(n)
 =\kappa X\log X+
   [\kappa(2\log2+2\gamma-1)+2\kappa']X
   +O_B(X/\log^B X)
\]

for each fixed B. Partial summation and the quantitative prime number
theorem then give

\[
 A(X)=\int_X^{2X}\log t\,dt+o(X),\qquad
 D_\tau(X)=\kappa\int_X^{2X}\log^2t\,dt+
             d\int_X^{2X}\log t\,dt+o(X).             \tag{3}
\]

For explicit residual accounting, let

\[
 r_A(t)=\sum_{2\le n\le t}\Lambda(n+2)-t,\qquad
 r_D(t)=\sum_{2\le n\le t}\Lambda(n+2)\tau(n)
                  -\kappa t\log t-(d-\kappa)t
\]

and define

\[
 {\cal V}_X(r)=\log(2X)|r(2X)|+\log X|r(X)|
                  +\int_X^{2X}|r(t)|\,\frac{dt}{t}.
\]

The two errors in (3) have absolute values at most V_X(r_A) and
V_X(r_D), respectively. Their prefix definitions retain the integer
floors and fixed initial terms. Taking B sufficiently large makes
both residuals o(X). Thus the fully accounted lower expression in
(2) is

\[
 2\int_X^{2X}\log t\,dt
 -\frac{\kappa}{2}\int_X^{2X}\log^2t\,dt
 -\frac d2\int_X^{2X}\log t\,dt
 -2{\cal V}_X(r_A)-\frac12{\cal V}_X(r_D)-E_{\rm pp}.
                                                               \tag{4}
\]

Its leading term is -kappa X log^2 X/2. This is substantially weaker
than the available nonnegativity bound. The theorem does not supply
a positive fraction of C X through this minorant.

This failure extends to any fixed polynomial P(tau(n)) that is a
global prime minorant away from prime squares and has P(2)>0.
Testing n=p^(k-1) requires P(k)<=0 for every integer k>=4. Its leading
coefficient must therefore be negative, and there exist fixed a,b>0
such that P(t)<=a-bt for every real t>=2. Consequently

\[
 \sum_{X<n\le2X}\Lambda(n+2)\log n\,P(\tau(n))
 \le aA(X)-bD_\tau(X)
 =-b\kappa X\log^2X+O(X\log X).
\]

This uses only the first divisor moment, not unproved higher moments.
A prime-square correction is o(X) and cannot repair that loss.
The conclusion is restricted to fixed coefficients and a global
pointwise minorant. It excludes neither rough-restricted moments nor
variable, nonpolynomial, or shift-dependent weights.

## 2. A rough restriction removes the large moment, with explicit defects

For all sufficiently large X, W^5>2X+2. Work on

\[
 {\cal G}_X=\{X<n\le2X:\ n\text{ is squarefree and W-rough},
                             \ n+2\text{ is prime}\}.
\]

Use w(n)=log n log(n+2), put

\[
 M_j=\sum_{\substack{n\in{\cal G}_X\\\Omega(n)=j}}w(n)
 \quad(1\le j\le4),\qquad
 M=\sum_{j=1}^4M_j,\qquad D=\sum_{j=1}^4 2^jM_j .
\]

Every input in this set has 1<=Omega(n)<=4 and tau(n)=2^Omega(n).
Conversely every genuine twin input in the dyadic interval belongs
to this set. Therefore M_1=Q_tw exactly.

These restrictions are not free. Safe budgets for the removed
log(n)Lambda(n+2) mass are

\[
 \begin{split}
 \Delta_{\rm sf}
 &\le 2XL^2\sum_{p>W}p^{-2}\le 2XL^2/W,\\
 \Delta_{\rm shift}
 &\le \log(2X)[\psi(Y)-\vartheta(Y)]
       \le K\sqrt Y\log(2X).
 \end{split}                                                    \tag{5}
\]

The first uses the count of multiples of p^2 and a union bound.
The second uses the actual
[proper-prime-power Mangoldt bound](../TwinPrime/Analytic/NonprimeMangoldtTail.lean).
The divisor moment changes by at most 16 times the sum of these
budgets, since tau(n)<=16 on the full rough support.

The shifted-power defect here includes composite inputs and is not
automatically bounded by the W2-based Epp. Both defects in (5) are
o(X). Their overlap is harmless in this upper budget.

On retained squarefree inputs beta'_W(n)=log n. Thus the existing
[rough beta mass](ROUGH_COMPOSITE_SIEVE_BOUND.md) differs from M
only on the removed terms, and (5) yields

\[
 4C\log(29/21)X-o(X)\le M\le4CX+o(X).               \tag{6}
\]

There is no extra Epp to subtract when working with M_1: the shifted
output is already prime and M_1 is the genuine twin sum.

## 3. The sharp first-moment target and its complete divisor remainder

Nonnegative M_j satisfy D>=2M_1+4(M-M_1), so

\[
 Q_{\rm tw}=M_1\ge\max(0,\,2M-D/2).                \tag{7}
\]

This is the optimal bound using only M and D. If D/M is between
2 and 4, a mixture of the j=1 and j=2 classes attains it. If D/M
is between 4 and 16, a mixture of j=2 and j=4 attains zero.
The case M=0 is immediate.

Accordingly a sufficient new arithmetic estimate is

\[
 D\le4M-2\delta CX
\]

cofinally for some fixed delta>0. This would directly give a positive
total budget. If one uses only the separate lower certificate (6),
an independent upper coefficient for D would have to be below
16 log(29/21), approximately 5.16437, with strict slack. No such
restricted moment estimate is supplied by the unrestricted theorem
in Section 1.

The finite hyperbola decomposition shows what that missing moment
actually contains. Squarefreeness and n>1 give

\[
 \tau(n)/2=\#\{d\mid n:d<\sqrt n\}.
\]

Every nonunit divisor below sqrt(n) has at most two prime factors,
because (W+1)^3>sqrt(2X) eventually. Define S_p and S_pp as the
w(n)-weighted counts of prime and semiprime divisors below sqrt(n).
Then

\[
 D/2=M+S_p+S_{pp},\qquad
 M-S_p-S_{pp}=M_1-2M_3-6M_4.                       \tag{8}
\]

The prime-divisor sum has the exact range

\[
 q>W\text{ prime},\quad
 \max(q,\lfloor X/q\rfloor)<r\le\lfloor2X/q\rfloor,
\]

with r squarefree and W-rough, (q,r)=1 and qr+2 prime. Its weight
is log(qr)log(qr+2).

The semiprime-divisor sum has W<p<q prime, (pq)^2<2X and

\[
 \max(pq,\lfloor X/(pq)\rfloor)<r\le\lfloor2X/(pq)\rfloor,
\]

with r squarefree and W-rough, (pq,r)=1 and pqr+2 prime. Here
Omega(r)<=2. This entire nonnegative remainder must be kept when
charging the upper losses in (8).

There is a stronger exact identity if one keeps the multiplicity
correction:

\[
 M_1=M-S_p+D_{\rm mult},\qquad
 D_{\rm mult}=
 \sum_{\substack{n\in{\cal G}_X\\n\text{ composite}}}
 w(n)\bigl(\#\{p\mid n:p<\sqrt n\}-1\bigr)\ge0.       \tag{9}
\]

Discarding it loses positive triple- and quadruple-factor mass.
Equivalently, the disjoint least-prime decomposition imposes that
every prime divisor of r exceed q. Thus a successful switch needs
either a bound for the complete signed combination or new information
about this multiplicity correction; counting a divisor twice is not
a new saving.

## 4. A switched upper sieve gives a finite bound, but an excessive charge

To test the difficult balanced region, retain only
X^(21/50)<q<=X^(1/2) in S_p and call its mass S_bal. Reverse the order
of summation and fix r. It lies in

\[
 X^{1/2}<r\le2X^{29/50}.
\]

Enlarge the q range to

\[
 I_r=(\max(X/r,X^{21/50}),\ \min(2X/r,X^{1/2})],
 \qquad
 \ell_r=\max\left(0,\min(2X/r,X^{1/2})-\max(X/r,X^{21/50})\right).
\]

This retains both clipped endpoints and only increases the upper
count. Dropping the conditions q<r and (q,r)=1 is permitted for
this nonnegative upper bound. Rough r has at most two prime factors
throughout this enlarged range.

For these odd r and the forms q and rq+2, the number of excluded residues modulo p is
nu_r(p)=1 if p divides 2r and 2 otherwise. Their singular series is

\[
 {\mathfrak S}_r=C\prod_{\substack{p\mid r\\p>2}}
                       \frac{p-1}{p-2}=C(1+O(W^{-1})).
\]

The finite interval Selberg theorem gives

\[
 \#\{q\in I_r:q,\ rq+2\text{ prime}\}
 \le\frac{\ell_r}{G_r(z_r)}
          +z_r^2(1+\log(z_r^2))^5,                 \tag{10}
\]

where Q_r=X/r, z_r=sqrt(Q_r)/log^10(Q_r), and

\[
 G_r(z)=\sum_{d\le z}\mu(d)^2
                    \prod_{p\mid d}\frac{\nu_r(p)}{p-\nu_r(p)}.
\]

The integer-counting remainders satisfy |R_r(d)|<=nu_r(d).
On squarefree support tau_3(d)nu_r(d)<=6^omega(d)<=tau_6(d);
summing tau_6 up to z_r^2 gives the displayed error. This is the
finite theorem, rather than an assumed uniform prime-pair asymptotic.
See [Tao, Notes 4, Theorem 30 and Lemma 29](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/).

Uniformity in the growing coefficient r is explicit. If G_1 is the
fixed twin-form denominator, positivity of its coefficients gives

\[
 G_r(z)\ge
 \left(1-\sum_{p\mid r}\frac2{p-2}\right)G_1(z),\qquad
 G_1(z)=\frac{\log^2z}{2C}+O(\log z).
\]

The sum is O(1/W), since there are at most two distinct prime factors
of r. The resulting elementary leading constant is 8C, not 4C:
log(z_r) is asymptotic to half log(Q_r).
The normalization 2^k k!=8 for k=2 is in the same source's Theorem 32.

For complete residual accounting, let both sums below run over **all**
W-rough integers sqrt(X)<r<=2X^(29/50). This is a nonnegative
enlargement: squarefreeness and the existence of a suitable prime q
or prime rq+2 are not restrictions on this r-sum. Set

\[
 {\cal U}_X=L^2\sum_r\frac{\ell_r}{G_r(z_r)},\qquad
 {\cal E}_{\rm sieve}=L^2\sum_r z_r^2(1+\log(z_r^2))^5 .
\]

These are finite nonnegative quantities, and S_bal<=U_X+E_sieve.
Even summing the error over all integers r gives
E_sieve=O(X/log^12 X)=o(X). The prime output condition is already
part of the retained set, so no second shifted-power defect is added.

Put v=21/100. Ordinary unweighted rough-number summation gives

\[
 K_{\rm bal}=\frac8v\int_{21/50}^{1/2}
                  \frac{\omega((1-t)/v)}{t^2}\,dt,\qquad
 S_{\rm bal}\le C K_{\rm bal}X+
             |{\cal U}_X-CK_{\rm bal}X|+{\cal E}_{\rm sieve}.
                                                               \tag{11}
\]

The actual main-sum discrepancy in (11) retains denominator and
singular-factor errors, W rounding, logarithmic weights and the
clipped endpoints. It is o(X). The endpoint transition regions
[X^(1/2),2X^(1/2)] and [X^(29/50),2X^(29/50)] contribute O(X/log X).

Only 2<log r/log W<3 occurs here for large X, so the unweighted
rough count is a sum over primes and semiprimes. PNT and partial
summation give uniformly
Phi(y,W)=y omega(log y/log W)/log W+O(y/log^2 y), with
omega(u)=(1+log(u-1))/u for 2<u<3.
This statement has no shifted-prime weight. A precise general form is
[Matomäki–Zuniga–Alterman, Lemma 2.1](https://www.utupub.fi/bitstream/handle/10024/185534/Matom%C3%A4ki_and_zuniga_weighted_sieves_2025.pdf?isAllowed=y&sequence=1).
Use z=W+1 in the source's strict prime convention; replacing its
log(z) by log(W) is included in the main-sum discrepancy in (11).

The upper *charge* in (11) is already too large:

\[
 K_{\rm bal}\ge8\int_{21/50}^{1/2}\frac{dt}{t^2(1-t)}
 \ge8\cdot8(1/2-21/50)=128/25=5.12.                \tag{12}
\]

Here omega(u)>=1/u and t^2(1-t)<=1/8 on the interval. This exceeds
even the available upper coefficient 4 for M in (6), before charging
the other prime divisors and S_pp. It is a lower bound for the
coefficient of this particular *upper estimate*, not for actual S_bal.

The elementary pointwise cap S_bal<=M is better: two such prime
divisors below sqrt(n) would require a third rough factor, making
n>X^(21/50+21/50+21/100)>2X eventually. The cap restores only a
zero budget before the other losses; the switched upper estimate
does not improve it. Nor may the favorable D_mult in (9) be counted
without an independent estimate.

## 5. More moments specify new arithmetic, not a supplied gain

For F_j=sum_(n in G) w(n) binomial(Omega(n),j), the exact finite
four-state problem gives

\[
 M_1\ge\max\left(0,\frac{8F_0-5F_1+2F_2}{3}\right),\qquad
 \frac{8F_0-5F_1+2F_2}{3}=M_1-M_3/3,
\]

and

\[
 M_1=4F_0-3F_1+2F_2-F_3.                            \tag{13}
\]

The first bound is optimal from those three moments. The second is
an exact selector, but its third factorial moment contains divisors
that are products of three primes above W, hence exceed X^(63/100).
Direct BV does not reach those moduli. Switching to the cofactor
retains the triple-prime and shifted-prime restrictions; ordinary
progression counts do not evaluate that restricted sum.

The current estimates prove neither the strict first-moment inequality
following (7) nor a positive lower bound for (13). A genuine gain
M_1>=delta C X would improve the *complete* loss T+R and would not
require another 0.263 saving. The errors needed for the proposed
moment applications are now explicit, but no such gain has been
obtained. This route therefore does not justify substantial further
formalization at this checkpoint.
