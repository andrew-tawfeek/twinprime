# The rough composite loss at the raised cutoff

Checkpoint: 2026-09-05. This is a paper derivation using the classical
upper and lower linear sieve, together with the repository's proved BV
and proper-prime-power estimates. It is not a new Lean asymptotic theorem.
It gives an actual bound for a remaining class and identifies precisely
what that bound does not establish. B* remains open.

## 1. Preserve the composite restriction

Let X tend to infinity through positive integers, put

\[
 W=\lfloor X^{21/100}\rfloor,\qquad
 C=2\,\mathrm{twinPrimeConstant},\qquad Y=2X+2.
\]

Call a positive integer W-rough when every prime divisor exceeds W. Define

\[
 \begin{split}
 N_{\rm rough}(X)
   &=\sum_{\substack{X<n\le2X\\n\ W\text{-rough, composite}}}
          \beta'_W(n)\Lambda(n+2),\\
 P(X)&=\sum_{\substack{X<n\le2X\\n\text{ prime}}}
          \log n\,\Lambda(n+2),\\
 S(X)&=\sum_{\substack{X<n\le2X\\n\ W\text{-rough}}}\Lambda(n+2),\\
 H(X)&=\sum_{\substack{X<n\le2X\\n\ W\text{-rough}}}
          \beta'_W(n)\Lambda(n+2).
 \end{split}                                                    \tag{1}
\]

Here beta'_W(n) is the sum of log p over distinct prime divisors p>W.
For X>W, every prime n in the interval is W-rough and has beta'_W(n)=log n.
Since n>1, the prime/composite partition gives the exact identity

\[
 H(X)=P(X)+N_{\rm rough}(X).                         \tag{2}
\]

The composite exclusion is therefore retained explicitly throughout; it
is not replaced by an assumption that primes make a negligible contribution.

The resulting bounds are

\[
 \boxed{\quad
 4C\log(29/21)
 \le\liminf_{X\to\infty}\frac{N_{\rm rough}(X)+P(X)}X
 \le\limsup_{X\to\infty}\frac{N_{\rm rough}(X)+P(X)}X
 \le4C.\quad}                                      \tag{3}
\]

In particular,

\[
 N_{\rm rough}(X)\le4CX-P(X)+o(X),\qquad
 \limsup\frac{N_{\rm rough}(X)}X\le4C.              \tag{4}
\]

## 2. The repeated-factor defect is controlled

For positive W-rough n, the divisor identity for log n gives

\[
 \begin{split}
 0\le\log n-\beta'_W(n)
 &=\sum_{d\mid n}\mathrm{nonprimeMangoldt}(d)\\
 &=\sum_{\substack{d\mid n\\d>W^2}}
                       \mathrm{nonprimeMangoldt}(d).             \tag{5}
 \end{split}
\]

Indeed every nonzero summand is d=p^j with j>=2, and roughness forces p>W,
so d>W^2. This is why replacing beta by log here needs no squarefreeness
assumption, provided its error is included.

Let K>0 be the uniform constant in the proved
[NonprimeMangoldtTail](../TwinPrime/Analytic/NonprimeMangoldtTail.lean):
for V>=1 and every T,
sum_(V<d<=T) nonprimeMangoldt(d)/d <= K V^(-1/2).
Using Lambda(n+2)<=log Y, nonnegativity, and at most floor(2X/d) multiples
of d in the larger interval 1<=n<=2X, (5) implies, for W>=1,

\[
 \begin{split}
 0\le\mathcal D(X)
 &:=\sum_{\substack{X<n\le2X\\n\ W\text{-rough}}}
            \Lambda(n+2)(\log n-\beta'_W(n))\\
 &\le2X\log Y\sum_{W^2<d\le2X}
               \frac{\mathrm{nonprimeMangoldt}(d)}d
 \le\frac{2KX\log Y}{W}=o(X).                      \tag{6}
 \end{split}
\]

This argument also covers an empty reciprocal-tail interval. It uses a
prefix count of multiples, so no unsummed '+1 per prime power' error is
introduced. Consequently

\[
 \log X\,S(X)-\mathcal D(X)
       \le H(X)\le\log(2X)\,S(X).                 \tag{7}
\]

## 3. The actual shifted-prime sieve and its endpoints

Sieve the nonnegative sequence a(n)=1_(X<n<=2X)Lambda(n+2) by the odd primes
at most W. Write S_odd(X,W) for the resulting sum. For every odd squarefree
sieve modulus d, its exact multiples sum is

\[
 \sum_{\substack{X<n\le2X\\d\mid n}}\Lambda(n+2)
 =\psi(2X+2;d,2)-\psi(X+2;d,2)
 =X/\phi(d)+r_X(d),\qquad |r_X(d)|\le2E_d(Y).       \tag{8}
\]

The endpoints have difference exactly X. The residue 2 is reduced for all
these odd moduli. Thus the density is g(p)=1/(p-1) for odd primes and the
main mass is X. No distribution of a prime-pair sequence is assumed.

The distinction between odd-prime sifting and actual roughness matters
for the lower bound. For the eventual range W>=2, any additional even n counted by S_odd has nonzero
Lambda(n+2) only if n+2 is a power of 2. Hence

\[
 0\le S_{\rm odd}(X,W)-S(X)
   \le\sum_{2^j\le Y}\log2\le\log Y.              \tag{9}
\]

After multiplication by log X this is still o(X). All other prime powers
remain in the sequence; none is silently discarded.

The external theorem is the standard linear sieve with main factors F(s)
and f(s), dimension-one product condition, level D, and s=log D/log z>=1.
For each fixed approximation parameter its remainder coefficients are
bounded independently of X (or are a fixed finite sum of bounded
components). The theorem and normalizations are stated in
[Lichtman, *A modification of the linear sieve, and the count of twin primes*, Theorem 2.10 and equations (2.3)--(2.5), version 2 (2024-02-14)](https://arxiv.org/html/2109.02851v2#S2.SS2),
with attribution to Iwaniec and *Opera de Cribro*. Multiplying the pointwise
sieve inequalities by the nonnegative a(n) gives the weighted version used
here. For 2<s<=3 the defining equations give

\[
 F(s)=\frac{2e^\gamma}{s},\qquad
 f(s)=\frac{2e^\gamma}{s}\log(s-1).                 \tag{10}
\]

Take D=X^(1/2)/log^B X with B sufficiently large for BV, and z=W+1 to sieve
exactly the primes at most W. Then s tends to 50/21, which lies strictly
between 2 and 3. The product normalization is

\[
 V(z)=\prod_{2<p<z}\left(1-\frac1{p-1}\right)
       \sim\frac{Ce^{-\gamma}}{\log z}.             \tag{11}
\]

BV and (8) make the remainder o(X/log X), after fixing the sieve
approximation parameter; let that parameter decrease to zero after the
limit. From (10)--(11) we obtain

\[
 \begin{split}
 \limsup\frac{\log X}{X}S_{\rm odd}(X,W)&\le4C,\\
 \liminf\frac{\log X}{X}S_{\rm odd}(X,W)
     &\ge4C\log(29/21).                            \tag{12}
 \end{split}
\]

There is also a route matching the existing fixed-power distribution
exports: first use D=floor(X^a) for fixed 42/100<a<1/2. The corresponding
constants are 2C/a and (2C/a)log(a/(21/100)-1). Letting a increase to 1/2
recovers (12); no uniformity in a is needed. Equations (6)--(9) and (2)
then prove (3).

## 4. The exact prime term and the remaining allowance

Let

\[
 T_{\rm twin}(X)=
 \sum_{\substack{X<n\le2X\\n,n+2\text{ prime}}}
                 \log n\log(n+2).
\]

The difference P-T_twin consists only of prime n with a proper-prime-power
shift. In the repository's notation,

\[
 0\le P(X)-T_{\rm twin}(X)\le E_{\rm pp}(X)=o(X).  \tag{13}
\]

This uses the actual error from [Correlation](../TwinPrime/Correlation.lean)
and its [logarithmic precision](../TwinPrime/Analytic/PrimePowerLogPrecision.lean).
Thus P has not been assumed small; replacing it by the twin contribution
is justified only with the explicit error (13).

Numerically, 4log(29/21)=1.291093569052204... . The simple upper sieve
certifies only 4 C X for N_rough by itself, not the approximately 0.737 C X
allowance left after the middle-prime estimate at v=0.21 in
[MIDDLE_PRIME_SIEVE_BOUND](MIDDLE_PRIME_SIEVE_BOUND.md).

The lower inequality gives a precise diagnostic for a proposed stronger
bound. If one independently proved
N_rough<=(737/1000) C X+o(X), even just cofinally, then (3) and (13) would
force a positive twin contribution on those scales, with coefficient at
least

\[
 C\bigl(4\log(29/21)-737/1000\bigr)>0.             \tag{14}
\]

Positivity does not depend on a decimal calculation: log(1+x)>=x/(1+x)
for x>=0 implies

\[
 4\log(29/21)-737/1000
 \ge32/29-737/1000=10627/29000>0.
\]

No bound of that strength has been proved here. Furthermore, controlling
N_rough alone would not justify dropping the separate signed quantity
N_comp-P_comp in the full partition: the outstanding combined requirement
is still N_rough+N_comp-P_comp within the remaining allowance. Equations
(3)--(4) show that the simple sieve does not close a budget based only on
upper bounds for the losses. They do not prove that every possible signed
combination or refined sieve argument must fail.

The elementary defect and endpoint arguments above are paper derivations
from checked repository inputs. The cited upper/lower linear-sieve step,
its asymptotic assembly, and the resulting rough-class constants have not
been exported as Lean theorems in this note.
