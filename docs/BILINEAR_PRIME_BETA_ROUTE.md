# Prime-only beta and the small-prime-part reduction

Research checkpoint: 2026-09-05. This note records finite cancellation and an
absolute error estimate, then identifies an unresolved arithmetic subrange.
It does not prove B*. The earlier [failed approaches](FAILED_APPROACHES.md),
[sign review](BILINEAR_SIGN_REVIEW.md), and
[asymptotic-sieve application audit](ASYMPTOTIC_SIEVE_REVIEW.md) remain relevant.
The subsequent [cutoff-change proof](CUTOFF_SHIFT_ROUTE.md) raises the right
cutoff with a proved signed o(X) error and records the resulting mixed
coefficient and remaining range.

Write C=2C2>0 for the singular constant in PLAN, and

\[
 b_{U,V}=\mu_{>U}*\beta_V,\qquad
 \beta_V(r)=\sum_{\substack{d\mid r\\d>V}}\Lambda(d),\qquad
 m_U(a)=\sum_{\substack{d\mid a\\d\le U}}\mu(d).
\]

All factors below are positive integers. A positive integer is U-smooth if
every prime factor is at most U, and U-rough if every prime factor exceeds U;
1 satisfies both conditions. Their canonical factorization n=ab includes
all prime-power multiplicities in the appropriate factor.

## 1. Checked identities for the original beta

[BilinearSmallPart.lean](../TwinPrime/Analytic/BilinearSmallPart.lean) has passed
standalone checking, the root build and independent mathematical review. It proves:

* If 1<a<=U and b is U-rough, then b_(U,U)(ab)=0. Neither factor needs to be
  squarefree, and b=1 is included.
* If a is squarefree and U-smooth, and b is U-rough, then
  b_(U,U)(ab)=Lambda_(>U)(ab)-m_U(a)log b. Only a needs to be squarefree.
  When ab>U the first term is Lambda(ab).
* If p,q are distinct primes with p,q<=U<pq, then
  b_(U,U)(pqb)=log b>=0 for every positive U-rough b.

The proofs restrict low divisors to the smooth factor and retain their signed
sum. They do not restrict a factorwise signed inequality to a smaller set.
For a large smooth part with repeated primes, the second identity cannot be
used for the original beta: small primes can have powers above U.

## 2. Removing prime powers inside beta

Define

\[
 \beta'_V(r)=\sum_{\substack{p\mid r\\p>V,\ p\ \mathrm{prime}}}\log p.
\]

Then beta_V-beta'_V is the nonnegative divisor sum of
nonprimeMangoldt(d)=1_(d not prime)Lambda(d) over d>V. This removes prime-power
**divisors of r**, separately from the earlier removal of prime-power inputs
n or shifted inputs n+2.

[NonprimeMangoldtTail.lean](../TwinPrime/Analytic/NonprimeMangoldtTail.lean)
has passed standalone checking, the root build and independent review. From the actual
Chebyshev bound psi(t)-theta(t)<=C_pp sqrt(t), finite Abel summation proves

\[
 \sum_{V<d\le T}\frac{\operatorname{nonprimeMangoldt}(d)}d
 \le 3C_{\rm pp} V^{-1/2}\quad(V\ge1),
\]

including T<V. No distribution hypothesis occurs in this theorem.

For L=log(4X+4), X>=1 and V>=1, the factorwise application is

\[
 \sum_{\substack{d>U,r>V\\X<dr\le2X}}
 |\mu(d)(\beta_V(r)-\beta'_V(r))\Lambda(dr+2)|
 \le 4XL^2\sum_{V<e\le2X}\frac{\operatorname{nonprimeMangoldt}(e)}e
 \ll XL^2/\sqrt V.                                      \tag{1}
\]

Indeed the number of positive pairs dr<=2X with e|r is at most
(2X/e)(1+log(2X)); use |mu|<=1, Lambda(dr+2)<=L and
1+log(2X)<=2L. At V=floor(X^(1/5)), (1) is o(X). Absolute factorwise mass
also permits additional factor restrictions. An o(X) replacement transfers
lower bounds with fixed positive slack; it does not preserve an exact
threshold such as -CX/2 without allowing for that error.

**Checked source map:** all seven modules below passed the full root build
(8902 jobs), individual Lean compilation and independent source review.

| Module | Actual result |
|---|---|
| [BilinearSmallPart](../TwinPrime/Analytic/BilinearSmallPart.lean) | The original-beta identities in Section 1. |
| [NonprimeMangoldtTail](../TwinPrime/Analytic/NonprimeMangoldtTail.lean) | The actual nonnegative reciprocal tail above V. |
| [BilinearPrimeBeta](../TwinPrime/Analytic/BilinearPrimeBeta.lean) | Actual factorwise error mass and the finite factor-4 bound in (1). |
| [PrimeBetaGrowth](../TwinPrime/Analytic/PrimeBetaGrowth.lean) | L^k/sqrt(primaryCutoff(X)) tends to zero for every fixed natural k. |
| [PrimeBetaReduction](../TwinPrime/Analytic/PrimeBetaReduction.lean) | One positive uniform constant in (1); normalized mass and signed-difference limits, even after multiplication by L^k. These hold for every left-cutoff function U(X), with V(X)=primaryCutoff(X). |
| [PrimeBetaSmallPart](../TwinPrime/Analytic/PrimeBetaSmallPart.lean) | Exact all-positive smooth/rough coefficient identity and distinct-prime-log weight described below. |
| [PrimeBetaGrouping](../TwinPrime/Analytic/PrimeBetaGrouping.lean) | The exact reindexing from the factor sum to its grouped convolution, with both strict cutoffs and all natural endpoints. |

The uniform error bound requires V>=1 and X>=1; it places no restriction on U.
All 52 new public theorems occur in the integrated audit of 1200 unique
selected declarations, with only Classical.choice, propext and Quot.sound.
The audit reported no errors; the 247-file project source scan found no
proof holes or trust bypasses. B* remains an explicit unproved premise.

## 3. The prime-only identity needs no squarefreeness

Put P_U(n)=1_(n prime and n>U)log n and b'_U=mu_(>U)*beta'_U. For the canonical
smooth/rough factorization n=ab,

\[
 b'_U(n)=P_U(n)-m_U(a)\log\operatorname{rad}(b).             \tag{2}
\]

Here rad(b) is the product of the distinct prime divisors of b, with rad(1)=1.
The checked Lean theorem gives exactly P_U(ab)-m_U(a)beta'_U(b), and another
checked theorem gives beta'_U(b)=sum_(p in primeFactors(b)) log p for rough b.
Writing this last finite sum as log rad(b) is paper notation here, not an
exported radical-identity theorem.
To prove (2), write beta'_U=P_U*1, so mu*beta'_U=P_U. Every divisor d<=U of ab
divides a; for each such d, beta'_U((a/d)b)=log rad(b). This factors the low
convolution exactly. Repeated factors in a or b cause no change to the proof.

Useful paper sign ranges follow:

* b=1 gives zero for every U-smooth n>U.
* If a>1 and rad(a)<=U, then m_U(a)=0, including cases a>U.
* If a>1 and every distinct pair of prime divisors of a has product>U, then
  m_U(a)=1-omega(a)<=0; hence b'_U(ab)>=0. In particular this holds when every
  prime of a exceeds sqrt(U). Powers of those primes are permitted.

Thus a nonrough negative coefficient requires a pair of distinct small primes
p,q with pq<=U. This is a genuine sign restriction, not a bound for their
weighted mass. The class a=1 still gives zero on primes and -log n on rough
squarefree composites. All such squarefree inputs survive the previous gcd
and large-square removals.

## 4. A specific remaining range and the first invalid BV step

Take U=floor(X^(1/5))>=2. If

\[
 \left\lceil2X/U^2\right\rceil\le a\le
 \left\lfloor2X/(U+1)\right\rfloor,\qquad X<ab\le2X,
\]

and b>1 is U-rough, then b<=U^2, so b is prime. A composite rough b would
be at least (U+1)^2. Consequently an exact surviving contribution is

\[
 -\sum_{\substack{a\ U\text{-smooth}\\
       \lceil2X/U^2\rceil\le a\le\lfloor2X/(U+1)\rfloor}}
 m_U(a)
 \sum_{\substack{p>U\ {\rm prime}\\X<ap\le2X}}
       \log p\,\Lambda(ap+2).                            \tag{3}
\]

Here a ranges approximately from X^(3/5) to X^(4/5), while p ranges from
X^(1/5) to X^(2/5). The coefficient m_U(a) remains signed; no uniform favorable
sign was proved for this range.

Taking modulus a lies beyond classical BV. Switching to the prime modulus p
puts it below X^(2/5), but leaves the smoothness condition and m_U(a) inside
the progression sum. Expanding m_U(a) produces

\[
 -\sum_{p>U\ {\rm prime}}\log p\sum_{d\le U}\mu(d)
 \sum_{\substack{c\ U\text{-smooth}\\dc\text{ in the displayed }a\text{ range}\\
                       X<pdc\le2X}}\Lambda(pdc+2).
\]

The first unsupported step is replacing this restricted inner sum by the
unweighted progression main term or error supplied by BV. Even when pd is
within the allowed level, c is restricted to smooth integers. Moreover pd can
reach U^3, approximately X^(3/5), beyond that level. Inclusion-exclusion to
remove smoothness introduces further moduli, not an automatic saving. Even
moduli retain the separate power-of-two contribution; the same obstruction
already occurs for odd, squarefree a.

Ordinary Mertens does not control these weights. Already on U<a<=2U, smooth
a are precisely the composite a, m_U(a)=-mu(a), and exactly

\[
 \sum_{\substack{U<a\le2U\\a\ U\text{-smooth}}}\mu(a)
 =\mathcal M(2U)-\mathcal M(U)+\pi(2U)-\pi(U).
\]

Discarding the smoothness restriction changes even this unweighted mean.
The prime-weighted version in (3) requires additional information.

Finally, fix U=V=floor(X^(1/5)) as X tends to infinity through natural numbers.
Equation (2) gives B'=W_prime-S, where
S=sum_(X<n<=2X) m_U(a(n))log rad(b(n))Lambda(n+2), and
W_prime=sum_(X<n<=2X, n prime) log n Lambda(n+2).
The exact
[correlation decomposition](../TwinPrime/Analytic/Decomposition.lean) gives
W2=A+(H-I)+B. Therefore

\[
 S=A+(H-I)+(B-B')-(W_2-W_{\rm prime}).
\]

The proved classical inputs give A=CX+o(X), H-I=o(X); the proved
prime-power bound gives W2-W_prime=o(X). Estimate (1) supplies B-B'=o(X).
Thus S=CX+o(X) is a paper consequence of these actual statements with this
fixed cutoff; its assembled asymptotic is not a new Lean theorem here.
Positivity of W_prime then
recovers only B'>=-CX+o(X), with no positive surviving fraction. The proper
subrange (3) is more specific than the full B*, but no estimate for it obtained
here supplies that missing margin.
The Friedlander-Iwaniec audit does not bypass this step: its required
distribution level and additional bilinear estimate remain separate obligations.
