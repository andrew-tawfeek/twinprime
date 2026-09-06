# Finite sign structure and an exceptional-range estimate

This investigates Experiment C in `PLAN.md` Section 7.4. The identities and
inequalities below have elementary proofs given here. The executable checks
validate finite instances independently; they do not prove asymptotic estimates.
The main signed bound (B*) remains unproved.

For positive integers `U,V`, write

\[
 b_{U,V}(n)=\sum_{\substack{d\mid n\\d>U}}\mu(d)\beta_V(n/d),
 \qquad B_{U,V}(X)=\sum_{X<n\le 2X}b_{U,V}(n)\Lambda(n+2).
\]

Here `beta_V(r)` is the exact coefficient already defined in the plan. In
particular `beta_V(1)=0`. All interval endpoints below are integer endpoints.

## 1. What the coefficient detects

**Primes vanish.** If `n=p` is prime, its divisors are `1,p`. The divisor `1`
does not exceed `U`, and the possible divisor `p` contributes
`mu(p) beta_V(1)=0`. Thus `b(p)=0` for every positive pair of cutoffs.

**Semiprimes have an explicit nonpositive coefficient.** For distinct primes
`p,q`, only the divisors `p,q` can contribute:

\[
 b(pq)=-\mathbf1_{p>U}\mathbf1_{q>V}\log q
        -\mathbf1_{q>U}\mathbf1_{p>V}\log p.
\]

The divisor `pq` has quotient 1 and contributes zero. For a square,
`b(p²) = -1_{p>U} 1_{p>V} log p`. With `U=V=z`, a semiprime coefficient is
zero if either prime is at most `z`; otherwise it is `-log(pq)` for distinct
primes and `-log p` for a square. Treating squares as two distinct divisors would
incorrectly double their contribution.

**All prime powers can be bounded uniformly.** For any prime `p` and `a>=1`,

\[
 b(p^a)=-\mathbf1_{p>U}
       \#\{k:1\le k\le a-1,\ p^k>V\}\log p.
 \tag{1}
\]

Indeed, the only squarefree divisors of `p^a` are `1,p`; their roles are as
above. Consequently `-log(p^a) <= b(p^a) <= 0`, independently of the cutoffs.

**Rough composites do not alternate signs with their number of factors.** If
every prime divisor of `n` exceeds `max(U,V)`, then

\[
 \boxed{b_{U,V}(n)=\Lambda(n)-\log n.}
 \tag{2}
\]

Every divisor greater than 1 then exceeds both cutoffs. Thus
`beta_V(r)=sum_{b|r} Lambda(b)=log r` for every `r|n`, and the only divisor
at most `U` is 1. Subtracting its contribution from
`sum_{d|n} mu(d) log(n/d)=Lambda(n)` proves (2). These two convolution identities
are also proved directly by counting prime exponents and summing over subsets
of the distinct prime divisors.

If `n` has at least two distinct prime divisors, (2) is exactly `b(n)=-log n`,
whether `n` is a semiprime, a product of three or more primes, or has repeated
prime factors. Higher-factor terms therefore cannot be discarded as favorable.
Prime powers give `b(p^a)=-(a-1)log p` in this rough range.

Grouping terms before taking absolute values saves a precisely measurable loss.
For squarefree rough `n` with `k>=2` distinct prime factors, the sum of the
positive factorwise contributions is `(2^(k-2)-1) log n`, and the absolute sum
of the negative factorwise contributions is `2^(k-2) log n`. To see this, fix a
prime factor `p`. Its logarithm occurs for squarefree divisors formed from the
other `k-1` primes. There are `2^(k-2)` odd subsets and `2^(k-2)-1` nonempty
even subsets. Therefore the full factorwise absolute sum is
`(2^(k-1)-1) log n`, although the actual coefficient is only `-log n`.

This is a real finite improvement over dropping positive factor terms. It
does not bound the weighted mass of rough composites, or establish a fixed
positive margin in the total `CX` budget.

## 2. Switching exposes a signed small-divisor coefficient

Define `m_U(a)=sum_{d|a,d<=U} mu(d)`. Reversing the order of the two divisor sums
gives the exact identity

\[
 b_{U,V}(n)=
 \sum_{\substack{p^k\mid n\\p^k>V}}\log p
   \bigl(\mathbf1_{n=p^k}-m_U(n/p^k)\bigr).
 \tag{3}
\]

Here `p` is prime and `k>=1`. The inner tail of the Möbius divisor sum equals
`1_{n/p^k=1}-m_U(n/p^k)` because its complete sum is the convolution identity
`mu*1=epsilon`. No sign estimate was used. On `n>V`, the indicator part sums to
`Lambda(n)`.

There is an especially simple family. Let `a>1` be squarefree with every prime
factor at most `V`, let `q>max(U,V)` be prime, and suppose `q` does not divide
`a`. Then

\[
 b_{U,V}(aq)=-m_U(a)\log q.
 \tag{4}
\]

In a quotient containing `q`, its logarithm is the only prime-power logarithm
above `V`. Quotients without `q` contribute zero. Summing the remaining divisors
of `a` above `U` gives `-m_U(a)` since `a>1`.

The coefficient `m_U(a)` has no universal sign or upper bound of 1. Switching
therefore exposes sign information that still has to be controlled on the
shifted-prime sequence; it does not remove that obligation.

## 3. Exact counterexamples within the plan's canonical intervals

All rows use `U=V=floor(X^(1/5))` and `X<n<=2X`; the shifted value in each row
is prime. Primality was checked individually by trial division through the
integer square root, including the one larger witness. No large enumeration
was performed.

| X | U=V | n and its factorization | n+2 | Exact b(n) | Rejected shortcut |
|---:|---:|---|---:|---|---|
| 1,000 | 3 | 1,085 = 5·7·31 | 1,087 | `-log 1085` | Discard rough terms with at least three factors. |
| 1,000 | 3 | 1,127 = 7²·23 | 1,129 | `-log 1127` | Discard mixed composites with repeated factors. |
| 10,000 | 6 | 10,245 = 3·5·683 | 10,247 | `+log 683` | Assume all composite coefficients are nonpositive. |
| 503,284,375 = 55⁵ | 55 | 577,533,495 = 3·5·7·11·500029 | 577,533,497 | `-2 log 500029` | Assume globally `b(n)>=-log n`, or discard nonrough terms as favorable. |

For the positive row, `m_6(15)=1-1-1=-1`. For the last row, the five pair
products at most 55 are `15,21,33,35,55`; the sixth is `77`, and every triple
product exceeds 55. Hence `m_55(1155)=1-4+5=2`. Since `500029>1155`, the strict
inequality `-2 log 500029 < -log(1155·500029)` follows exactly from monotonicity
of the logarithm. Its sign does not depend on floating-point evaluation.

These counterexamples reject pointwise premises. They do not disprove an
eventual or cofinal averaged bound such as (B*).

## 4. A proved bound for the proper-prime-power subrange of B

The following uniform exceptional-range estimate controls a subset of the
actual bilinear sum, including proper prime powers in the shifted position.
It is independent of `U,V>=1`.

First, for every positive integer `n`,

\[
 \tau(n)\le 729n^{1/4}.
 \tag{5}
\]

Here is an explicit proof of the constant. For every integer `a>=0`,
`a+1 <= 3·2^(a/4)`. The seven cases `a=0,...,6` reduce after raising to the
fourth power to `(a+1)^4 <= 81·2^a`. For `a>=3`, the implication from `a` to
`a+4` follows from `a+5 <= 2(a+1)`. These seven bases and steps cover all
nonnegative integers. Thus each prime below 16 contributes at most a factor
3 to `(a+1)/p^(a/4)`. There are exactly six such primes: `2,3,5,7,11,13`.
For any prime `p>=17`, `a+1 <= 2^a <= p^(a/4)`; the first inequality follows
by induction on `a`. Multiplying the prime-power factors of `tau(n)` gives
`3^6 n^(1/4)=729 n^(1/4)`, proving (5).

Since `0<=beta_V(r)<=log r`, absolute values yield

\[
 |b_{U,V}(n)|\le\tau(n)\log n\le729n^{1/4}\log n.
 \tag{6}
\]

Set `Y=2X+2` and `L=floor(log_2 Y)`. There are at most `sqrt(Y)L` proper prime
powers at most `Y`: their exponents lie between 2 and `L`, and each exponent
has at most `sqrt(Y)` possible bases, even if primality of the base is ignored.

For terms with **n a proper prime power**, use (1), the count just given, and
`Lambda(n+2)<=log Y`. The total absolute weighted contribution is at most
`sqrt(Y)L log²Y`.

For terms with **n+2 a proper prime power**, use (6) and the same count. Their
total absolute weighted contribution is at most `729Y^(3/4)L log²Y`.
Taking the union and allowing an upper-bound overcount at their intersection
gives

\[
 \boxed{
 \sum_{\substack{X<n\le2X\\
       n\text{ or }n+2\text{ a proper prime power}}}
 |b_{U,V}(n)|\Lambda(n+2)
 \le \bigl(\sqrt Y+729Y^{3/4}\bigr)L\log^2Y=o(X).
 }
 \tag{7}
\]

The last limit follows from `L<=log(Y)/log(2)` and
`log³(Y)/Y^(1/4) -> 0`, with `Y=2X+2`. All constants are explicit and independent
of the cutoffs. The specific absolute-mass bound (7), with exponent `3/4`,
remains a paper proof. The integer base inequalities and finite instances of
(5) are checked in the companion tests. Lean now proves the assembled
sublinear removal result using a different, weaker numerical bound, as follows.

The accompanying [BilinearSign.lean](../TwinPrime/Analytic/BilinearSign.lean)
does prove the prime coefficient vanishing, (2) with both divisor and
prime-divisor formulations of roughness, its `-log n` consequence for inputs
that are not prime powers, and `|b(n)| <= #n.divisors * log n`. It also proves
the exact prime-power formula
`b(p^a) = if U<p then -beta_V(p^a/p) else 0` for `a>=1`, and
`|b(p^a)|<=log(p^a)` for all `a>=0`. These statements are unconditional finite
lemmas.

The integrated [BilinearExceptional.lean](../TwinPrime/Analytic/BilinearExceptional.lean)
defines

\[
 B_{\rm prime}(U,V,X)=
 \sum_{\substack{X<n\le2X\\n\text{ not a prime power}\\n+2\text{ prime}}}
 b_{U,V}(n)\Lambda(n+2).
\]

Here “prime power” includes primes themselves. Its theorem
`abs_bilinearTerm_sub_primeSupport_le` proves, for every `U,V>=1`,

\[
 \boxed{
 |B_{U,V}(X)-B_{\rm prime}(U,V,X)|
 \le \frac{2}{\log2}Y^{1/2}\log^3Y+32Y^{5/6}\log^2Y.
 }
 \tag{8}
\]

The formal proof uses the proved divisor bound `tau(n)<=16 n^(1/3)` from
[DivisorGrowth.lean](../TwinPrime/Analytic/DivisorGrowth.lean), the prime-power
coefficient bound above, and the Chebyshev bound for the total von Mangoldt
weight of nonprime prime powers. `bilinearExceptionalBound_eq` supplies the
displayed expression. `tendsto_bilinearExceptionalBound_div` proves that its
ratio to `X` tends to zero, and
`tendsto_bilinearTerm_sub_primeSupport_div` proves the normalized difference
tends to zero for any two eventually positive cutoff functions.

The exported finite theorem (8) bounds the **absolute value of the difference
of the signed sums**. It is not stated as the sum of the absolute masses in
(7). The paper's explicit `729 n^(1/4)` divisor bound and the stronger
`Y^(3/4)` absolute-mass estimate remain distinct from the formal `Y^(5/6)`
removal estimate. The assembled `o(X)` removal itself is now formalized.

Consequently, up to either explicit `o(X)` error, `B` can be restricted to
**n composite but not a proper prime power, and n+2 prime**. Prime first members
contribute exactly zero, and shifted non-prime-powers have zero von Mangoldt
weight. This controls an exceptional subrange with an error smaller than any
fixed fraction of `CX` eventually. It makes no positive-fraction saving on the
remaining main contribution. Replacing `B` by this restricted sum preserves
lower-bound implications with fixed positive slack; it is not automatically
equivalent at the exact boundary `-CX/2`.

## 5. Research decision and verification

Preserve the grouped sign on rough integers and remove the exceptional range
using the formal estimate (8), or the stronger paper estimate (7). Reject an
argument that drops higher-factor composites, declares all
nonrough terms favorable, bounds every coefficient below by `-log n`, or
assumes the switched coefficient `m_U` is nonnegative or at most 1.

The first unsupported step remaining in a switching proof is a signed estimate
for expressions containing `m_U(a) log q Lambda(aq+2)`, together with the other
prime-power-divisor terms in (3), on the full cut-off factor range. Formula (4)
and its opposite-sign examples show why knowing the support alone is insufficient.
No fixed positive margin for that remaining weighted sum has been proved here.

Reproduce the exact checks from the repository root:

```powershell
python -m unittest discover -s compute -p test_sign_diagnostics.py -v
python compute/sign_diagnostics.py
lake env lean TwinPrime/Analytic/BilinearSign.lean
```

Five tests pass: 4,000 comparisons with the independent divisor-sieve coefficient,
prime/prime-power/rough formulas, exact switching multipliers, the explicit
divisor-bound bases and 10,000 instances, and the named prime-shift witnesses.
The sign checker compares integer products and never infers a sign from a
floating-point logarithm. No theorem at infinity is inferred from these tests.
