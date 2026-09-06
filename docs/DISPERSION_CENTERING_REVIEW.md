# Dispersion centering: finite obstruction and a deterministic removal

The positive-part square-root budget is stronger than the signed estimate
(B*). This audit finds a concrete obstruction to discarding its off-diagonal,
but no proof that the full budget cannot be sublinear. It also gives a complete
paper bound for one deterministic center. That center removal is not an
improvement of (B*) by itself: the remaining centered correlation is unproved.

## 1. Verified inputs and the scope of this note

The exact entries, signed boxes and second-moment identity are in
[Dispersion.lean](../TwinPrime/Analytic/Dispersion.lean). The global square-root
budget is in [DispersionGlobal.lean](../TwinPrime/Analytic/DispersionGlobal.lean).
The two different gcd restrictions are distinguished in
[DISPERSION_GCD_ROUTE.md](DISPERSION_GCD_ROUTE.md): original factors use
`gcd(d,r)`, while dispersion off-diagonal pairs use `gcd(d,e)`.

[DispersionActiveBand.lean](../TwinPrime/Analytic/DispersionActiveBand.lean)
has passed standalone Lean checking. It proves that every nonzero box satisfies

\[
 X<4MN,\qquad MN<2X,
\]

and that the restricted dyadic family has at most
\(3D_X\) members, where \(D_X=\operatorname{dyadicNatDepth}(2X)\).
It also proves exact reindexing for the actual bilinear sum and the diagonal,
off-diagonal, large-gcd and small-gcd square-root budgets. No cancellation
estimate is part of those support results.

The ordinary estimate `mertens_log_six` is already an unconditional theorem in
[ClassicalDistribution.lean](../TwinPrime/Analytic/ClassicalDistribution.lean).
Its precise meaning, from
[MertensReduction.lean](../TwinPrime/Analytic/MertensReduction.lean), is that
there are \(K\ge0\) and a natural \(T_0\) such that

\[
 |\mathcal M(t)|\le Kt/(\log t)^6\quad(t\ge T_0),
 \qquad \mathcal M(t)=\sum_{1\le n\le t}\mu(n).
 \tag{1}
\]

The witness, local-factor formulas and assembled center estimate below are
paper calculations, not additional Lean theorems in the repository.

## 2. A positive off-diagonal entirely at gcd one

Take \(X=14\), \(U=V=1\), \(M=4\), \(N=2\). These are the primary cutoffs:
\(1^5\le14<2^5\). The exact left and right sets are
\(\{5,6,7,8\}\) and \(\{3,4\}\). The only nonzero entries are

\[
 a_{14}(5,3)=-\log17,\qquad a_{14}(7,3)=-\log23.
\]

Indeed their products are 15 and 21, both in \((14,28]\). The other relevant
shifted products are 20, 22, 26 and 30, none a prime power; the last endpoint
\(8\cdot4=32\) is outside the product interval, and \(\mu(8)=0\) anyway.
Since \(\beta_1(3)=\log3\) and \(\beta_1(4)=\log4\), the exact values are

\[
 B_{4,2}=-\log3(\log17+\log23),
\]
\[
 \Delta_{4,2}=\log3\big((\log17)^2+(\log23)^2\big),
 \qquad O_{4,2}=2\log3\log17\log23>0.
 \tag{2}
\]

Both orientations \((5,7),(7,5)\) occur, and \(\gcd(5,7)=1\). Thus every
dispersion cutoff \(G\ge1\) leaves (2) wholly in the small-gcd off-diagonal.
This refutes a universal assertion that this off-diagonal is nonpositive or
may be dropped. It does not refute an asymptotic saving as \(X\to\infty\).

## 3. The prime-pair local factors retain the determinant

For distinct positive \(d,e\), let

\[
 \nu_p(d,e)=\#\{r\bmod p:(dr+2)(er+2)\equiv0\pmod p\}.
\]

The conventional prime-pair heuristic uses
\(\mathfrak S(d,e)=\prod_p(1-\nu_p(d,e)/p)/(1-1/p)^2\).
This is a heuristic input here; the
[standard local-density formulation](https://terrytao.wordpress.com/2013/06/03/the-prime-tuples-conjecture-sieve-theory-and-the-work-of-goldston-pintz-yildirim-motohashi-pintz-and-zhang/)
does not supply the growing-parameter uniformity needed below.

For odd \(p\), the root counts are exact:

| Condition | \(\nu_p(d,e)\) |
| --- | ---: |
| \(p\mid d\) and \(p\mid e\) | 0 |
| \(p\) divides exactly one of \(d,e\) | 1 |
| \(p\nmid de\) and \(p\mid d-e\) | 1 |
| \(p\nmid de(d-e)\) | 2 |

At 2, either even coefficient makes one form identically even, so
\(\nu_2=2\) and the prime-pair main term vanishes. If both coefficients are
odd, \(\nu_2=1\). Exceptional powers of 2 in the actual von Mangoldt sums
remain; a zero singular series is not an exact zero identity for those sums.

For odd \(d,e\), writing
\(C_2=\prod_{p>2}(1-1/(p-1)^2)\), the root table gives

\[
 \mathfrak S(d,e)=2C_2
 \prod_{\substack{p>2\\p\mid\gcd(d,e)}}\frac p{p-2}
 \prod_{\substack{p>2\\p\mid de(d-e)\\p\nmid\gcd(d,e)}}
       \frac{p-1}{p-2}.
 \tag{3}
\]

In particular, small \(\gcd(d,e)\) does not remove the factors from
\(d-e\). The determinant of the two forms is \(2(d-e)\), up to sign.
Their contribution to the off-diagonal still has the sign \(\mu(d)\mu(e)\).
Replacing these signs by absolute values discards the cancellation being sought.

## 4. The beta weight cannot be replaced by an independent average

For fixed \(d,e\) in the left box, their common real interval for \(r\) is
\((\alpha,\omega]\), where

\[
 \alpha=\max(N,V,X/d,X/e),\qquad
 \omega=\min(2N,2X/d,2X/e).
\]

An empty interval contributes zero. Otherwise the exact divisor expansion
`vaughanBeta_apply` in [Vaughan.lean](../TwinPrime/Analytic/Vaughan.lean) gives

\[
 \sum_{\alpha<r\le\omega}\beta_V(r)\Lambda(dr+2)\Lambda(er+2)
 =\sum_{V<b\le\lfloor\omega\rfloor}\Lambda(b)
   \sum_{\lfloor\alpha/b\rfloor<t\le\lfloor\omega/b\rfloor}
     \Lambda(db t+2)\Lambda(eb t+2).
 \tag{4}
\]

All indices are positive integers. Thus the formal main term is built from
\(\Lambda(b)\mathfrak S(db,eb)(\omega-\alpha)/b\), not from
\(\mathfrak S(d,e)\) times an independent beta average. Its determinant is
\(2b(d-e)\), and primes dividing \(b\) divide both leading coefficients.
For large \(b\), the inner interval in (4) can contain zero or one integer.
Its exact cardinality is the difference of the displayed floors. A
fixed-coefficient prime-pair asymptotic cannot be summed over all these growing
\(d,e,b\) without a new uniform, weighted error estimate. Equations (3)–(4)
identify that gap; they do not close it.

## 5. An exact candidate center and its uniform paper bound

For the rest of this section set \(U=V=\operatorname{primaryCutoff}(X)\).
For \(r\in J_N=(N,2N]\cap(U,\infty)\), define

\[
 a_r=\max(M,U,\lfloor X/r\rfloor),\qquad
 b_r=\min(2M,\lfloor2X/r\rfloor),
\]
\[
 H_r=\sum_{a_r<d\le b_r}\mu(d),\qquad
 A_r=\sum_{a_r<d\le b_r}\mu(d)\Lambda(dr+2),\qquad
 c(r)=\mathbf1_{r\text{ odd}}\frac r{\varphi(r)}.
\]

Empty intervals have both sums zero. This (c(r)) is the ordinary
progression density for \(rd+2\) as \(d\) varies when \(r\) is odd; it is
zero in the non-reduced even progression. No distribution assertion is needed
to define
\(A_r^{\mathrm{cen}}=A_r-c(r)H_r\). Exactly,

\[
 B_{M,N}=B_{M,N}^{\mathrm{cen}}+C_{M,N},\quad
 B_{M,N}^{\mathrm{cen}}=\sum_{r\in J_N}\beta_U(r)A_r^{\mathrm{cen}},\quad
 C_{M,N}=\sum_{r\in J_N}\beta_U(r)c(r)H_r.
 \tag{5}
\]

The following details make the estimate for the total center uniform.

**Totient factor.** Write \(C_\varphi=\texttt{totientReciprocalConstant}\).
For every positive \(r\),

\[
 \frac r{\varphi(r)}
 =\sum_{d\mid r}\frac{\varphi(d)}{\varphi(r)}
 \le\sum_{d\mid r}\frac1{\varphi(r/d)}
 \le\sum_{1\le k\le r}\frac1{\varphi(k)}
 \le C_\varphi(1+\log r).
 \tag{6}
\]

The first two steps use `Nat.sum_totient` and
`Nat.totient_super_multiplicative` in
[pinned Mathlib Totient.lean](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Data/Nat/Totient.lean),
with \(r=d(r/d)\); the divisor involution justifies the next reindexing.
The last step is the proved `sum_reciprocalTotient_le_log` in
[TotientReciprocal.lean](../TwinPrime/Analytic/TotientReciprocal.lean).
The pointwise corollary (6) is a paper deduction here, not a cited existing
project theorem.

**Both Mertens endpoints are large.** Increase \(T_0\) in (1) to at least 2
and take \(X\ge\max(128,T_0^5)\). Then \(U\ge T_0\). If the interval is
nonempty, \(U\le a_r\le b_r\le2M\); consequently

\[
 |H_r|\le |\mathcal M(b_r)|+|\mathcal M(a_r)|
 \le\frac{4KM}{(\log U)^6}.
 \tag{7}
\]

The empty case satisfies the same inequality. This handles the moving lower
endpoint and a box truncated by \(d>U\); applying (1) only at \(2M\) would
not suffice. The exact finite summatory difference is already available as
`moebiusSummatory_sub` in
[MoebiusHyperbola.lean](../TwinPrime/Analytic/MoebiusHyperbola.lean).

**Uniform logarithms.** Put \(\ell=\log X\). The proved
`primaryCutoff_inverse_bound` in
[CutoffLogarithms.lean](../TwinPrime/Analytic/CutoffLogarithms.lean) gives
\(X<(U+1)^5\le(2U)^5\). Since \(U\ge2\),
\(\ell\le10\log U\). Thus (7) is at most
\(4\cdot10^6KM/\ell^6\). On an active box, \(M\ge1\) and \(MN<2X\),
so \(2N<4X\). For \(X\ge128\),

\[
 \log(2N)\le2\ell,\qquad 1+\log r\le3\ell\quad(r\in J_N).
\]

Using \(\beta_U(r)\le\log r\), \(|J_N|\le N\), (6) and (7), we obtain

\[
 |C_{M,N}|\le
 \frac{24\cdot10^6KC_\varphi MN}{\ell^4}
 \le\frac{48\cdot10^6KC_\varphi X}{\ell^4}.
 \tag{8}
\]

**Sum over the whole family.** The proved depth estimate
`dyadicNatDepth_le_two_div_log_two_mul_log` in
[BVLogComparisons.lean](../TwinPrime/Analytic/BVLogComparisons.lean) yields
\(D_X\le(2/\log2)\log(2X)\le(4/\log2)\ell\).
The active-band cardinality is at most \(3D_X\), and every inactive center
is zero because its product interval is empty. Therefore

\[
 \boxed{\displaystyle
 \sum_{(M,N)\text{ active}}|C_{M,N}|
 \le\frac{576\cdot10^6KC_\varphi}{\log2}
       \frac X{(\log X)^3}.}
 \tag{9}
\]

All thresholds depend only on the single ordinary Mertens bound, not on the
box or on \(r\). Equations (5)–(9) are the proposed deterministic center
assembly. Their constituent Lean inputs are proved, but this assembled theorem
has not been formalized in a new module.

## 6. What remains after centering

Equation (9) would permit replacing the original signed bilinear sum by the
sum of the centered boxes up to \(O(X/\log^3X)\). It does not bound the
centered boxes themselves or prove any improvement to the signed budget (B*).
In particular, controlling

\[
 \sum_{(M,N)\text{ active}}
 \sqrt{T_N\sum_{r\in J_N}\beta_U(r)(A_r-c(r)H_r)^2}
\]

requires a further correlation estimate. The prime-pair local factors and
the beta dependence in (3)–(4) remain in that variance.

The same uniform row bound used in (8) also gives
\[
 \sum_{(M,N)\text{ active}}
 \sqrt{T_N\sum_{r\in J_N}\beta_U(r)(c(r)H_r)^2}
 \le\frac{576\cdot10^6KC_\varphi}{\log2}\frac X{(\log X)^3}.
\]
Here each square root is bounded by
\(T_N\sup_{r\in J_N}|c(r)H_r|\); this is not an inference from the
absolute value of the signed center. Weighted finite Euclidean norm inequalities
then bound the difference between the raw and centered square-root
second-moment budgets by the displayed quantity. Moreover, the exact
second-moment decomposition gives, box by box,
\[
 \sqrt{\max(T_NO_{M,N},0)}
 \le\sqrt{T_N(\Delta_{M,N}+O_{M,N})}
 \le\sqrt{T_N\Delta_{M,N}}+\sqrt{\max(T_NO_{M,N},0)}.
\]
Since the full diagonal square-root sum is already proved to be \(o(X)\),
this paper calculation makes the original positive-part budget and the
centered variance budget equivalent at the level of an \(o(X)\) target.
It does not turn the stronger second-moment target into a weaker signed one.

A local-density model
has a full second-moment kernel which is an average of squares; its
off-diagonal is that kernel minus the diagonal, not a sum that can be discarded
termwise. Neither this observation nor the small-gcd restriction supplies
the missing signed cancellation. The positivity witness (2) and deterministic
bound (9) delimit useful finite work without asserting that the twin-prime
obligation has been discharged.
