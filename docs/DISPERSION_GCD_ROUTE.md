# Dispersion and the two large-gcd range removals

This note records proved finite identities and elementary estimates for the
signed bilinear term in [PLAN.md](../PLAN.md). The growing-family diagonal,
the large-gcd dispersion contribution, and the large-gcd original-factor
subsum are negligible. The remaining small-gcd correlation is unestimated.
These results do not complete M4 or prove the twin prime conjecture. See
[PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) for the current endpoint and
[SHIFTED_MOBIUS_INPUT_AUDIT.md](SHIFTED_MOBIUS_INPUT_AUDIT.md) for the limits of
the inspected shifted-Möbius theorems.

The subsequent refinements in Sections 7–8 use only the nonzero product band,
improve the two logarithmic errors, and remove large prime square factors.
The final simultaneous removal changes the actual bilinear sum by
O(X/log^7 X); its remaining signed sum is not estimated.

## 1. Exact right-closed partition

For natural cutoffs \(U,V\ge1\), write

\[
B_{U,V}(X)=\sum_{\substack{d>U,\ r>V\\X<dr\le2X}}
 \mu(d)\beta_V(r)\Lambda(dr+2),\qquad
\beta_V(r)=\sum_{\substack{b\mid r\\b>V}}\Lambda(b).
\]

Put \(D_X=\operatorname{dyadicNatDepth}(2X)\), and select the pairs

\[
\mathcal I_{U,V,X}=\{(i,j):0\le i,j<D_X,\quad
 U\le2\cdot2^i,\quad V\le2\cdot2^j,\quad 2^i2^j\le2X\}.
\]

Their cells are \((M,2M]\times(N,2N]\), with \(M=2^i,N=2^j\).
Every relevant factor \(n>1\) has exactly one index: apply the left-closed
dyadic partition to \(n-1\). Thus powers of two belong to the upper endpoint
of the preceding cell. Every actual pair has exactly one selected cell,
although the selected family may contain empty boxes, and

\[
B_{U,V}(X)=\sum_{(i,j)\in\mathcal I_{U,V,X}}B_{M,N},\qquad
|\mathcal I_{U,V,X}|\le D_X^2.
\]

The cutoffs and product interval remain inside each box. In particular, set

\[
I_M=(M,2M]\cap(U,\infty),\quad J_N=(N,2N]\cap(V,\infty),
\quad a_X(d,r)=1_{X<dr\le2X}\mu(d)\Lambda(dr+2).
\]

Then \(B_{M,N}=\sum_{r\in J_N}\beta_V(r)\sum_{d\in I_M}a_X(d,r)\).
All indices in these real-looking intervals are natural numbers.

## 2. The complete diagonal is negligible

Define

\[
T_N=\sum_{r\in J_N}\beta_V(r),\quad
\Delta_{M,N}=\sum_{r\in J_N}\beta_V(r)\sum_{d\in I_M}a_X(d,r)^2,
\]
\[
O_{M,N}=\sum_{r\in J_N}\beta_V(r)
 \sum_{\substack{d,e\in I_M\\d\ne e}}a_X(d,r)a_X(e,r).
\]

Both orientations of each distinct pair occur in \(O_{M,N}\). Weighted
Cauchy–Schwarz gives \(B_{M,N}^2\le T_N(\Delta_{M,N}+O_{M,N})\).
With \(L=\log(4X+4)\), the elementary bounds

\[
0\le\beta_V(r)\le\log r,\quad |a_X(d,r)|\le\log(2X+2),
\quad T_N\le N\log(2N)
\]

imply, on selected boxes and for \(X\ge1\),

\[
\frac{T_N\Delta_{M,N}}{X^2}\le\frac{8L^4}{U}.
\]

For \(X\ge128\), put \(a=2/\log2\); then \(D_X\le aL\). Consequently

\[
\frac1X\sum_{\mathcal I_{U,V,X}}\sqrt{T_N\Delta_{M,N}}
 \le D_X^2\sqrt{8L^4/U}\le\sqrt8\,a^2L^4/\sqrt U.
\]

For \(U=V=\lfloor X^{1/5}\rfloor\), we have \(U\sim X^{1/5}\), so this
tends to zero after multiplication by any fixed power \(L^k\),
\(k\in\mathbb N\). The Lean result controls the entire growing family,
not merely one box fixed in advance.

## 3. Elementary gcd counting

For \(A,B\in\mathbb N\) and \(G\ge1\), cover positive pairs with
\(\gcd(u,v)>G\) by the sets of pairs divisible by \(g\), for \(G<g\le A\).
Taking \(g=\gcd(u,v)\) proves coverage; overlaps only enlarge the bound:

\[
\#\{1\le u\le A,\ 1\le v\le B:\gcd(u,v)>G\}
 \le\sum_{G<g\le A}\lfloor A/g\rfloor\lfloor B/g\rfloor
 \le AB\sum_{g>G}g^{-2}\le AB/G.
\]

The implementation uses a finite inverse-square tail and also handles empty
intervals. This count includes equal pairs. That is safe for an upper bound
on a distinct-pair set and necessary for the unrestricted original factors.

## 4. Dispersion pairs: \(\gcd(d,e)>G\)

Split \(O_{M,N}=O^{\mathrm{disp}}_{\le G}+O^{\mathrm{disp}}_{>G}\) by the
gcd of the two **left factors** \(d,e\), retaining \(d\ne e\) in both pieces.
The entries still impose both product conditions \(X<dr\le2X\) and
\(X<er\le2X\). Counting in \((0,2M]^2\) gives at most \(4M^2/G\) pairs, so

\[
|O^{\mathrm{disp}}_{>G}|\le(4M^2/G)L^2T_N,\qquad
T_N|O^{\mathrm{disp}}_{>G}|\le16X^2L^4/G.
\]

Here the constant \(16\) uses \(M^2N^2\le4X^2\). Choose the natural ceiling

\[
G(X)=\lceil L^{10}\rceil,\qquad L^{10}\le G(X)\le2L^{10}.
\]

For \(X\ge128\), the actual full-family square-root budget satisfies

\[
\mathcal E(X):=\sum_{\mathcal I_{U,V,X}}
 \sqrt{T_N|O^{\mathrm{disp}}_{>G(X)}|},\qquad
\frac{\mathcal E(X)}X\le D_X^2\sqrt{16L^4/G(X)}
 \le\frac{4a^2}{L}.
\]

Thus \(\mathcal E(X)=O(X/L)=o(X)\). This fixed tenth-power cutoff does not
give arbitrary extra logarithmic losses for this budget.

The remaining quantity, with the primary cutoffs, is exactly

\[
\mathcal S(X)=\sum_{\mathcal I_{U,V,X}}
 \sqrt{\max\{T_N O^{\mathrm{disp}}_{\le G(X)},0\}}.
\]

Writing \(\mathcal D(X)=\sum\sqrt{T_N\Delta_{M,N}}\), the finite proof gives

\[
|B_{U,V}(X)|\le\mathcal D(X)+\mathcal E(X)+\mathcal S(X),\qquad
B_{U,V}(X)\ge-\mathcal D(X)-\mathcal E(X)-\mathcal S(X).
\]

No estimate for \(\mathcal S\) is proved. Its summands take the positive part
**inside each box before the square root**; a bound only for the signed sum
of off-diagonals across boxes would not control it. Proving
\(\mathcal S(X)=o(X)\) would give absolute bilinear cancellation, a stronger
sufficient target than B*: for every \(Y\), some \(X\ge Y\) satisfies
\(B_{U,V}(X)\ge-CX/2\), with \(C=2\,\mathrm{twinPrimeConstant}>0\).

## 5. Original factors: \(\gcd(d,r)>G\)

Independently split the original signed pair sum as

\[
B_{U,V}(X)=B^{\mathrm{fac}}_{\le G}(X)+B^{\mathrm{fac}}_{>G}(X),
\]

using \(\gcd(d,r)\le G\) and \(\gcd(d,r)>G\). Here \(d=r\) remains allowed.
This is a restriction of the actual bilinear sum, not of its dispersion
second moment. The rectangle count is now \(4MN/G\), giving

\[
|B^{\mathrm{fac}}_{M,N,>G}|\le
 (4MN/G)\log(2N)\log(2X+2)\le8XL^2/G.
\]

The exact restricted partition and its cardinality yield, for \(U,V\ge1\)
and \(X\ge128\),

\[
\frac{|B^{\mathrm{fac}}_{>G(X)}(X)|}{X}
 \le D_X^2\frac{8L^2}{G(X)}\le\frac{8a^2}{L^6}.
\]

Hence the removed actual subrange is \(O(X/\log^6 X)\), and with the primary
cutoffs the checked exact difference satisfies

\[
\frac{B_{U,V}(X)-B^{\mathrm{fac}}_{\le G(X)}(X)}X\longrightarrow0.
\]

The two removals involve different gcds and different residuals.
\(B^{\mathrm{fac}}_{\le G(X)}\) is a signed original-factor sum;
\(\mathcal S\) is a nonnegative dispersion budget involving ordered distinct
left-factor pairs. Neither remaining quantity is estimated here.

## 6. Lean source map

The following eight modules contain the finite proofs and limit results.
The underlying entry definitions and weighted Cauchy–Schwarz identity are in
[Dispersion.lean](../TwinPrime/Analytic/Dispersion.lean).

| Module | Principal declarations and scope |
|---|---|
| [DispersionPartition.lean](../TwinPrime/Analytic/DispersionPartition.lean) | `bilinearTerm_eq_sum_dispersionBoxes`, `dispersionBoxIndices_card_le`: exact right-closed partition and depth-squared count. |
| [DispersionAggregate.lean](../TwinPrime/Analytic/DispersionAggregate.lean) | `tendsto_primary_dispersion_diagonal_sum`: uniform growing-family diagonal limit with any fixed logarithmic loss. |
| [DispersionGlobal.lean](../TwinPrime/Analytic/DispersionGlobal.lean) | `abs_bilinearTerm_le_dispersion_sums`, `tendsto_primaryDispersionDiagonal_div_log_pow`: actual global budget and diagonal limit. `tendsto_primary_bilinear_div_of_offDiagonal` retains an explicit unproved off-diagonal premise. |
| [DispersionLargeGcd.lean](../TwinPrime/Analytic/DispersionLargeGcd.lean) | `card_largeGcd_rectangle_le`, `dispersionOffDiagonal_eq_small_add_large`, `dispersion_mass_mul_abs_largeGcd_le`: ordered distinct dispersion pairs and the constant-16 estimate. |
| [DispersionGcdCutoff.lean](../TwinPrime/Analytic/DispersionGcdCutoff.lean) | `dispersionGcdCutoff`, `dispersionGcdCutoff_family_error_le`: ceiling control and the explicit reciprocal-log bound. |
| [DispersionGcdGlobal.lean](../TwinPrime/Analytic/DispersionGcdGlobal.lean) | `tendsto_primaryDispersionLargeGcd_div`, `neg_primary_gcd_dispersion_le_bilinearTerm`: actual large-gcd budget is sublinear; `primaryDispersionSmallGcd` remains in the signed lower bound. |
| [DispersionBilinearGcd.lean](../TwinPrime/Analytic/DispersionBilinearGcd.lean) | `bilinearBox_filtered_eq_filtered_pair_sum`, `abs_bilinearBoxLargeGcd_le`: exact original-factor restrictions and the constant-8 box bound. |
| [BilinearGcdReduction.lean](../TwinPrime/Analytic/BilinearGcdReduction.lean) | `bilinearTerm_eq_smallGcd_add_largeGcd`, `abs_bilinearLargeGcd_div_le_log`, `tendsto_primary_bilinear_sub_smallGcd_div`: exact global split, sixth-power logarithmic saving, and normalized actual difference. |

All estimates above use finite counting, the elementary coefficient bounds,
and numerical growth; no prime-distribution or multiplicative-cancellation
hypothesis is used to remove either large-gcd range. The remaining analytic
obligation is still substantive, as recorded in the linked proof ledger.

## 7. Only three product levels can contribute

The inequalities d>M, r>N and X<dr≤2X imply MN<2X. The upper cell
endpoints d≤2M, r≤2N also imply X<4MN. Thus a nonzero box must satisfy

```text
X < 4 * 2^(i+j),     2^(i+j) < 2X.
```

Any two allowed exponents i+j differ by at most two. Mapping (i,j) to
(i,i+j) injects the active family into a depth-by-three rectangle. Hence
its cardinality is at most 3D_X. Outside this band every actual entry is
zero, so B and all four diagonal/off-diagonal root budgets reindex exactly.
This includes the signed small-gcd budget; it is not a support assumption.
[DispersionActiveBand.lean](../TwinPrime/Analytic/DispersionActiveBand.lean)
proves the count and these identities.

Put a=2/log 2 and retain L=log(4X+4), G=ceil(L^10). For X≥128, applying
the earlier per-box bounds to 3D_X≤3aL gives the stronger estimates

```text
diagonal_sum / X ≤ 3D_X * sqrt(8L^4/U),
large_gcd_dispersion_root_sum / X ≤ 12a/L^2,
abs(original_factor_large_gcd_sum) / X ≤ 24a/L^7.
```

These bounds concern the original full sums, identified by the exact
zero-box transport. The first is O(L^3/sqrt U). The preceding Section 4–5
bounds remain valid but are weaker. The numerical inequalities and actual
applications are proved in
[DispersionActiveBudget.lean](../TwinPrime/Analytic/DispersionActiveBudget.lean),
including `primaryDispersionLargeGcd_div_le_log_sq` and
`abs_primaryBilinearLargeGcd_div_le_log_seven`.

## 8. Large prime squares and the simultaneous residual

Let an input be bad at H if p² divides it for some prime p>H. If μ(d)≠0,
d is squarefree. Therefore a prime square dividing dr either lies wholly
in r, or p divides both d and r. The two allocations are covered by

```text
(a,b) ↦ (a,p²b),     (a,b) ↦ (pa,pb),     ab≤2X/p².
```

The number of positive pairs ab≤T is at most T(1+log T). Summing the
two images over p>H, enlarging to all integer p, and using the inverse-square
tail gives at most 2T(1+log T)/H pairs. Every original summand has absolute
value at most L². At T=2X and X,H≥1 this proves

```text
Σ_{d>U,r>V,X<dr≤2X, ∃prime p>H:p²|dr}
  abs(μ(d)β_V(r)Λ(dr+2)) ≤ 8X L³/H.
```

This is factorwise absolute mass, uniformly in U,V. It includes cases with
p² entirely in r and gcd(d,r)=1, so it removes a range not covered by the
original-factor gcd condition. At H=G(X), the normalized mass is at most
8/L^7. [DispersionSquareFactor.lean](../TwinPrime/Analytic/DispersionSquareFactor.lean)
proves the count, mass estimate, exact complementary split, and o(X) removal
for arbitrary cutoff functions.

Finally retain exactly the original pairs satisfying both

```text
gcd(d,r) ≤ G(X),
for every prime p>G(X), p² does not divide dr.
```

Call their signed sum B_core, with the primary cutoffs and unchanged
coefficient μ(d)β_V(r)Λ(dr+2). The exact decomposition removes the large-gcd
sum first, then the bad-square part within the small-gcd range. The latter
is bounded by the full factorwise absolute mass above. No inference from
a small signed sum to a small restricted sum is used. For X≥128,

```text
abs(B−B_core)/X ≤ (24a+8)/L^7,       (B−B_core)/X → 0.
```

These are `abs_primary_bilinear_sub_structuredCore_div_le` and
`tendsto_primary_bilinear_sub_structuredCore_div` in
[BilinearStructuredCore.lean](../TwinPrime/Analytic/BilinearStructuredCore.lean).
Its `structuredCore_condition_of_squarefree` proves that every squarefree
input survives both restrictions. In particular, rough squarefree composites
with negative grouped coefficient survive. This is a proved removal of
exceptional ranges, not cancellation of B_core or a proof of B*.

The [centering review](DISPERSION_CENTERING_REVIEW.md) gives a separate paper
calculation for a deterministic center and a positive small-gcd off-diagonal
witness. Its centered variance is still unestimated.
