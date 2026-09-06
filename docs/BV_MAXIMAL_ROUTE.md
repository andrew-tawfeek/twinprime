# A finite route to the maximal Type II estimate

This note derives a maximal product-cutoff bilinear first moment and records
its implementation status. The dyadic covers, adaptive disjoint-interval
square bound, exact staircase identity, level geometry, and weighted
combination are now Lean-proved. `CharacterMaximalBilinear.lean` proves the
actual maximal first moment (MB), with no analytic hypothesis. The exact
Vaughan box assembly, Type I bounds and character counting, cutoff and
logarithmic comparisons, full primitive maximal mean, and centered
large-conductor tail now also check. The asymptotic assembly at `T=2X+2`
and both pointwise and maximal centered Siegel–Walfisz implications to BV
are proved. [Independent pointwise centered Siegel–Walfisz](CLASSICAL_DISTRIBUTION_THEOREM.md)
now supplies the distribution input. Endpoints may be selected separately for every character.
No variation or mean-value estimate is added as an assumption, and the
signed twin-correlation bound `(B*)` remains open.

## 1. The fixed-interval input already available

Write the weighted finite character sum as

```text
Σ_ω w_ω F(ω) := Σ_{1≤q≤Q} (q/φ(q)) Σ_{χ primitive mod q} F(q,χ).
```

Use `η_ω=χ⁻¹` throughout, matching `primitive_character_large_sieve` in
`RationalLargeSieve.lean`. All weights are nonnegative. Let

```text
C_Q = Q² H_(Σ_{1≤q≤Q} φ(q)).
```

The checked input says, for every fixed natural interval I and coefficients c,

```text
Σ_ω w_ω |Σ_{n∈I} c(n)η_ω(n)|² ≤ (|I|+C_Q) Σ_{n∈I}|c(n)|².       (LS)
```

One may instead use `C_Q=Q²(1+2log(Q+1))`. Both choices are independent of
I, c, and any endpoint later selected for a character. Modulus one remains
in the family. For Q=0 all weighted sums vanish.

## 2. The required disjoint-interval square bound

Fix a padded interval J=[N,N+K), K=2^j, and let
`E_b=Σ_{n∈J}|b(n)|²`. Its depth-d dyadic cells are

```text
D(d,k) = [N+k·2^(j−d), N+(k+1)·2^(j−d)),
0≤d≤j, 0≤k<2^d.
```

For each character ω, allow an arbitrary finite family of pairwise disjoint
intervals `J_(ω,l)⊆J`. Their endpoints and the family itself may depend on ω.
Empty intervals may be retained. The needed conclusion is

```text
Σ_ω w_ω Σ_l |Σ_{n∈J_(ω,l)} b(n)η_ω(n)|²
 ≤ V_j(K,C_Q) E_b,

V_j(K,C) = 2(j+1)[2K+(j+1)C] ≤ 4(j+1)²(K+C).                    (DI)
```

This follows from finite interval covers, as follows. Every subinterval of J
is a disjoint union of at most `2(j+1)` dyadic cells. Because the original
intervals are disjoint, no nonempty dyadic cell can occur in two covers.
Cauchy–Schwarz on each cover therefore gives, pointwise in ω,

```text
Σ_l |Σ_{n∈J_(ω,l)} z_ω(n)|²
 ≤ 2(j+1) Σ_{d=0}^j Σ_{k<2^d} |Σ_{n∈D(d,k)} z_ω(n)|².          (DC)
```

The right side contains every cell once, independently of ω. Applying (LS)
to these fixed cells and using that one depth partitions J yields

```text
Σ_ω w_ω Σ_{d,k} |Σ_{n∈D(d,k)} b(n)η_ω(n)|²
 ≤ Σ_{d=0}^j (2^(j−d)+C_Q) E_b
 ≤ [2K+(j+1)C_Q] E_b.
```

Combining the last two displays proves (DI). This is an actual derivation
from (LS), not an invocation of an additional analytic inequality. The
factor `2(j+1)` in (DC) and the geometric depth sum are the complete losses.
A bound for a single prefix, applied separately to every interval, would
lose the number of intervals and is insufficient for this argument.

The new `dyadicEnergy` in `DyadicMaximal.lean` is exactly the complete tree
sum in (DC), with the root at depth zero. The pointwise theorem
`sum_disjoint_intervals_sq_le_dyadicEnergy` now proves (DC), and
`sum_weighted_disjoint_intervals_sq_le` proves the adaptive weighted bound.
`primitive_character_disjoint_intervals_large_sieve` instantiates it with
the proved character large sieve, without assuming any maximal estimate.

For implementation, an even simpler sufficient bound avoids the geometric
depth sum. Induct directly on the existing recursive energy definition to
obtain

```text
Σ_ω w_ω dyadicEnergy (b·η_ω) N j ≤ (j+1)(K+C_Q) E_b.
```

At an induction step, apply (LS) to the root, apply the induction hypothesis
to each half, and add the two disjoint coefficient energies. Replacing each
half length by K proves the displayed bound. Combined with (DC), this gives
`2(j+1)²(K+C_Q)E_b` in place of V_j. Although the two budgets are not ordered
uniformly for all j, either one is sufficient for the safe constant 2 in
(MB). The recursive energy estimate avoids proving a separate explicit
depth expansion or geometric-series identity.

## 3. A concrete dyadic-cover specification

Cells can be represented by `(depth,index)` in the finite dependent type
`Σ d : Fin (j+1), Fin (2^d.val)`. A recursive cover avoids bit manipulation.
Work first on [0,2^j); translation by N is a separate lemma.

For a prefix [0,r), `0≤r≤2^j`, define its cover recursively:

1. If r=0, use the empty cover. If r=2^j, use the root cell.
2. Otherwise let h=2^(j−1). If r≤h, embed the cover of [0,r) in the left child.
3. If h<r, use the whole left child and embed the cover of [0,r−h) in the
   right child. The right prefix is proper because the full-prefix case was
   removed first.

A suffix [l,2^j) has the reflected recursion. In either cover there is at
most one cell at each depth. For a general interval [l,r):

1. If l=r, use the empty cover; if l=0 and r=2^j, use the root.
2. If r≤h, recurse in the left child; if h≤l, recurse in the right child.
3. Otherwise l<h<r. Use the suffix cover of [l,h) in the left child and the
   prefix cover of [0,r−h) in the right child.

This gives at most two cells at each global depth, including all endpoint
equalities. Prove these invariants together by induction on j:

- every selected cell is a valid node of the full tree and is nonempty;
- its natural interval is contained in [l,r);
- selected cell intervals are pairwise disjoint;
- their disjoint union is exactly [l,r);
- at every depth at most two cells are selected, hence total cardinality
  is at most `2*(j+1)`.

For a left embedding, local `(d,k)` becomes global `(d+1,k)`; for a right
embedding it becomes `(d+1,2^d+k)`. These embeddings are injective and have
disjoint ranges. The root `(0,0)` belongs to neither range.

For a family of disjoint target intervals, the containment and nonempty
invariants prove that a cell cannot be selected for two distinct family
members. Consequently a sum over `(family member,selected cell)` injects
into the full node set. This is the precise no-reuse fact needed in (DC).
Pairwise disjointness of the covers alone, considered one cover at a time,
does not establish it.

An alternative definition selects maximal dyadic cells contained in [l,r).
At a given depth their parents must cross one of the two interval boundaries,
so there are at most two. The recursive construction above makes the coverage
and endpoint cases more explicit for Lean.

## 4. Exact staircase decomposition of the product cutoff

Fix positive starts M,N and padded lengths H=2^i, K=2^j. Put
`I=[M,M+H)` and `J=[N,N+K)`. Coefficients may be zero on padding. For every
natural endpoint t, define the clamped half-open boundary

```text
f_t(m) = min(N+K, max(N, floor(t/m)+1)).
```

The floor is natural division. Since m>0, for n∈J,

```text
n < f_t(m)  iff  m*n ≤ t.
```

The function f_t is nonincreasing in m. Let

```text
B_ω(l,r) = Σ_{l≤n<r} b(n)η_ω(n),
A_ω(l,r) = Σ_{l≤m<r} a(m)η_ω(m).
```

For a dyadic parent P=[l,l+2h), denote its left child by `P_L=[l,l+h)`.
Attach to P the n-interval

```text
J_P(t) = [ f_t(l+2h−1), f_t(l+h−1) ).
```

Its endpoints are ordered by monotonicity. The following identity is exact:

```text
Σ_{m∈I,n∈J,mn≤t} a(m)b(n)η_ω(mn)
 = A_ω(M,M+H) B_ω(N,f_t(M+H−1))
   + Σ_{P internal node of the m tree} A_ω(P_L) B_ω(J_P(t)).    (ST)
```

To prove it, induct on the m-tree depth. On a parent P, the entire parent
has the common baseline `n<f_t(max P)`. The left child's larger baseline
adds exactly `P_L × J_P(t)`. The right child has the same baseline as P.
The induction hypotheses account for all corrections internal to the two
children. For a singleton m, the baseline is the whole product-cutoff row.
Finite distributivity and `η(mn)=η(m)η(n)` produce (ST).

At every fixed parent depth d, the left m-children are fixed disjoint
intervals, each of length `h_d=H/2^(d+1)`. Their attached n-intervals
`J_P(t)` are pairwise disjoint for each t: if P occurs before P', then
`max P < max(P'_L)`, hence `f_t(max P) ≥ f_t(max(P'_L))`. Thus the first
n-interval lies entirely above the second; equality gives an empty gap or
adjacent endpoints. Clamping preserves these inequalities.

No approximation to `mn≤t` has been made, and t=0 gives an empty region.
The identity does not require t to be comparable to the box dimensions.

## 5. Independent maximizing endpoints and the bilinear bound

Let `E_a=Σ_{m∈I}|a(m)|²`, and let every ω choose an arbitrary `t_ω≤T`.
Apply (ST), take absolute values, and sum with weights w_ω. For a fixed
parent depth d, weighted Cauchy–Schwarz on the combined indices `(ω,P)`
gives

```text
Σ_ω w_ω Σ_{P at depth d} |A_ω(P_L)| |B_ω(J_P(t_ω))|
 ≤ sqrt((h_d+C_Q) E_a · V_j(K,C_Q) E_b).                       (DEPTH)
```

For the first square factor, the m-children are fixed, so (LS) applies to
each and their disjointness bounds their total coefficient energy by E_a.
For the second factor, the n-intervals can depend on ω. Apply (DI) to their
disjoint family; do not treat those intervals as fixed when invoking (LS).
The root term is the same argument with one m-interval of length H and one
variable n-prefix.

There are i internal depths and one root term. Therefore

```text
Σ_ω w_ω |Σ_{m∈I,n∈J,mn≤t_ω} a(m)b(n)η_ω(mn)|
 ≤ sqrt(V_j(K,C_Q) E_a E_b)
     · [sqrt(H+C_Q)+Σ_{d<i} sqrt(H/2^(d+1)+C_Q)]
 ≤ 2(i+1)(j+1) sqrt((H+C_Q)(K+C_Q) E_a E_b).                   (MB)
```

Because the same right side works for every choice of t_ω, choose an actual
maximizer from the finite set `{0,...,T}` for each ω. This proves (MB) with
the maximum over t≤T inside the character sum. It never moves a maximum
through a sum as an unsupported equality.

For nonempty original intervals of lengths h,k, choose minimal powers of
two H≥h,K≥k and extend coefficients by zero. Then H≤2h and K≤2k, so the
right side is at most

```text
4(i+1)(j+1) sqrt((h+C_Q)(k+C_Q) E_a E_b),
i=ceil(log₂ h), j=ceil(log₂ k).
```

Empty intervals give zero directly. The loss for taking the product-cutoff
maximum is thus at most two logarithms of the side lengths. Symmetry allows
the roles of m and n to be exchanged, although this is unnecessary for a
fixed-logarithm BV estimate.

## 6. Consequence for the Vaughan Type II polynomial and losses

The derivation begins with Type II, then records the checked full primitive
mean and its centered large-conductor consequence. The uniform
small-conductor distribution estimate remains an input to the final BV route.

For `a(m)=μ(m)` and `b(n)=β_V(n)`, the existing finite coefficient bounds give
`|a(m)|≤1` and `0≤b(n)≤log n`. To apply the proved dyadic theorem without
silently treating an arbitrary cutoff as a power of two, use global cells
`[2^i,2^(i+1))`, for `0≤i<D=ceil(log₂(T+1))`. Use the coefficient masks

```text
a_T(m) = μ(m) if U<m≤T, and 0 otherwise;
b_T(n) = β_V(n) if V<n≤T, and 0 otherwise.
```

Assume U,V≥1. The D² boxes cover the full positive support exactly. A
contributing box with M=2^i, N=2^j satisfies MN≤T, U<2M, and V<2N.
Its energies satisfy `E_a≤M` and `E_b≤N log²T`. In particular M>U/2 and
N>V/2. Starting a doubling partition at arbitrary U,V would instead require
padding each side and a separate comparison; this global partition avoids it.

For general positive lower bounds U≤M and V≤N, the polynomial part of (MB),
before the dyadic and coefficient logarithms, has the bound

```text
sqrt(MN(M+C_Q)(N+C_Q))
 ≤ MN + sqrt(C_Q) sqrt(MN)(sqrt(M)+sqrt(N)) + C_Q sqrt(MN)
 ≤ T + sqrt(C_Q) T(1/sqrt(U)+1/sqrt(V)) + C_Q sqrt(T).          (POLY)
```

This inequality and its following logarithmic specialization are now proved
in `BilinearBoxPolynomial.lean`. Here M≤T/V and N≤T/U follow from MN≤T and
M≥U,N≥V. Set
`L_Q=1+2log(Q+1)≥1` and use `C_Q=Q²L_Q`. Then (POLY) is at most

```text
L_Q [T + Q T(1/sqrt(U)+1/sqrt(V)) + Q² sqrt(T)].
```

For the actual global cells, apply (POLY) with U/2,V/2 in place of U,V.
The middle term acquires a factor √2, which may safely be replaced by 2;
the other terms are unchanged. This affects only the absolute constant,
not the polynomial exponents or the logarithmic count. The support masks
and this active-box restriction must be retained in the finite assembly.

That finite assembly is now proved. `CharacterVaughan` supplies the exact
masked pair identity; the dyadic partition modules cover every positive
index exactly once; `VaughanActiveBoxes` removes only identically zero boxes.
`CharacterVaughanDyadic` bounds the actual full Type II maximum by the sum
of active box maxima. `CharacterVaughanMean` proves, for all positive U,V,

```text
Σ_{q≤Q} (q/φ(q)) Σ_{χ primitive} max_{0≤t≤T}|S_II(t,χ)|
 ≤ 2D⁴ log(T)L_Q [T + QT(1/√(U/2)+1/√(V/2)) + Q²√T].         (FII)
```

Here D=ceil(log₂(T+1)) exactly. A level factor `(i+1)(j+1)` is at most
D², and the active family has at most D² members. Those are the two
proved depth budgets. The theorem includes Q=0 and T=0,1 and has an
inverse-character version. No Type II mean-value estimate is assumed.

The losses of this deliberately simple construction are:

- at most two logarithms from (MB);
- at most two logarithms from the number of boxes;
- one logarithm from the square root of the β coefficient energy;
- one logarithm from the checked harmonic large sieve, via L_Q.

Thus (FII) supplies a Type II bound with a fixed sixth logarithmic power.
`BVLogComparisons.lean` now proves `D≤(2/log 2)log T` and `L_Q≤2log T`
for `T≥256` and `Q≤sqrt T`. At the paper level, choosing U,V comparable to
T^(1/3) gives the familiar polynomial `T + T^(5/6)Q + sqrt(T)Q²`, up to
absolute constants. That sharper choice is not the formal full-mean theorem
below. Integer cutoffs require an explicit comparison, for example
`floor(T^(1/3))≥T^(1/3)/2` for sufficiently large T. These are BV-internal
cutoffs; they need not equal the twin-correlation primary cutoff T^(1/5).
The latter would also give a power-saving middle term, with exponent 9/10.

The checked full mean follows the [Type I route](BV_TYPEI_ROUTE.md), using
the BV-internal cutoff `W=floor(T^(1/8))`. `BVInternalCutoffs.lean` proves
the needed floor and power comparisons for `T≥256`, including
`T^(1/8)/2≤W≤T^(1/8)` and `1/sqrt(W/2)≤2T^(-1/16)`.
`CharacterVaughanTypeI`, `CharacterTypeIBounds`, `PrimitiveCharacterCounting`,
and `CharacterTypeIMean` prove the exact Type I identities, primitive counts,
pointwise and maximal bounds, and their full weighted assembly. The low
von Mangoldt term and the modulus-one contribution are retained.

`VaughanMeanParameters.lean` absorbs the actual Type I and Type II budgets.
With `C₀=5+16(2/log 2)^4`, `VaughanMeanValue.lean` proves, for
`T≥256` and `1≤R≤sqrt T`,

```text
Σ_{1≤q≤R} (q/φ(q)) Σ_{χ primitive mod q} max_{0≤t≤T}|ψ(t,χ)|
 ≤ C₀ [T + T^(15/16)R + sqrt(T)R²] log⁶T.                    (FM)
```

The maximum ranges over every natural endpoint, including zero. This is
the uncentered character sum, including modulus one; an inverse-character
version is also proved. All six logarithmic losses, including the harmonic
large-sieve loss, are accounted for. No mean-value hypothesis occurs in (FM).

Let `P(T,r)` be the sum over primitive characters modulo r of the maximum
of `|ψ(t,χ)−1_(χ principal)t|` for `0≤t≤T`. The same module proves the
actual centered tail, for `T≥256` and `1≤R₀≤Q≤sqrt T`,

```text
Σ_{R₀<r≤Q} P(T,r)/φ(r)
 ≤ C₀ log⁶T [T/R₀ + T^(15/16)(1+log(Q/R₀)) + 2sqrt(T)Q].    (CT)
```

Conductor one is excluded from this tail; at primitive conductors greater
than one the centered and uncentered maxima agree. The proved conductor
reduction combines (CT) with the remaining centered small-conductor mass
and the explicit replacement error `Q(log Q+2sqrt(T)log T)`. Its versions
also handle `Q<R₀`, including `Q=0`, by truncating the small range and making
the tail zero. A supplied uniform centered bound E on conductors up to R₀
gives a small-conductor budget R₀E by checked character counting.

The asymptotic parameter and threshold choices are now checked at the exact
endpoint `T=2X+2`. `BVConductorGrowth.lean` proves, for every A>0 and
eventually uniformly in `1≤R₀≤Q` with
`log^(A+9)X≤R₀` and `Q≤sqrt(X)/log^(A+9)X`,

```text
Cφ(1+log Q) bvLargeConductorBudget (2X+2) R₀ Q
 ≤ Ktail X/log^A X,       Ktail=768CφC₀+1.
```

Here `Cφ=totientReciprocalConstant`. Its power-saving middle term is
controlled by the proved eventual comparison `log^(A+8)X≤X^(1/16)`.
`BVSmallConductorGrowth.lean` selects
`R₀=ceil((log X)^(A+9))`, proves its upper bound
`R₀≤log^(A+10)(2X+2)`, and absorbs the small-conductor budget supplied by
maximal centered Siegel–Walfisz with exponents `2A+12` and `A+10`.
If C is the latter estimate's constant, that contribution is at most
`12CφC X/log^A X`. The replacement error contributes at most
`X/log^A X` in the same modulus range.

`BombieriVinogradovFromSW.lean` combines these bounds into
`MaximalSiegelWalfisz.bombieriVinogradov`, with BV exponent `B=A+9` and
constant `K=12CφC+Ktail+1`. Its threshold is chosen before Q and all
character endpoints, and the existing zero-tail branch includes Q<R₀
and Q=0. `SiegelWalfiszMaximal.lean` proves uniform pointwise-to-maximal
conversion by treating short endpoints trivially and applying the pointwise
bound to the remaining endpoints with comparable logarithms. Hence
`PointwiseSiegelWalfisz.bombieriVinogradov` is also proved. The pointwise
conductor exponent is increased by one during maximalization.

The required independent pointwise centered Siegel–Walfisz theorem,
including conductor one, is now supplied by `pointwise_siegel_walfisz`.
Neither the completed BV argument nor
(FM) or (CT) estimates the shifted signed bilinear term `(B*)`.

## 7. Lean APIs and implementation order

The local API inspection found the following useful entries:

- `Finset.exists_mem_eq_sup'` selects a maximizing endpoint. Work first with
  arbitrary choices `t : characterIndex → ℕ`, then specialize to these choices.
- `Finset.sum_Ico_consecutive`, `Ico_union_Ico_eq_Ico`,
  `Ico_disjoint_Ico_consecutive`, `sum_union`, and `sum_biUnion` support the
  recursive covers and exact staircase sums.
- `Finset.sum_mul_sq_le_sq_mul_sq` supplies real Cauchy–Schwarz. Put
  `sqrt(w_ω)*|A|` and `sqrt(w_ω)*|B|` in its two factors; alternatively reuse
  the weighted finite inequality supplied by the rectangular-bilinear work.
- `Nat.le_div_iff_mul_le` converts `n≤t/m` to `n*m≤t` for m>0. Proving
  antitonicity of `t/m` directly from this equivalence avoids reliance on a
  guessed denominator-monotonicity lemma name.
- `Nat.le_pow_clog`, `Nat.clog_le_iff_le_pow`, `Nat.pow_pred_clog_lt_self`,
  and `Nat.clog_mono_right` handle power-of-two padding and logarithmic depth.
- The existing `dyadicEnergy` is the desired tree energy. Prove (DC) from
  the covers and its recursion, then sum (LS) by direct tree induction as
  above. An explicit finite-node/depth expansion gives the alternative V_j but
  is optional for the maximal bilinear conclusion.

A practical sequence is: recursive covers with all five invariants; the
no-reuse injection for a disjoint family; (DC); the weighted bound (DI);
the generic antitone-boundary staircase identity (ST); its per-depth
disjointness; arbitrary-endpoint (MB); finite maximum specialization; finally
Vaughan boxes and coefficient estimates. The staircase identity can be
proved for any antitone natural boundary f into [N,N+K], then specialized
to f_t, separating the combinatorics from natural division.

Current Lean status: the covers, no-reuse argument, (DC), adaptive weighted
(DI), both versions of (ST), per-level disjointness and exact grouping,
and (MB) are proved. `DyadicStaircaseFirstMoment.lean` handles arbitrary
antitone boundaries from fixed-interval second moments.
`CharacterMaximalBilinear.lean` discharges those inputs with the actual
primitive-character large sieve and proves both selected-cutoff and
finite-maximum versions, including inverse characters. Its only side
condition is M>0, and its loss is exactly `2(i+1)(j+1)`.
`BilinearBoxPolynomial.lean` proves (POLY) with positive lower side bounds.
The exact Vaughan character identity, masked global dyadic box assembly,
coefficient energy applications, and full finite Type II mean are also
proved in `CharacterVaughan`, `VaughanBoxCoefficients`,
`CharacterVaughanDyadic`, and `CharacterVaughanMean`. The Type I and counting
modules now complete the raw primitive mean. `BVInternalCutoffs`,
`BVLogComparisons`, and `VaughanMeanParameters` prove its numerical
comparisons; `VaughanMeanValue` proves (FM), (CT), and the resulting finite
progression bound with explicit small-conductor input. `BVConductorGrowth`
and `BVSmallConductorGrowth` complete the asymptotic absorption and cutoff
comparisons at `T=2X+2`. `SiegelWalfisz` states the independent centered
pointwise and maximal inputs; `SiegelWalfiszMaximal` proves their forward
implication, and `BombieriVinogradovFromSW` proves BV from either input.
The low von Mangoldt term and modulus one are retained. Independent
pointwise centered Siegel–Walfisz is now proved; the signed bound `(B*)` remains unproved.

The inspected Mathlib finite Fourier API has `ZMod.dft_apply`,
`ZMod.invDFT_apply`, and `ZMod.dft_dft`. Fourier-expanding an indicator of
the integer product mn gives phases `e(hmn/L)`, which do not split into a
function of m times a function of n. Hence that direct use of finite Fourier
inversion does not deliver the rectangular large-sieve argument. A Perron
or smoothed Fourier construction in log(mn) would need additional analytic
estimates. No suitable ready-made Perron or dyadic interval-variation theorem
was found in the inspected pinned APIs. The finite staircase route above
requires neither of those analytic constructions.
