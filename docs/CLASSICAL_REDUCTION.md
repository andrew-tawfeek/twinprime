# Classical inputs and their proved reduction

The earlier conditional endpoint is
`TwinPrime.twinPrimeConjecture_of_bv_mertens_and_bilinear`. It requires exactly:

1. `MaximalBombieriVinogradov`, the explicit maximal progression estimate.
2. `MertensLogSix`, meaning there is a constant K≥0 such that, eventually,
   `|Σ_{n≤t} μ(n)| ≤ Kt/log⁶t`.
3. PLAN's cofinal signed bound (B*), at U=V=floor(X^(1/5)).

The refined `TwinPrime.twinPrimeConjecture_of_bv_and_bilinear` now derives
the second input from the first. The [independent classical chain](CLASSICAL_DISTRIBUTION_THEOREM.md)
now supplies BV as well, while B* remains open. This document explains the checked classical bridges;
it is not an unconditional proof of twin primes.

## 1. Ordered ordinary Möbius sums

Write

```text
M(N) = Σ_{0<n≤N} μ(n),
S(N) = Σ_{0<n≤N} μ(n)/n,
T(x) = Σ_{0<n≤floor(x)} μ(n) log(x/n)/n.
```

All limits of S and the logarithmic moment use ordered finite sums. No
`Summable (μ(n)/n)` assumption is made; that would assert unconditional
convergence, which is not the intended notion.

[MoebiusHyperbola.lean](../TwinPrime/Analytic/MoebiusHyperbola.lean) uses the
exact convolution μ*1=ε to prove, for positive integers K,N,

```text
1 = Σ_{d≤N} μ(d) floor(KN/d) + Σ_{m≤K} M(floor(KN/m)) − K M(N).
```

Replacing the first floor by KN/d costs at most N, because |μ|≤1. If
`|M(t)|≤ηt` throughout N≤t≤KN, the checked estimate is

```text
|S(N)| ≤ 2/K + η(K+1).
```

Choose K first and then η. This proves M(N)/N→0 implies S(N)→0, without
assuming S converges and without importing a boundary constant from ζ.

[MoebiusAbel.lean](../TwinPrime/Analytic/MoebiusAbel.lean) proves the exact
discrete reciprocal-weight Abel formula. A logarithmic telescoping kernel
then gives, under the quantitative Mertens input,

```text
|S(b) − S(a)| ≤ (32 + 2/log 2) K / log⁵a     (b≥a, a sufficiently large).
```

Let b tend to infinity using the just-proved zero limit. It follows that
`S(a)=O(log⁻⁵a)` and `S(a)log²(a+1)→0`. The quantitative Mertens input is
still a hypothesis in these theorems.

## 2. The smoothed boundary constant is proved

[MoebiusBoundary.lean](../TwinPrime/Analytic/MoebiusBoundary.lean) starts from
another exact convolution identity:

```text
Σ_{d≤X} μ(d)/d · H_floor(X/d) = 1.
```

Here H is the harmonic sum. With γ the Euler–Mascheroni constant, set
`R_X(d)=H_floor(X/d)−log(X/d)−γ`. Both the real logarithm argument and the
integer harmonic cutoff are retained. The checked finite estimates are

```text
|R_X(d)| ≤ 2d/X,
Σ_{a≤t<X} |R_X(t+1)−R_X(t)| ≤ 2log X.
```

Split the weighted remainder at a=floor(X^(1/5)). Its first part is at most
2a/X. Discrete partial summation bounds the tail by

```text
[(32+2/log2) K / log⁵a] · (2+2log X).
```

The existing cutoff inequalities make both terms tend to zero. The exact
identity becomes `T(X)+γS(X)+o(1)=1`, proving T(X)→1. The finite formula
`T(x)=log(x)S(floor x)−Σ_{n≤floor x} μ(n)log(n)/n` then identifies the
logarithmic moment as −1 and extends the limit to real x→∞. Neither constant
is an additional assumption in the final wrapper.

## 3. The correction coefficient and the twin constant

[MoebiusSmoothing.lean](../TwinPrime/Analytic/MoebiusSmoothing.lean) defines
the multiplicative correction h by the exact convolution

```text
1_odd(n) μ(n)/φ(n) = (h * (μ/n))(n).
```

Its proved local factors, for positive exponents k, are

```text
h(2^k) = 2^(-k),
h(p^k) = −1/[p^k(p−1)]     for odd primes p.
```

[SmoothingSummability.lean](../TwinPrime/Analytic/SmoothingSummability.lean)
proves absolute summability of h, of √n·|h(n)|, and of log²(n+1)·|h(n)|.
It evaluates the signed Euler product as

```text
Σ h(n) = 2 Π_{p>2}(1−1/(p−1)²) = 2*twinPrimeConstant.
```

The finite convolution bridges are exactly

```text
F(U) = Σ_{d≤U} h(d) S(floor(U/d)),
smoothedTotientSum(U) = Σ_{d≤U} h(d) T(U/d).
```

The second argument U/d is real, not a floored logarithm argument.
[SmoothingLimits.lean](../TwinPrime/Analytic/SmoothingLimits.lean) applies
dominated convergence using the proved correction moments. It concludes

```text
F(U)log²(U+1) → 0,
smoothedTotientSum(U) → 2*twinPrimeConstant.
```

## 4. Connection to the primary endpoint

[MertensReduction.lean](../TwinPrime/Analytic/MertensReduction.lean) packages
these implications from the single explicitly defined `MertensLogSix`
hypothesis. With BV, the previously proved progression and partial-summation
estimates give A_U(X)/X→2C₂ and K_U,U(X)/X→0. The exact Vaughan decomposition,
cofinal (B*), and proved prime-power removal imply twin-prime infinitude.

BV is now proved inside Lean by the independent centered Siegel–Walfisz
chain. The remaining requirement is a proof of (B*) or a valid replacement;
the classical bridges do not establish that signed fixed-shift bound.

A subsequent [elementary reduction](PNT_MERTENS_REDUCTION.md) now derives
the quantitative Mertens input from BV in Lean. It includes the centered
signed error, real hyperbola remainders, unweighting, and actual supremum
contraction. `twinPrimeConjecture_of_bv_and_bilinear` therefore has just the
BV and B* arguments. The earlier three-input theorem remains available.

The newest `twinPrimeConjecture_of_signed_bilinear` supplies the proved
BV theorem to that reduction and retains only B*. See the
[completed proof map](CLASSICAL_DISTRIBUTION_THEOREM.md).
