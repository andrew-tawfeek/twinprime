# A quantitative elementary reduction from the prime estimate to Mertens

This document gives a paper proof that the repository's
`MaximalBombieriVinogradov` implies `MertensLogSix`. **This implication is
now formalized in [PrimeToMertens.lean](../TwinPrime/Analytic/PrimeToMertens.lean).**
The refined conditional endpoint derives Mertens from BV. The signed bilinear
input (B*) is unaffected and remains open.

The argument uses the exact second-order convolution identity appearing in
Ramaré, *From explicit estimates for primes to explicit estimates for the
Möbius function*, [§3, equation (3.3)](https://ramare-olivier.github.io/Maths/ElementaryConversion-11.pdf).
The quantitative contraction below is supplied here; it is not an appeal
to that paper's explicit numerical theorem. It uses neither a zero-free
region nor an assertion about the boundary values of the reciprocal zeta
function.

## 1. Statement and endpoint conventions

For real `x >= 1`, put

\[
\psi(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n),\qquad
M(x)=\sum_{1\le n\le\lfloor x\rfloor}\mu(n).
\]

Every arithmetic convolution below is over **positive** integer factors:
`(f*g)(n) = sum_{de=n} f(d)g(e)`. Write `1` for the constant-one arithmetic
function and `epsilon` for the convolution identity, supported at 1. These
correspond to arithmetic functions taking value zero at the unused index
0 in Lean. Thus `mu*1 = epsilon`.

We prove the following implication:

\[
\psi(x)=x+O\!\left(\frac{x}{(\log x)^6}\right)
\quad\Longrightarrow\quad
M(x)=O\!\left(\frac{x}{(\log x)^6}\right).                 \tag{1}
\]

All estimates are as `x -> infinity`; constants may depend on the prime
estimate and its initial threshold. Estimates used on `x >= 2` can be
extended to that whole range by increasing their constants, since the
remaining interval is bounded. Natural endpoints are recovered by
restriction. No sum includes zero, and no estimate divides by `log 1`.

Here is how the premise follows from the repository's exact BV definition.
Choose `A=6` and `Q=1`. Its admissibility condition holds for all sufficiently
large natural `X`, because

\[
\frac{\sqrt X}{(\log X)^B}\longrightarrow\infty.
\]

The maximal error at modulus 1 includes the endpoint `t=X` and the reduced
residue `a=0`: `0 < 1`, `Coprime 0 1`, and `X <= 2*X+2`.
Also `totient 1=1`, and congruence modulo 1 imposes no restriction.
The single term of the modulus sum therefore bounds
`|psi(X)-X|` by `K*X/(log X)^6`. For real `x`, set `N=floor x` and use
`|psi(x)-x| <= |psi(N)-N|+1`. For sufficiently large `x`,
`N >= x/2` and `log N >= (log x)/2`; the extra constant is absorbed.
This proves precisely the real premise of (1).

## 2. A centered convolution with a strong summatory error

Write `R(x)=psi(x)-x`. Partial summation gives, exactly for real `x >= 1`,

\[
L(x):=\sum_{n\le x}\frac{\Lambda(n)}n
 =\log x+1+\frac{R(x)}x+\int_1^x\frac{R(t)}{t^2}\,dt.
\]

The prime estimate makes the improper integral absolutely convergent at
infinity. Define the real constant

\[
c=1+\int_1^\infty\frac{R(t)}{t^2}\,dt.
\]

It follows that

\[
L(x)=\log x+c+O((\log x)^{-5}).                           \tag{2}
\]

Indeed the tail integral is bounded by a constant times
`integral_x^infinity dt/(t log^6 t) = 1/(5 log^5 x)`, and
`R(x)/x=O(log^-6 x)`. **There is no need to identify `c` with `-gamma`.**
In particular this step imports no Möbius cancellation or previously
computed Möbius boundary constant.

Set

\[
a=\Lambda*\Lambda-\Lambda\log-2c\,1,
\qquad A(x)=\sum_{n\le x}a(n).
\]

We claim

\[
A(x)=O\!\left(\frac{x}{(\log x)^5}\right).                \tag{3}
\]

Let `y=sqrt x` as a real number. The exact hyperbola identity is

\[
\sum_{mn\le x}\Lambda(m)\Lambda(n)
 =2\sum_{n\le y}\Lambda(n)\psi(x/n)-\psi(y)^2.
\]

Because `y*y=x`, every pair in the left side has one coordinate at most
`y`; the intersection is exactly the rectangle with both coordinates at
most `y`. Thus this identity remains exact when `y` is not integral.
Substitute `psi(t)=t+R(t)` to obtain

\[
2xL(y)-x+
2\sum_{n\le y}\Lambda(n)R(x/n)-2yR(y)-R(y)^2.
\]

Since `x/n >= sqrt x`, the first error sum is

\[
O\!\left(\frac{x}{(\log x)^6}
          \sum_{n\le\sqrt x}\frac{\Lambda(n)}n\right)
 =O(x/(\log x)^5),
\]

using (2). The other two errors are smaller. Equation (2) now gives

\[
\sum_{mn\le x}\Lambda(m)\Lambda(n)
 =x\log x+(2c-1)x+O(x/(\log x)^5).                        \tag{4}
\]

A second exact partial summation identity gives

\[
\sum_{n\le x}\Lambda(n)\log n
 =\psi(x)\log x-\int_1^x\frac{\psi(t)}t\,dt
 =x\log x-x+O(x/(\log x)^5).                             \tag{5}
\]

For the last error, `R(x) log x = O(x/log^5 x)` and
`integral_1^x R(t)/t dt = O(x/log^6 x)`. The latter bound follows by
splitting at `sqrt x`: the first part is `O(sqrt x)` from `R(t)=O(t)`;
the second is `O(x/log^6 x)`. The constant from integrating the main term
is absorbed. Subtract (5) from (4) and then subtract `2c floor x`.
The remaining `2c(x-floor x)` is bounded, proving (3).

We also need an absolute coefficient estimate. The prime premise implies
there is `Cpsi >= 1` with `0 <= psi(t) <= Cpsi*t` for every real `t >= 1`.
Partial summation yields `L(y) <= Cpsi*(1+log y)`. Therefore for `y >= 1`,

\[
\begin{aligned}
H(y):=\sum_{k\le y}\frac{|a(k)|}{k}
&\le L(y)^2+(\log y)L(y)+2|c|(1+\log y)\\
&\le D(1+\log y)^2,\qquad
D=C_\psi^2+C_\psi+2|c|.                                  \tag{6}
\end{aligned}
\]

For the convolution term, enlarge the region `mn <= y` to
`m <= y, n <= y`, using `Lambda >= 0`. For the last term use the elementary
harmonic bound. This estimate uses absolute values of `a` and does not
assume cancellation in it.

## 3. The exact Möbius identity and the second hyperbola split

Let `Df(n)=f(n)log n`, a derivation for Dirichlet convolution. From
`D mu = -mu*Lambda`, apply `D` once more to get

\[
D^2\mu=\mu*(\Lambda*\Lambda-\Lambda\log).
\]

Since `mu*1=epsilon`, this proves the exact arithmetic identity

\[
\mu*a=\mu\log^2-2c\,\epsilon.                            \tag{7}
\]

Fix `0 < delta < 1/2`, to be chosen below, and put
`y=x^delta`, `z=x^(1-delta)`, so `yz=x`. Define
`S2(x)=sum_{n<=x} mu(n) log^2 n`. The exact rectangular hyperbola split
of (7) is

\[
S_2(x)-2c
 =\sum_{k\le y}a(k)M(x/k)
   +\sum_{d\le z}\mu(d)A(x/d)-A(y)M(z).                  \tag{8}
\]

This includes equality endpoints on both sums and subtracts their common
rectangle once. Real `y,z` introduce no floor error in (8).

For all sufficiently large `x`, `x/d >= y >= 2` in the second sum. From
(3), `|mu(d)| <= 1`, and the harmonic bound,

\[
\left|\sum_{d\le z}\mu(d)A(x/d)\right|
 \ll \frac{x}{(\delta\log x)^5}\sum_{d\le z}\frac1d
 \ll_\delta \frac{x}{(\log x)^4}.
\]

The boundary term satisfies
`|A(y)M(z)| <= |A(y)|z <<_delta x/log^5 x`, using the trivial
bound `|M(z)| <= floor z <= z`. The constant `2c` can also be absorbed.
Consequently (8) gives

\[
|S_2(x)|
 \le\sum_{k\le x^\delta}|a(k)|\,|M(x/k)|
       +E_\delta\frac{x}{(\log x)^4}                     \tag{9}
\]

for some fixed `E_delta >= 0` and every sufficiently large real `x`.
No estimate for `M` beyond its trivial bound has been used to obtain this.

## 4. Weighted supremum and contraction

For real `x >= 2`, define

\[
w(x)=\frac{|M(x)|(\log x)^6}{x},\qquad
W(x)=\sup_{2\le t\le x}w(t).
\]

`W(x)` is finite for each finite `x`, since `|M(t)| <= t` and `log t`
is bounded on the interval. It is nonnegative and nondecreasing. We do
**not** assume `W` is bounded independently of `x`.

For sufficiently large `x` and `k <= x^delta`, we have
`2 <= x/k <= x` and `log(x/k) >= (1-delta)log x`. Thus

\[
\sum_{k\le x^\delta}|a(k)|\,|M(x/k)|
 \le \frac{W(x)x}{(1-\delta)^6(\log x)^6}H(x^\delta).
                                                                    \tag{10}
\]

The possible term `k=1` involves `M(x)` itself. This is allowed: it is
bounded by the same finite supremum, and the contraction below absorbs
it together with all other terms. There is no inductive circularity.

Abel summation, with the zero weight at `n=1` included, gives

\[
S_2(x)=M(x)(\log x)^2
       -2\int_1^x\frac{M(t)\log t}{t}\,dt.
\]

On `1 <= t < 2` the integral is bounded by a fixed constant. On
`2 <= t <= x`, the definition of `W(x)` bounds its absolute integrand by
`W(x)/(log t)^5`. The elementary estimate

\[
\int_2^x\frac{dt}{(\log t)^5}
 \le C_I\frac{x}{(\log x)^5}
\]

holds for all sufficiently large `x`. To verify it, split at `sqrt x`:
the lower part is at most `sqrt x/(log 2)^5`, and the upper part is at most
`32x/(log x)^5`. Increase the fixed constant to absorb the former part.

Combine this with (9), (10), and (6), and multiply by `(log x)^4/x`.
After increasing `E_delta` to absorb the fixed initial integral, we get

\[
w(x)\le
\left[
 \frac{D(\delta+1/\log x)^2}{(1-\delta)^6}
 +\frac{2C_I}{\log x}
\right]W(x)+E_\delta.                                   \tag{11}
\]

Choose `delta` small enough that
`D*delta^2/(1-delta)^6 < 1/4`. This is possible because `D` is fixed
before `delta` is chosen. Then choose a fixed `x0 >= 2`, also satisfying
all previous thresholds, such that the coefficient in square brackets
is at most `1/2` for every `x >= x0`.

For any `X >= x0`, each `t` in `[x0,X]` now satisfies
`w(t) <= W(t)/2+E_delta <= W(X)/2+E_delta`. On `[2,x0]` we have
`w(t) <= W(x0)`. Taking the supremum gives

\[
W(X)\le\max\{W(x_0),\tfrac12W(X)+E_\delta\},
\]

and hence

\[
W(X)\le\max\{W(x_0),2E_\delta\}.
\]

This is a bound independent of `X`. It proves (1), with a nonnegative
constant as required by `MertensLogSix`. Restricting to natural endpoints
matches that definition exactly.

## 5. Formalization status and resulting scope

The BV-to-Mertens conclusion is now checked in Lean, including the constant
sign in (7), both real hyperbola endpoints, the logarithmic losses before
unweighting, and the finite supremum argument. The formal weighted-prime
step uses BV's maximal ordinary error directly. Thus the formal theorem is
`MaximalBombieriVinogradov → MertensLogSix`; the broader implication (1)
from an arbitrary ordinary prime-error hypothesis remains a paper result.

The exact logarithmic derivation and identity (7) are now checked in
[`MoebiusSelberg.lean`](../TwinPrime/Analytic/MoebiusSelberg.lean), including
the finite divisor-pair formula and all natural endpoints. The parameter
`c` is arbitrary in that algebraic result. The reciprocal-sum estimates
construct the particular center used in the analytic proof.

The following additional parts are now checked in Lean:

| Step | Checked implementation |
|---|---|
| Extract the prime error from modulus one of BV | [BombieriVinogradovPsi.lean](../TwinPrime/Analytic/BombieriVinogradovPsi.lean), including every integer endpoint through `2X+2` |
| Extend the prime error to real endpoints | [PrimeReal.lean](../TwinPrime/Analytic/PrimeReal.lean); an exponent k uses explicit constant `2^k K+1` |
| Construct c and prove the integer reciprocal remainder | [PrimeReciprocal.lean](../TwinPrime/Analytic/PrimeReciprocal.lean); apply the existing generic Abel theorem to `Lambda(n)-1` and the harmonic remainder, with error constant `(32+2/log2)K+1` |
| Preserve c and the remainder for the actual real logarithm | [PrimeReciprocalReal.lean](../TwinPrime/Analytic/PrimeReciprocalReal.lean); the floor-log difference is at most `2/x`, and a natural remainder constant C becomes `32C+2` |
| Exact integer and real hyperbola identities | [Hyperbola.lean](../TwinPrime/Analytic/Hyperbola.lean), with both strips and their common rectangle |
| Instantiate both splits with the actual coefficients | [SelbergSummatory.lean](../TwinPrime/Analytic/SelbergSummatory.lean), including the `-2c` term at positive endpoints and the square-root prime convolution |
| Absolute reciprocal coefficient mass | [SelbergCoefficientBounds.lean](../TwinPrime/Analytic/SelbergCoefficientBounds.lean), using only Chebyshev's elementary upper bound |
| Absorb an established contraction into a locally finite supremum | [SupremumContraction.lean](../TwinPrime/Analytic/SupremumContraction.lean), without assuming continuity or a global bound |
| Logarithmically weighted prime estimate, including the linear term | [LogFactorial.lean](../TwinPrime/Analytic/LogFactorial.lean), [PrimeLog.lean](../TwinPrime/Analytic/PrimeLog.lean); discrete Abel summation and explicit real endpoint corrections |
| Centered signed summatory error (3) | [SelbergCenteredError.lean](../TwinPrime/Analytic/SelbergCenteredError.lean), [PrimeToSelberg.lean](../TwinPrime/Analytic/PrimeToSelberg.lean); all three prime estimates are discharged from BV |
| Möbius hyperbola remainder (9) | [SelbergMoebiusError.lean](../TwinPrime/Analytic/SelbergMoebiusError.lean); the tail and overlap use only the trivial Mertens bound |
| Reciprocal-log kernel and real logarithmic unweighting | [LogKernel.lean](../TwinPrime/Analytic/LogKernel.lean), [MoebiusLogWeight.lean](../TwinPrime/Analytic/MoebiusLogWeight.lean); includes the final fractional interval |
| Local boundedness and the actual short-head estimate (10) | [WeightedMertens.lean](../TwinPrime/Analytic/WeightedMertens.lean); no uniform supremum bound is assumed |
| Parameter choice and the arithmetic contraction (11) | [ContractionParameters.lean](../TwinPrime/Analytic/ContractionParameters.lean), [MertensContraction.lean](../TwinPrime/Analytic/MertensContraction.lean) |
| Complete BV-to-Mertens implication | [PrimeToMertens.lean](../TwinPrime/Analytic/PrimeToMertens.lean), `MaximalBombieriVinogradov.mertensLogSix` |

The reciprocal center is obtained from a convergent ordinary error sum;
neither c nor its limit is assumed. The formal absolute-mass bound uses
`D'(2+log y)^2`, where `D'=Kpsi^2+Kpsi+2|c|` and
`Kpsi=log4+4`. This is slightly looser than (6). The checked contraction uses

```text
D'(delta+2/log x)^2/(1-delta)^6 + [128(1+14^5)+4]/log x.
```

Its limiting coefficient is unchanged. The kernel sum is bounded by
`(1+14^5)x/log^5 x` at natural endpoints; the explicit real floor comparison
and final fractional interval account for the displayed larger constant.
The parameter is fixed after D' and the unweighting constant, and the
coefficient is eventually at most 1/2. Local supremum absorption then
produces a bound independent of x and yields exactly `MertensLogSix`.

The refined endpoint `twinPrimeConjecture_of_bv_and_bilinear` now eliminates
the separate `MertensLogSix` parameter from the
[classical reduction](CLASSICAL_REDUCTION.md). Its BV argument is now supplied by
the [independent classical chain](CLASSICAL_DISTRIBUTION_THEOREM.md), while the
cofinal signed bilinear inequality (B*) remains open. This argument is not a proof of the twin primes
conjecture and does not claim that (B*) follows from a distribution estimate.
