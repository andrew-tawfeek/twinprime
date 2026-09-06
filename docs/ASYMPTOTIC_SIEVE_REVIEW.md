# Applying the Friedlander–Iwaniec asymptotic sieve to shifted primes

This completes the application audit requested in PLAN.md Section 7.5. The
route remains conditional for two separate reasons: its remainder hypothesis
exceeds the range of classical Bombieri–Vinogradov, and its bilinear hypothesis
requires additional cancellation for the actual shifted-prime sequence.
The elementary density and coefficient conditions do not create a third
unknown. No asymptotic assertion in this review has been added to Lean.

The source is Friedlander–Iwaniec, *Asymptotic sieve for primes*, Annals 148
(1998), 1041–1065, [published-version arXiv PDF](https://arxiv.org/pdf/math/9811186).
Equation numbers below refer to that paper. We use its **Theorem 2**, since the
unmodified sequence is not supported on squarefree integers. Theorem 3 is
considered separately below. The calculations applying those hypotheses are
derived here; none is transferred from the polynomial sequence treated in the
authors' companion paper.

## 1. Exact sequence, densities, and endpoints

For positive integers `n`, put

\[
 a_n=\Lambda(n+2),\quad
 A(t)=\sum_{1\le n\le t}a_n=\psi(t+2)-\log2,
 \qquad
 A_d(t)=\psi(t+2;d,2)-\log2.
 \tag{A}
\]

These are exact identities for integer `t>=0` and `d>=1`; the subtracted
term is the contribution at the shifted integer 2. Take

\[
 g(d)=\begin{cases}1/\varphi(d),&d\text{ odd},\\0,&d\text{ even},\end{cases}
 \qquad r_d(t)=A_d(t)-g(d)A(t).
 \tag{D}
\]

Thus `g` is multiplicative, `g(1)=1`, `g(2^k)=0` for `k>=1`, and
`g(p^k)=1/(p^(k-1)(p-1))` for odd primes. In particular the residue 2 is
coprime to exactly the odd moduli. The singular product specializes to

\[
 H=\prod_p\frac{1-g(p)}{1-1/p}
   =2\prod_{p>2}\frac{p(p-2)}{(p-1)^2}=2C_2.
 \tag{H}
\]

Use the paper at endpoint `x=2X`, together with its conclusion at `x=X`.
Subtraction selects **exactly** `X<n<=2X`, while the upper shifted endpoint is
`2X+2`. The prime-index sum in its conclusion becomes
`sum_(p<=x) log(p) Lambda(p+2)`. Terms with `p+2` a proper prime power have
total weight `O(sqrt(x) log^3(x))=o(x)`: count at most
`sqrt(x+2) floor(log_2(x+2))` powers, each with weight at most `log^2(x+2)`.
Consequently a successful application gives a dyadic weighted twin asymptotic
`2C2 X+o(X)`, hence the same `TwinPrimeConjecture` as the repository endpoint.
This conclusion remains conditional on the two estimates identified below.

## 2. Hypothesis table

Here `K=2^22`, `L=(log x)^(2^24)`, and all sums have positive integer indices.
The formula references specify the precise hypotheses in
[Theorems 1–2, pp. 1041–1044 and 1059](https://arxiv.org/pdf/math/9811186).

| Requirement | Substitution or status |
|---|---|
| Nonnegative coefficients (1.1) | `Lambda(n+2)>=0`. |
| Growth (1.4): `A(x) >> A(sqrt x) log^2 x` | PNT gives `A(x)~x`. |
| Crude bound (1.6): `A_d(x) << d^-1 tau(d)^8 A(x)`, uniformly `d<=x^(1/3)` | Verified below using Brun–Titchmarsh. |
| Density (1.7) | Exact definition (D). |
| Prime densities (1.8): `0<=g(p)<1`, `g(p)<<1/p` | `g(2)=0`, `g(p)=1/(p-1)` for odd `p`. |
| Prime-density sum (1.9): `sum_(p<=y) g(p)=log log y+c+O(log^-10 y)` | Classical PNT error suffices. |
| Square densities (9.1): `0<=g(p^2)<=g(p)`, `g(p^2)<<p^-2` | Immediate from (D). |
| Coefficient norm (9.2): `sum_(n<=x) a_n^2 <= x^(-2/3) A(x)^2` | Holds eventually; see below. |
| Remainders (R3): `sum_(d<D L^2, d cubefree) |r_d(t)| <= A(x)L^-2`, for every `t<=x` | Not supplied at the required level by classical BV. |
| Distribution range (R1): `x^(2/3)<D<x` | First unavailable range. |
| Bilinear (B): `T(x;N,C)<=A(x)log^-K x` | Additional unproved cancellation; defined below. |
| (B1–B3): `sqrt(D)/Delta<N<sqrt(x)/delta`; `delta,Delta>=2`; `1<=C<=x/D` | Every such `N,C`, with one uniform estimate. |
| Useful conclusion (1.17) | Relative error `O(log(delta)/log(Delta))`; require this ratio to tend to zero for an asymptotic. |

Theorem 1's squarefree-support condition (1.16) fails already at
`a_9=log(11)>0`. Removing squareful indices is not a negligible modification:
PNT in the fixed progression `2 mod 9` gives `A_9(x)~x/6`. Theorem 2 is the
appropriate way to keep the original sequence and its original main constant.

### Verification of the available bounds

For odd `d<=x^(1/3)`, Brun–Titchmarsh and the elementary proper-prime-power
bound give

\[
 A_d(x)\le\log(x+2)\pi(x+2;d,2)+O(\sqrt{x}\log^2x)
 \ll\frac{x}{\varphi(d)}+\sqrt{x}\log^2x
 \ll\frac{x\tau(d)}d.
\]

Here `log((x+2)/d)` is a fixed positive proportion of `log x`,
`d/phi(d)<=2^omega(d)<=tau(d)`, and `x/d>=x^(2/3)` absorbs the power error.
For even `d`, every contributing shifted integer is a power of 2, so
`A_d(x)<=log(x+2)`. This proves (1.6), including its full modulus range.
The classical inequality used here is stated in
[Maynard, *On the Brun–Titchmarsh theorem*, p. 2](https://arxiv.org/pdf/1201.1777).

Also

\[
 \frac{\sum_{n\le x}a_n^2}{x^{-2/3}A(x)^2}
 \le\frac{x^{2/3}\log(x+2)}{A(x)}
 \sim\frac{\log x}{x^{1/3}}\longrightarrow0,
\]

which proves the eventual inequality (9.2), even with its coefficient one.
For (1.9), use
`1/(p-1)=1/p+1/(p(p-1))` for odd primes. The correction series converges,
with tail `O(1/y)`; the required error follows from the classical PNT error
for the prime reciprocal sum. These are classical analytic inputs in this
paper audit, not assertions that their proofs are present in the Lean project.

## 3. What BV supplies, and the exact missing range

Write `y=t+2`, `E_d(y)=psi(y;d,2)-y/phi(d)` for odd `d`, and
`E_1(y)=psi(y)-y`. From (A),

\[
 r_d(t)=E_d(t+2)-\frac{E_1(t+2)}{\varphi(d)}
       -(1-1/\varphi(d))\log2 \qquad(d\text{ odd}).
 \tag{E}
\]

This includes `d=1`, where the entire remainder is zero. No progression
estimate is applied to the noncoprime even residue class.

The elementary bound `sum_(d<=Q)1/phi(d)<<log(2Q)` follows by inserting
`d/phi(d)=sum_(e|d) mu^2(e)/phi(e)` and bounding the resulting convergent
Euler product `prod_p(1+1/(p(p-1)))`. Therefore

\[
 \sum_{\substack{d\le Q\\d\text{ odd}}}\max_{t\le x}|r_d(t)|
 \ll\sum_{\substack{d\le Q\\d\text{ odd}}}\max_{y\le x+2}|E_d(y)|
 +\log(2Q)\max_{y\le x+2}|E_1(y)|+Q.
 \tag{E1}
\]

For even moduli we have the stronger collective estimate

\[
 \sum_{\substack{d\le Q\\2\mid d}}\max_{t\le x}|r_d(t)|
 \le\log2\sum_{2\le k\le\log_2(x+2)}\tau(2^k-2)
 \ll_\epsilon x^\epsilon\log x.
 \tag{E2}
\]

Indeed `g(d)=0`, the sums `A_d(t)` increase with `t`, and each positive
`2^k-2` contributes for at most its number of divisors. The usual elementary
divisor bound suffices. Restricting either estimate to cubefree moduli only
reduces its left side.

Maximal BV controls the first term of (E1), with arbitrarily large **fixed**
logarithmic saving, for `Q<=sqrt(x+2)/log^B(x+2)`. The extra logarithm
multiplying `E1`, the boundary term `Q`, and (E2) are harmless in this range. See
[Tao's BV theorem and maximal version, Theorem 17 and Exercise 20](https://terrytao.wordpress.com/2015/01/10/254a-notes-3-the-large-sieve-and-the-bombieri-vinogradov-theorem/).

Substituting `Q=D L^2` shows that classical BV supplies a version of (R3)
only with

\[
 D\ \ll\ \frac{x^{1/2}}{(\log x)^{B+2\cdot2^{24}}}.
\]

This does not meet `D>x^(2/3)`. Increasing the logarithmic saving does not
repair the exponent gap. Even Theorem 1's weaker squarefree-modulus remainder
condition would still require `D>x^(2/3)`.

A sufficient replacement is a maximal distribution estimate in the **fixed
residue 2 over odd cubefree moduli**, through `x^(theta')`, for some
`theta'>theta>2/3`, with a sufficiently large fixed logarithmic saving. Take
`D=x^theta`; then `D L^2<x^(theta')` eventually. A maximal all-residue
Elliott–Halberstam hypothesis would suffice, but is stronger than this stated
requirement. Restricted-modulus or signed-weight distribution estimates cannot
be substituted without proving that they control this sum of absolute errors.

## 4. The actual bilinear norm and a coefficient-overlap obstruction

For the proposed sequence, the missing norm is

\[
 T(x;N,C)=\sum_{m\ge1}\left|
  \sum_{\substack{N<n\le2N\\mn\le x}}
  \gamma_C(n)\mu(mn)\Lambda(mn+2)\right|,
 \qquad
 \gamma_C(n)=\sum_{\substack{d\mid n\\d\le C}}\mu(d).
 \tag{FI-B}
\]

The coefficient is this particular truncated divisor sum, not an arbitrary
bounded coefficient, and not the repository's `beta_V`. It satisfies
`|gamma_C(n)|<=tau(n)` and includes `gamma_1(n)=1`. Since
`mu(mn)=mu(m)mu(n)1_((m,n)=1)`, only squarefree coprime factors contribute.
The coprimality condition must remain after this factorization.

The outer absolute values matter: (FI-B) is the supremum over all real
outer coefficients `|alpha_m|<=1` of the absolute value of the corresponding
double sum. This follows by choosing the sign of each inner sum. It therefore
asks for substantially more than a favorable sign in one aggregate sum.

There is a useful **exact finite obstruction** when the divisor cutoff
overlaps the factor interval. For integer `N>=1` and squarefree `N<n<=2N`,

\[
 \mu(n)\gamma_N(n)
 =\sum_{\substack{e\mid n\\e\ge n/N}}\mu(e)
 =-\sum_{\substack{e\mid n\\e<n/N}}\mu(e)=-1.
 \tag{O}
\]

The complementary sum contains only `e=1`, including at `n=2N`. Thus

\[
 T(x;N,N)=
 \sum_{\substack{N<n\le2N\\mn\le x\\mn\text{ squarefree}}}
   \Lambda(mn+2).
 \tag{O1}
\]

No Möbius cancellation survives inside any row. This identity alone does not
assert an asymptotic lower bound for (O1), but it rules out an argument that
credits this coefficient range with automatic sign cancellation.

To keep the largest permitted coefficient cutoff well below the smallest
factor scale, the natural separation is

\[
 \frac{C_{\max}}{N_{\min}}
 =\frac{x/D}{\sqrt D/\Delta}
 =\frac{\Delta x}{D^{3/2}}=o(1).
 \tag{O2}
\]

Writing `D=x^theta`, `Delta=x^eta` gives
`0<eta<3theta/2-1`. A positive power margin is possible only when
`theta>2/3`. If one simply inserts the BV level, `Cmax` exceeds the entire
upper factor range and the allowed family contains `C=N`; (O1) exposes the
changed nature of the requirement. This is a coefficient-level reason that
the published range restriction cannot simply be erased.

A concrete conditional choice is

\[
 D=x^{3/4},\quad\Delta=x^{1/32},\quad\delta=(\log x)^a\quad(a>0).
\]

It requires all blocks `x^(11/32)<N<sqrt(x)/log^a(x)` and every
`1<=C<=x^(1/4)`. The coefficient/factor ratio is at most `x^(-3/32)` and
the theorem's relative error tends to zero. Its remainder requirement still
runs beyond `x^(3/4)` by the specified logarithmic factor.

### Why a routine Cauchy step does not finish this norm

Even for `C=1`, applying Cauchy in `m` squares sums with terms

\[
 \mu(n_1)\mu(n_2)
 \Lambda(mn_1+2)\Lambda(mn_2+2),
 \qquad (m,n_1n_2)=1,
\]

with the squarefree `m` restriction and both hyperbolic endpoints retained.
For `n1!=n2` these are prime correlations of two different linear forms in
`m`; ordinary BV for one progression supplies no estimate for their required
signed aggregate. Discarding these terms as nonpositive is unjustified.
Taking absolute values throughout instead gives, using `|gamma|<=tau`,

\[
 T(x;N,C)\le\log(x+2)\sum_{N<n\le2N}\tau(n)\lfloor x/n\rfloor
 \ll x\log^2x,
\]

which falls short of `x/log^(2^22)(x)`. This is the first unsupported step
in that attempted proof, rather than a missing manipulation of BV.

Shifted proper prime powers can be removed from (FI-B) without creating a
main-order obstruction: their total absolute contribution is bounded by
`sum_(p^k<=x+2,k>=2) log(p) tau_3(p^k-2)` and hence by
`O_epsilon(x^(1/2+epsilon) log^2 x)`. The unresolved part remains on actual
shifted primes.

## 5. The rough-factor variant and comparison with PLAN (B*)

The paper's Theorem 3 replaces its bilinear condition with a version restricted
by `(n,prod_(p<P)p)=1`, with saving `log^(-2^26)(x)` and

\[
 2\le P\le\Delta^{1/(2^{35}\log\log x)}.
\]

It retains Theorem 2's other requirements.
[Source: Section 10, pp. 1063–1065](https://arxiv.org/pdf/math/9811186).
For the displayed choice `Delta=x^(1/32)`, this is only `P=x^(o(1))`, far
below a fixed positive power of `x`. It cannot be identified with PLAN 9's
cube-root roughness. It also does not force `gamma_C=1` throughout the required
family: `Cmax=x^(1/4)` greatly exceeds this allowable `P`. This variant may
be technically useful if a new estimate benefits from removing small prime
factors, but it does not repair the missing distribution level.

The paper labels that variant `(B*)`; it is **different from PLAN's (B*)**.
PLAN needs a cofinal one-sided bound of size `-C X/2` for its one specified
full Vaughan bilinear sum at `U=V=floor(X^(1/5))`. The FI hypothesis requires
small absolute row sums, uniformly over its coefficient and factor ranges,
at every sufficiently large endpoint. Those ranges omit portions of the
Vaughan factor domain; FI pays for the complementary portions with its
stronger remainder input. There is no direct termwise inequality identifying
the two bilinear expressions, and this review proves no logical implication
between the two standalone hypotheses.

As a complete conditional package, FI gives a stronger conclusion: the full
weighted twin asymptotic. Combined with the classical inputs in the repository's
exact decomposition, it would force its normalized Vaughan bilinear term to
tend to zero, stronger than the cofinal one-sided budget actually needed.
It is therefore not an established weakening of the current target.

**Route decision:** retain this as a precisely stated conditional alternative.
Do not begin a large formalization on the premise that only (FI-B) remains.
An application needs both the cubefree fixed-residue remainder estimate above
level `2/3` and a genuine estimate for (FI-B), or for its carefully restricted
rough-factor variant. The usable structural result from this audit is the
exact coefficient-overlap identity (O), together with the explicit separation
ratio (O2). Neither estimate follows from the finite identities already proved
in the repository.

## Audit checks

The displayed source formulas were checked against rendered pages 1043, 1059,
and 1063 of the published paper, including the exponents `2^22`, `2^24`,
`2^26`, and the denominator `2^35 log log x`. The latter is also confirmed by
the Rankin estimate on p. 1064, which uses `log(Delta)/log(P)`.

An independent in-memory trial-factorization check verified
`mu(m*n)*gamma_N(n) = -mu(m)` for squarefree `m*n`, and zero otherwise,
for all `1<=N<=100`, `N<n<=2N`, `1<=m<=100`: **505,000 exact integer
checks passed**. This checks the finite coefficient identity only. Its proof
is (O), and the experiment supplies no asymptotic estimate for (O1).
Only this document was added for the audit; no Lean files were changed.
