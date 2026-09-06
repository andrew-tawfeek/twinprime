# A concrete Chen weight: lower mass and semiprime leakage

This reviews the alternative in PLAN.md Section 8 using the explicit Chen
weight in Tao's proof, with roughness exponent **1/8**. It does not supply a
twin-prime lower bound. For this weight the available lower and leakage
constants give a strictly negative margin, and the aggregate estimates admit
zero twin mass. This is a limitation of the stated estimates, not a theorem
excluding every refinement of Chen's method.

## Selected interval and weight

Let `X` be an integer, put `x=2X+2`, and take `x` sufficiently large. Then
the integer interval `[x/2,x-2]` is exactly `(X,2X]`. Set

\[
 z=x^{1/8},\qquad y=x^{1/3},\qquad
 P_{<}(z)=\prod_{\ell<z,\ \ell\ \mathrm{prime}}\ell.
\]

This uses the source's strict primorial cutoff: surviving prime factors are
at least `z`. The repository's `RoughParity.lean` instead uses a primorial
including primes at its integer cutoff. No equality of these supports is
assumed.

For `m=p+2`, define the following integer counts:

\[
 k(m)=\#\{q\le y:q\text{ prime},\ q\mid m\},\quad
 j(m)=\#\{q\le y:q\text{ prime},\ q^2\mid m\},
\]

\[
 t(m)=\sum_{q\le y<r\le s\atop q,r,s\ \mathrm{prime}}
          1_{m=qrs},\qquad
 w(m)=1-\tfrac12 k(m)-\tfrac12 j(m)-\tfrac12 t(m).
\]

Choose the nonnegative weight on primes in `(X,2X]`

\[
 a_X(p)=1_{(p+2,P_{<}(z))=1}\max(w(p+2),0).
 \tag{1}
\]

It is the positive part of the standard Chen minorant, including its square
correction. The half-weight and triple subtraction already occur in
[Halberstam's proof, Sections 1–2](https://www.numdam.org/article/AST_1975__24-25__281_0.pdf),
whose cutoff is `x^(1/10)`. The **selected** cutoff and interval here come
from [Tao's proof, Section 3 and Lemma 11](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/).
We do not transfer a numerical constant from Halberstam's different variant.

Here is a direct check of (1). On the interval, `y^2<m<=y^3=x`.
If `m` has at least three prime factors with multiplicity, it cannot have
zero factors at most `y`. If it has two distinct such factors, `k>=2`.
If it has only one, either its square divides `m`, or the other factors
are exactly two primes greater than `y`. The square or triple subtraction
then makes `w<=0`. Conversely, a semiprime in this interval cannot have
both factors at most `y`. Thus:

| Shifted factorization, after the `z` filter | Weight |
|---|---:|
| `m` prime | 1 |
| `m=qr`, `z<=q<=y<r` | 1/2 |
| `m=qr`, `y<q<=r` | 1 |
| `Omega(m)>=3` | 0 |

In particular `0<=a_X<=1`. Squares `q^2` are in the third row and have
Liouville value `+1`. The product representation uses `q<=r` and counts each
semiprime once. The interval excludes `m=0,1`, and every twin in `(X,2X]`
has weight 1 for sufficiently large `X`.

## Exact mass and parity identities

Let `T=N2(X)`. Define `E` and `B` to be the counts in the second and third
rows of the table, with `qr-2` prime and the exact condition

\[
 X<qr-2\le2X.
\]

Let `S_y` count primes `p` in `(X,2X]` whose shifted value has every prime
factor strictly greater than `y`. The cube cutoff classifies this smaller
support, giving exact identities

\[
 C_a:=\sum_p a_X(p)=T+\tfrac12E+B
       =\tfrac12E+S_y,\qquad S_y=T+B. \tag{2}
\]

Consequently the weighted semiprime leakage is `D_a=E/2+B`, and

\[
 L_a:=\sum_p a_X(p)\lambda(p+2)=-T+D_a,
 \qquad T=C_a-D_a=\tfrac12(C_a-L_a). \tag{3}
\]

The `x^(1/8)` roughness in (1) alone does **not** imply `Omega(m)<=2`.
The weight supplies that restriction. Raising the roughness to `y` removes
the entire `E/2` contribution in (2); Chen's lower bound cannot simply be
retained after this removal.

For this exact weight, a sufficient alternative to the primary bilinear
input is a fixed `delta>0` and cofinally many `X` with `C_a(X)>0` and
`L_a(X)<=(1-delta)C_a(X)`. Equation (3) then gives
`N2(X)>=delta*C_a(X)/2>0`, and the repository's cofinal dyadic endpoint
implies `TwinPrimeConjecture`. The positive lower bound below supplies the
mass premise eventually; the strict fractional parity bound is a separate
unproved input. It is not supplied by the known Chen estimates.

## Published inputs and normalization

Write

\[
 \mathfrak c_2=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right),
 \qquad M(x)=\mathfrak c_2\frac{x}{\log^2x}.
\]

Thus `M(2X+2)~2 c2 X/log^2 X`. In the source's notation, equations
(40), (41), and the bound following (42) give respectively

\[
 A_1\ge(4\log3-o(1))\frac{\mathfrak c_2x}{\log x},\quad
 \sum_q A_{2,q}\le(4\log6+o(1))\frac{\mathfrak c_2x}{\log x},
\]
\[
 A_3\le(4J+o(1))\frac{\mathfrak c_2x}{\log x},\qquad
 J=\int_{1/8}^{1/3}\frac{\log(2-3u)}{u(1-u)}\,du.
 \tag{4}
\]

Here `A1` is the von Mangoldt weighted rough mass; `A2,q` additionally
requires `q|p+2`; `A3` counts the displayed triple products. The source's
linear sieve has `F(s)=2e^gamma/s` for `1<s<=3` and
`f(4)=e^gamma log(3)/2`.
[Tao, Theorem 2 and Section 3](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/)

For completeness, the omitted square penalty costs at most

\[
 \log x\sum_{z\le q\le y}\left(\frac{x}{q^2}+1\right)
 \ll x^{7/8}\log x=o(x/\log x).
\]

Removing prime powers of the left variable costs `O(sqrt(x) log^2 x)`:
on the rough support `Omega(m)<=8`, so the absolute minorant is bounded
by 6. These errors are separate from the prime squares retained in `B`.
If the real cutoff `y` is itself prime, changing an `A2,q` endpoint from
`q<y` to `q<=y` costs at most `O(x^(2/3) log x)`, also negligible here.
Taking the positive part increases the minorant sum. Dividing by
`log x`, which bounds `log p` above, therefore gives

\[
 C_a\ge(\kappa-o(1))M(x),\qquad
 \kappa=4\log3-2\log6-2J
        =2\bigl(\log(3/2)-J\bigr)>0. \tag{5}
\]

The constant is positive without relying on numerical quadrature. For
`t=1-3u>=0`, use `log(1+t)<=t-t^2/2+t^3/3`. Integration gives

\[
 J\le J_3:=\frac{175}{128}
       +\frac{20}{3}\log\frac{16}{21}
       +\frac56\log\frac83<\frac38.
\]

Also `log(3/2)>2(1/5+(1/5)^3/3)=152/375`, hence
`kappa>91/1500`. One exact rational certificate for `J3<3/8` uses
eight terms of `log r=2 sum_{j>=0} h^(2j+1)/(2j+1)`, where
`h=(r-1)/(r+1)`. The absolute tail after eight terms is at most
`2|h|^17/(17(1-h^2))`. Substituting `h=-5/37` and `5/11`
gives a rational upper bound strictly below `3/8`.

## Leakage on the same support

Every element of `E` occurs exactly once in the corresponding `A2,q` sum;
extra products and left prime powers only enlarge that sum. Since
`log p>=log(x/2)`, (4) implies

\[
 E\le(4\log6+o(1))M(x). \tag{6}
\]

For `B`, use `B<=S_y`. Apply the upper linear sieve to the original prime
sequence at `y=x^(1/3)`, with `D=x^(1/2-epsilon)`. Its parameter tends
to `s=3/2`, and its main term is

\[
 \frac{x}{2}\frac{2e^\gamma}{s}
       \frac{2\mathfrak c_2}{e^\gamma\log y}
 =\frac{2\mathfrak c_2x}{\log D}
 =(4+o(1))\frac{\mathfrak c_2x}{\log x}.
\]

Using the strict condition `q>y` only shrinks this sifted set. Conversion
from logarithmic weights therefore gives `B<=S_y<=(4+o(1))M(x)`.
Combining with (6),

\[
 D_a\le(U+o(1))M(x),\qquad U=2\log6+4. \tag{7}
\]

The resulting coefficient in the twin lower bound (3) is exactly

\[
 \boxed{\kappa-U=-4\log2-2J-4<0.} \tag{8}
\]

For orientation only, quadrature gives
`J=0.3630837292...`, `kappa=0.0847627577...`,
`U=7.5835189385...`, and `kappa-U=-7.4987561807...`.
Equation (8), rather than these decimals, proves that the stated estimates
leave no positive margin. The upper bound (7) is not asserted to be optimal.

## Where the estimate fails and what the sources supply

The range substitutions below are for the selected weight. Take fixed
`0<epsilon<1/24`, and then let it tend to zero in the limiting constants.
At no point is distribution beyond exponent `1/2` being invoked.

| Term | Moduli and sieve parameter | Available input |
|---|---|---|
| `A1` | odd squarefree `d<=D`, residue `-2`; `s=4-8epsilon` | Prime BV, lower linear sieve |
| `sum A2,q` | `z<=q<=y`, `d|P_<(z)`, `(d,q)=1`, `qd<=D`; `4/3-8epsilon<=s<=3-8epsilon` | Prime BV, upper linear sieve; summing repeated moduli loses at most `O(log x)` |
| `A3` | switched products `qrs`, `z<=q<=y<r<=s`; residue `+2` modulo squarefree `d<=D` | The source's Proposition 13: convolution distribution from the classical BV method and Siegel–Walfisz; then an upper sieve with parameter tending to 1 |
| `S_y` | original prime sequence, `d<=D`; `s=3/2-3epsilon` | Upper linear sieve gives 4; its lower function is zero here |

The local density is `g(2)=0`, `g(l)=1/(l-1)` for odd primes.
All displayed counts use the same shift and interval. Proposition 13 is
a distribution theorem for a switched convolution, not merely a restatement
of the single prime-progression BV estimate. None of these analytic inputs
is newly formalized by this review.

There is also a direct numerical-budget obstruction. For this coefficient
test use the logarithmically weighted versions of `T,E,B,C_a,L_a` and
normalize every sum by `c2 x/log x`. The identities remain valid after
inserting the common weight `log p`; left prime powers contribute only
the negligible error already bounded above. The nonnegative component assignment

\[
 T=B=A_3=0,\qquad E=A_1=\sum A_{2,q}=4\log3
\]

satisfies the aggregate lower and upper constraints (4), since
`log3<log6`. It has `C_a=2log3>=kappa`, `D_a=C_a`, and `L_a=C_a`.
Thus these constraints do not imply the required strict fractional parity
bound on `L_a`. This assignment is a feasibility test for the listed
aggregate inequalities, not a construction of actual primes or a model
satisfying every BV progression constraint.

Returning to the unweighted counts, attempting to retain only the cube-root
rough part gives from (2), (5), and (6) just

\[
 S_y\ge(\kappa-2\log6-o(1))M(x),
\]

whose coefficient is negative. A positive lower bound for `S_y` would still
include balanced semiprimes. One must improve the compatible total/leakage
budget, or establish new signed information in (3); changing the support or
relabeling the Chen lower bound does neither. No such additional estimate
is obtained here, and no implication from this particular missing estimate
to or from PLAN's separate bilinear hypothesis (B*) is claimed.

## Checks

The factorization proof and constant comparison above are paper arguments.
An in-memory exact-arithmetic check tested 1,129 rough shifted values at
`x=32,64,128,256,512,1024,2048`, covering multiplicities 1 through 8,
233 square-correction cases and 58 triple-correction cases. It verified
the weight table and all four finite mass/parity equalities in (2)–(3)
on the seven corresponding prime intervals. Cutoffs were tested by the
integer comparisons `q^8>=x` and `q^3<=x`, without rounding real powers.
The logarithm bound for `J3` was separately checked with exact fractions
and the displayed series remainder. Floating-point quadrature supplied
only the illustrative decimals.

No large enumeration, Lean change, build, external upload, or new
conditional endpoint was performed for this review.

## Combining the existing class and moment inequalities

Checkpoint: 2026-09-05. The
[divisor-moment assessment](DIVISOR_SWITCH_BUDGET.md) and the
middle-prime bound do not repair the leakage budget above.
There is a support distinction even before their different
cutoffs are considered.

Chen's central prime is p, with p+2 rough. In the divisor
assessment, the central prime is p=n+2, with p-2=n rough.
When the cutoffs exceed 3, these central primes satisfy
p=2 mod 3 and p=1 mod 3, respectively. Their composite
leakage masses cannot be identified. The middle-prime class
also has central prime 1 mod 3 once U>3.

Both original notes nevertheless use the same interval for
the lower integer in a genuine twin pair. With the common
weight log(n)log(n+2), their genuine twin mass is exactly
Q_tw. The backward central-prime interval is then
(X+2,2X+2], not (X,2X]. If both central-prime intervals are
instead aligned, the genuine pair sums differ by at most
4 log^2(2X+2). This endpoint correction does not identify
the composite supports.

For transferring the Chen estimates to the common weight,
any nonnegative coefficient b on its prime interval satisfies

\[
 \log X\sum_p b(p)\log p
 \ \le\ \sum_p b(p)\log p\log(p+2)
 \ \le\ \log(2X+2)\sum_p b(p)\log p.
\]

The original weighted upper bounds are O(X/log X).
Thus replacing the extra logarithm by log X costs
O(X/log X)=o(X). Also
(c2(2X+2)/log(2X+2))log X=(1+o(1))CX.
The original square, prime-power and cutoff errors remain
as stated above; multiplying them by at most log(2X+2)
still gives o(X). This justifies using the displayed
coefficients in units of CX for the following leading
budget test.

Here is a joint assignment satisfying the listed leading
inequalities. Every entry is a coefficient of CX, not an
assertion about the actual primes. Split E according to
z<=q<=U, U<q<=W, and W<q<=y, where
U=floor(X^(1/5)), W=floor(X^(21/100)).

| Chen component | Assigned coefficient |
|---|---:|
| Genuine twins | 0 |
| E_low | 2 |
| E_middle | 0 |
| E_high | 4 log 3 - 2 |
| B and A3 | 0 |
| A1, sum A2,q, and E | 4 log 3 |
| Ca, Da, and La | 2 log 3 |

Nonnegativity and every lower/upper constraint in (4)-(7)
hold. In particular log 3<log 6 and Ca>=kappa.
Independently, the divisor-side assignment is

\[
 M_2=2,\quad M_1=M_3=M_4=0,\quad
 M=2,\quad D=8,\quad S_p=S_{\rm bal}=2,\quad
 S_{pp}=D_{\rm mult}=0.
\]

It satisfies 4 log(29/21)<M<4, both complete hyperbola
identities, the balanced cap, and the moment inequalities.
All their genuine-prime lower expressions are zero.

Finally the signed ledger can have

\[
 T_{\rm middle}=0,\quad N_{\rm rough}=2,\quad
 N_{\rm comp}=0,\quad P_{\rm comp}=1,\quad J=1,
\]

with leading residuals zero. Then R=1, T_middle+R=1,
and P_comp-N_comp=H+T_middle-J holds with H=2.
The 0.263 middle-prime upper bound is satisfied.
The full margin is still zero. This assignment only tests
the listed aggregate identities and inequalities; it is
not a construction of primes or of full BV progression data.

A possible new joint estimate can be stated without
confusing the supports. Let Da use the common log-product
weight on the actual Chen support, and let M, Sp and Spp
retain the actual divisor-side support. Put

\[
 h=4\log(29/21),\quad
 D_{\rm Chen}=(\kappa CX-C_a)_+,\quad
 D_{\rm rough}=(hCX-M)_+.
\]

The existing paper estimates imply both nonnegative
deficits are o(X), with the conversion and removal errors
included. Since Ca=Q_tw+Da and
M-Sp-Spp=Q_tw-2M3-6M4<=Q_tw, a cofinal inequality

\[
 D_a+S_p+S_{pp}\le(\kappa+h-\delta)CX+E_{\rm joint},
 \qquad 0\le E_{\rm joint}=o(X),\quad\delta>0,
\]

would give the complete lower budget

\[
 2Q_{\rm tw}\ge\delta CX
          -D_{\rm Chen}-D_{\rm rough}-E_{\rm joint}.
\]

No additional Epp is subtracted here: Q_tw already uses
genuine primes, and the other removals are in the deficits.
The threshold kappa+h is about 1.3758563, whereas the
feasible assignment has Da+Sp+Spp=2 log 3+2, about
4.1972246. No joint upper bound of the required strength
has been obtained. Adding the old estimates does not
supply this new arithmetic input.
