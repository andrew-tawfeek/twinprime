# Gowers uniformity and the fixed-shift budget

Checkpoint: 2026-09-05. This paper tests a different mechanism
from tuple sieves: quantitative Gowers uniformity of the primes.
It supplies no positive margin in the
[complete signed budget](SIGNED_TOTAL_BUDGET.md). The norm-to-pair
transfer has a polynomial loss, and a sparse comparison construction
shows why small finite-order norms do not remove it.
No new Lean endpoint is claimed.

## 1. The available theorem does not count this pair

[Leng, Theorem 7, version 5](https://arxiv.org/html/2312.10772v5)
gives, for each fixed k>=2 and some c_k>0, the effective estimate

\[
 \|\Lambda-\nu_N\|_{U^k[N]}
       \ll_k\exp(-(\log N)^{c_k}).                       \tag{1}
\]

Here Q=exp((log N)^(1/10)), P(Q)=product_(p<Q)p, and
nu_N is the source's Siegel model:

\[
 \Lambda_Q(n)=\frac{P(Q)}{\varphi(P(Q))}
                         1_{(n,P(Q))=1},\qquad
 \nu_N(n)=\Lambda_Q(n)(1-n^{\beta-1}\chi(n))
\]

when its exceptional zero is present, and nu_N=Lambda_Q
otherwise. The subexponential estimate is for this corrected
model. Dropping the correction is not part of (1).

The same source's Theorem 5 counts affine patterns only when
their linear coefficient vectors are pairwise independent.
For n and n+2 both vectors are (1). The distinct constants
do not satisfy the hypothesis. Enlarging the Gowers order
does not repair this failure.

The interval convention used here is the normalized average
over all integer cubes contained in [1,N], as in
[Tao–Teräväinen, Definition 1.1](https://content.ems.press/assets/public/full-texts/serials/jems/27/4/13625437/online/10.4171-jems-1404.pdf).
That paper supplies an older quantitative bound; the faster
rate in (1) is the one tested below.

Adding an independent variable also leaves a missing estimate.
The forms n,m can be independent, but restricting their count
to m=n+2 selects only O(N) points from an O(N^2) region.
The ambient O_A(N^2/log^A N) error does not resolve that line.
A statement averaged over shifts likewise needs a separate
fixed-shift bound.

## 2. Exact model replacement, padding and every error

Write C=2C2>0 as in the total ledger. Let Y=2X+2, and
use the single model nu=nu_Y throughout.
Choose a prime p with 2Y<p<4Y, and regard [1,Y] as part
of G=Z/pZ. Put J_X=(X,2X] and define by zero extension

\[
 a=1_{J_X}\Lambda,\quad b=1_{J_X+2}\Lambda,\quad
 c=1_{J_X}\nu,\quad d=1_{J_X+2}\nu,\quad
 f=a-c,\quad g=b-d.
\]

For complex functions write

\[
 C_2(u,v)=\mathbb E_{x\in G}u(x)\overline{v(x+2)},\qquad
 \widehat u(r)=p^{-1}\sum_xu(x)e(-rx/p).
\]

Fourier ell^r norms use counting measure; physical L2 norms
use the normalized mean, ||u||_2=(E_G|u|^2)^(1/2).
The functions in the actual replacement are real. Define

\[
 M=p\Re C_2(c,d),\quad
 H=p\Re\bigl(C_2(f,d)+C_2(c,g)\bigr),\quad
 K=p\Re C_2(f,g).
\]

Q_tw is the sum of log(n)log(n+2) over genuine twin pairs
with X<n<=2X. Epp is the nonnegative proper-prime-power
defect in [the exact correlation identity](../TwinPrime/Correlation.lean).
Then the finite genuine-prime identity is

\[
 \boxed{Q_{\rm tw}=M+H+K-E_{\rm pp}.}                   \tag{2}
\]

The supports match exactly and p>2Y prevents wrapping.
No endpoint term or model correction is suppressed.
Set D_model=|M-CX| and D_mixed=|H|; these are actual
nonnegative finite quantities, not asserted o(X) here.

Normalized Fourier orthogonality and Hölder give

\[
 C_2(u,v)=\sum_r\widehat u(r)\overline{\widehat v(r)}
                           e(-2r/p),\qquad
 \|u\|_{U^2(G)}^4=\sum_r|\widehat u(r)|^4,
\]

and therefore

\[
 |C_2(u,v)|\le\sqrt p\,\|u\|_{U^2(G)}\|v\|_{U^2(G)}.
                                                        \tag{3}
\]

In particular the complete norm-based lower budget is

\[
 Q_{\rm tw}\ge CX-D_{\rm model}-D_{\rm mixed}
          -p^{3/2}\|f\|_{U^2(G)}\|g\|_{U^2(G)}-E_{\rm pp}.
                                                        \tag{4}
\]

The mixed terms also need control. A precise bound retaining
the model's Fourier data is

\[
 D_{\rm mixed}\le p\bigl(
   \|f\|_{U^2}\|\widehat d\|_{\ell^{4/3}}
  +\|g\|_{U^2}\|\widehat c\|_{\ell^{4/3}}\bigr).
\]

The generic further estimate
||d_hat||_(4/3)<=p^(1/4)||d||_2 has another polynomial
loss. No favorable model spectrum is assumed without proof.

The interval-to-group step in (1) is explicit at order 2.
For F supported on [1,Y], zero-padding into p>2Y gives

\[
 \|F\|_{U^2(G)}
 =\left(\frac{Y(2Y^2+1)}{3p^3}\right)^{1/4}
       \|F\|_{U^2[Y]}.                                 \tag{5}
\]

The numerator Y(2Y^2+1)/3 counts the additive quadruples
of the interval; equality modulo p is equality over the
integers in this range. Restricting to either dyadic mask
costs at most 2+log p:

\[
 \|F1_J\|_{U^2(G)}
 \le\|\widehat{1_J}\|_{\ell^1}\|F\|_{U^2(G)}
 \le(2+\log p)\|F\|_{U^2(G)}.                           \tag{6}
\]

The first inequality is Young's convolution inequality.
For nonzero r, the geometric-sum estimate
|widehat(1_J)(r)|<=1/(2 min(r,p-r)) proves the second.

Thus (1) does transfer to f and g, with its padding
factor and a logarithmic loss. Nevertheless p is comparable
to X, and the normalized error from (3) is proportional
to sqrt(p) times the product of the two norm bounds.
Even granting D_model+D_mixed+Epp=o(X), equal norm
bounds would need o(p^(-1/4)) to give an o(X) error
through (4). A sufficiently small constant at that
power scale would suffice for a fixed positive margin.
Every fixed logarithmic saving, or a bound
exp(-c(log p)^gamma) with fixed 0<gamma<1, is too weak
for this calculation.

This is a limitation of the norm-based bound, not a
lower bound for the actual error K. The polynomial
loss in (3) is real: for p>5, q(x)=e(x^2/p) and
u=(q+q(.+2))/2 satisfy

\[
 |u|\le1,\qquad C_2(u,u)=1/4,\qquad
 \|u\|_{U^2}^4=3/(8p).
\]

These identities follow from the quadratic Gauss sum
and the orthogonality of nonconstant linear phases.
They rule out a general logarithmic replacement for
the sqrt(p) loss, even for bounded inputs.

## 3. A sparse nonnegative sequence with zero shift-two mass

Here is a stronger comparison, with height and support
size comparable to a prime-density weight. Fix a positive
integer S and a prime N>=11. On Z/NZ take independent
Bernoulli variables B_n with success probability
rho=1/log N. Put

\[
 A_n=B_n(1-B_{n-2})(1-B_{n+2}),\quad
 \delta=\rho(1-\rho)^2,\quad f_n=A_n/\delta-1.
                                                        \tag{7}
\]

Then A_n A_(n+2)=0 identically, including cyclic
boundaries. At each site the probabilistic mean of f_n
is zero, and |f_n|<=delta^(-1).

For order s, a cube has 2^s vertices. The Bernoulli
neighborhoods of two distinct vertices overlap only
when their difference is one of 0,+2,-2,+4,-4.
For a uniform cube, each such difference is uniform
modulo N: the corresponding linear expression has a
coefficient 1 or -1. Consequently, with

\[
 B_s=5\binom{2^s}{2},
\]

the proportion of cubes with any overlapping
neighborhoods is at most B_s/N. On every other cube,
the centered factors are independent, so the
probabilistic expectation of their product is zero.
Therefore

\[
 0\le\mathbb E_B\|f\|_{U^s(G)}^{2^s}
       \le\frac{B_s}{N\delta^{2^s}}.                    \tag{8}
\]

Nonnegativity needed here is not inferred from the
individual signed products. It follows from the
standard exact square representation

\[
 \|f\|_{U^s}^{2^s}
 =\mathbb E_{h_1,\ldots,h_{s-1}}
   \left|\mathbb E_x
      \Delta_{h_1}\cdots\Delta_{h_{s-1}}f(x)\right|^2.
\]

For s=1 this is the squared mean. Markov's inequality
and a union bound give probability at least 1/2 that
simultaneously, for 1<=s<=S,

\[
 \|f\|_{U^s}\le
 \eta_s:=\frac{(2SB_s/N)^{1/2^s}}{\delta}.               \tag{9}
\]

Choose any such realization. With
alpha=E_G A/delta, one has |alpha-1|<=eta_1=o(1).
For sufficiently large N, alpha>0, so define

\[
 w=\frac{A}{\delta\alpha},\qquad z=w-1.
\]

These are exact finite identities:

\[
 w\ge0,\quad\mathbb E_Gw=1,\quad
 w(n)w(n+2)=0,\quad
 \mathbb E_Gz(n)z(n+2)=-1.                             \tag{10}
\]

Moreover

\[
 \|z\|_{U^s}\le\frac{\eta_s+\eta_1}{\alpha}
       \ll_S(\log N)N^{-1/2^s}\quad(1\le s\le S).
                                                        \tag{11}
\]

The nonzero values of w are O(log N), and its support
has size delta alpha N~N/log N. For every fixed finite
list of Gowers orders, these norm bounds eventually
beat every fixed logarithmic saving and every
exp(-c(log N)^gamma) with 0<gamma<1.

Relative to the constant model 1, the model pair mass
is N, both mixed sums vanish, and the residual pair
sum is exactly -N. Thus the complete main mass is
cancelled despite positivity, exact mean, sparse
support, and the small finite-order norms.

This construction is not a model of actual Mangoldt
values, Cramér local factors, all BV progression data,
or additional majorant hypotheses. It disproves the
inference from the listed norm and density information
alone. No contradiction with a prime-pattern theorem
is claimed.

## 4. Interval version and its endpoint residual

The same argument works with the source's interval
norm convention. Take independent B_n for
-1<=n<=N+2, and use (7) on 1<=n<=N. For N>=16s the
number of valid integer s-cubes is at least

\[
 \frac{N^{s+1}}{8(8s)^s}:
\]

choose x between N/4 and N/2 and each increment between
0 and N/(4s). For a bad pair of vertices, the collision
equation fixes one increment with coefficient 1 or -1.
There are at most N(3N)^(s-1) choices for the other
variables per equation. Thus its bad-cube proportion
is at most B'_s/N, where

\[
 B'_s=8(8s)^s3^{s-1}B_s.
\]

Replace B_s by B'_s in (8)-(9). Normalized interval
Gowers moments are nonnegative, as follows by zero
extension into a sufficiently large cyclic group and
division by the positive indicator moment. Markov,
mean normalization, and (11) follow with constants
depending on S. No cyclic/interval equivalence is
being assumed without this separate count.

All interior products w_n w_(n+2), 1<=n<=N-2, vanish.
Since sum_(n=1)^N w_n=N, the centered correlation is

\[
 \frac1{N-2}\sum_{n=1}^{N-2}z_nz_{n+2}
 =-1+\frac{w_1+w_2+w_{N-1}+w_N-4}{N-2}
 =-1+O_S(\log N/N).                                   \tag{12}
\]

The four boundary weights are retained explicitly.
This shows that the obstruction persists for the
interval convention and is not a wrapping artifact.

## 5. What would improve the actual signed sum

Return to the actual M,H,K in (2). One sufficient
new arithmetic estimate is

\[
 H+K\ge-(1-\delta_0)CX
\]

cofinally for some fixed delta_0>0, together with
D_model+Epp=o(X). More generally the actual finite
criterion is M+H+K>Epp, on unbounded scales.
Neither follows from (1).

If the stronger displayed estimate and residual bound
were proved, the full signed-loss transfer would be

\[
 T+R\le(1-\delta_0)CX+
       |J-CX|+D_{\rm model}+D_{\rm cl}+D_\beta.
\]

Here J is the same classical center as in the total
ledger, not the interval J_X. Epp remains in the
genuine-prime bound (2) and cancels in this W2-based
loss transfer. The middle-prime bound is not counted
again.

The tested norm estimates give no such gain. The
comparison sequence shows why a sharper norm-only
argument cannot simply remove the need for fixed-shift
arithmetic. The certified positive total margin
remains zero, and no substantial formalization of
this insufficient transfer is justified.
