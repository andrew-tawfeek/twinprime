# Distribution and additive Fourier tests of the total budget

Checkpoint: 2026-09-05. This is a paper assessment, not a new Lean
endpoint. The [total signed budget](SIGNED_TOTAL_BUDGET.md) remains
Q_tw>=0.737 C X-R-E_tot, with E_tot=o(X). The certified positive margin
is zero. The tests below must improve R or the complete loss T+R; a
smaller upper bound for T alone does not meet that requirement.

## 1. Exact additive budget, including its relation to the signed loss

Use e(t)=exp(2 pi i t) and the exact integer supports

\[
 A_X(\alpha)=\sum_{X<n\le2X}\Lambda(n)e(n\alpha),\qquad
 B_X(\alpha)=\sum_{X+2<m\le2X+2}\Lambda(m)e(m\alpha).
\]

Orthogonality gives W2=int A_X conjugate(B_X) e(2 alpha). The positive
phase selects m=n+2. No endpoint term is suppressed. Given a major-arc
set M and its complement m, define

\[
 M_X=\Re\int_{\mathfrak M} A_X\overline{B_X}e(2\alpha),\quad
 N_X=\Re\int_{\mathfrak m} A_X\overline{B_X}e(2\alpha),\quad
 D_{\rm maj}=|M_X-CX|.
\]

Then the exact and lower-bound budgets are

\[
 Q_{\rm tw}=M_X+N_X-E_{\rm pp}
 \ge CX+N_X-D_{\rm maj}-E_{\rm pp}.                 \tag{1}
\]

Thus N_X>=-(1-delta) C X on cofinally many scales, for fixed delta>0,
would suffice once D_maj+Epp=o(X). Requiring N_X=o(X) would be stronger
than necessary. From the existing exact classical identity,

\[
 T+R=J-CX-N_X+(CX-M_X)+r_{\rm cl}+r_\beta.          \tag{2}
\]

The proposed one-sided bound would therefore give

\[
 T+R\le(1-\delta)CX+
 |J-CX|+D_{\rm maj}+D_{\rm cl}+D_\beta.             \tag{3}
\]

This would improve the *complete* leading loss by delta. It need not
pass through the separate 0.263 bound; no extra 0.263 saving is required
from a method that directly controls T+R. All residuals in (1) and (3)
are displayed. No such bound for N_X has been obtained here.

## 2. Major arcs: the main mass and every approximation term

Fix a sufficiently large constant B and put P=(log X)^B. Take the arcs
alpha=a/q+beta modulo one, q<=P, (a,q)=1, |beta|<=P/X. They are disjoint
for large X and their total measure is O(P^3/X). Define

\[
 I_X(\beta)=\int_X^{2X}e(\beta t)\,dt,\qquad
 C_P=\sum_{q\le P}\frac{\mu(q)^2c_q(2)}{\varphi(q)^2},\qquad
 A_P=\sum_{q\le P}\frac{\mu(q)^2|c_q(2)|}{\varphi(q)^2}.
\]

Here c_q is the Ramanujan sum. For squarefree q, |c_q(2)|=1, so A_P is
bounded uniformly. The absolutely convergent Euler product gives
C_P->C: the factor at two is 2, and at each odd p it is
1-1/(p-1)^2.

Let eta_X and eta'_X be the actual maximum errors, respectively, in

\[
 A_X(a/q+\beta)=\frac{\mu(q)}{\varphi(q)}I_X(\beta)
                    +\text{error},\qquad
 B_X(a/q+\beta)=\frac{\mu(q)}{\varphi(q)}e(2\beta)I_X(\beta)
                    +\text{error}.
\]

The second integral has exactly translated endpoints. Hence its e(2 beta)
factor cancels the beta part of the selecting phase; summing a produces
c_q(2). Since |I_X|<=X, the full major-arc budget is

\[
 D_{\rm maj}\le |\mathfrak M|
       [X(\eta_X+\eta'_X)+\eta_X\eta'_X]
       +X|C-C_P|+\frac{2XA_P}{\pi^2P}.              \tag{4}
\]

The last term retains the truncated singular-integral tail:
int_R |I_X|^2=X and |I_X(beta)|<=1/(pi |beta|) away from zero.
The actual centered Siegel-Walfisz estimate, summation over reduced
residues, and partial summation give eta_X+eta'_X=O_K(X/log^K X)
for every fixed K after B is fixed. The noncoprime prime powers and
both sharp endpoints are included in those errors. Choose K>3B+1;
then (4) is o(X). This is a paper application of existing distribution,
not an additional assumption about prime pairs.

For comparison with the classical source, the major arcs and main-term
calculation are given in Section 4, particularly Proposition 4.1, of
[Matomäki–Radziwiłł–Tao, *Correlations of the von Mangoldt and higher divisor functions I*, version 3](https://arxiv.org/pdf/1707.01315).
The finite budgets (1)–(4) above use the repository's shifted dyadic
supports explicitly.

## 3. Why magnitude control and diagonal subtraction do not suffice

Put E_X=sum_(X<n<=2X) Lambda(n)^2 and define E'_X with the shifted
support of B_X. Parseval and Cauchy-Schwarz give only

\[
 |N_X|\le
 \left(\int_{\mathfrak m}|A_X|^2\right)^{1/2}
 \left(\int_{\mathfrak m}|B_X|^2\right)^{1/2}
 \le\sqrt{E_XE'_X}.                                  \tag{5}
\]

Both energies are X log X+(2 log 2-1)X+o(X). Indeed the prime contribution
sum log^2 p has this asymptotic by the repository's quantitative prime
number theorem and partial
summation; the proper-prime-power contribution is
O(sqrt(X) log^3 X). Moving the interval by two changes at most four
terms, each bounded by log^2(2X+2). Thus the normalized loss in (5) is
(1+o(1)) log X/C, which exceeds the whole available leading budget.
This is a limitation of that bound, not a lower bound for |N_X|.

There is also an exact way to inspect the proposed diagonal removal.
For X>=2 put

\[
 F_X=|A_X|^2,\qquad G_X=F_X-E_X,\qquad
 b_X=\Lambda(2X-1)\Lambda(2X+1)+\Lambda(2X)\Lambda(2X+2).
\]

Then 0<=b_X<=2 log^2(2X+2), and

\[
 W2=\int_0^1F_Xe(2\alpha)\,d\alpha+b_X
    =\int_0^1G_Xe(2\alpha)\,d\alpha+b_X.             \tag{6}
\]

Subtracting the diagonal leaves the selected coefficient unchanged.
On the minor arcs it changes the integral by
E_X int_M e(2 alpha), of absolute size at most
E_X |M|=O(P^3 log X)=o(X). But the available triangle inequality gives
int_m |G_X|<=2E_X. An estimate for the centered oscillation has not been
supplied by this algebraic subtraction. The exact endpoint term b_X
and the arc-local constant term cannot be silently deleted.

The signed minor coefficient required by (1), rather than a smaller
global energy norm or a new representation of it, is the missing input.

To connect the centered calculation to N_X explicitly, B_X-A_X has
four endpoint terms. Its L2 norm is at most 2 log(2X+2). On any
measurable arc set A, Cauchy-Schwarz therefore gives

\[
 \left|\int_A A_X\overline{B_X}e(2\alpha)
             -\int_A F_Xe(2\alpha)\right|
 \le2\log(2X+2)\sqrt{E_X}=o(X).                      \tag{7}
\]

There is a further quantitative obstruction to using a *global* L2
bound after centering. Write r_X(h)=sum_n a_n a_(n+h), with
a_n=1_(X<n<=2X)Lambda(n), extended by zero. Fourier Parseval gives

\[
 \|G_X\|_2^2=\sum_{h\ne0}r_X(h)^2
 \ge\frac{[(\sum_n a_n)^2-E_X]^2}{2(X-1)}
   =(1/2+o(1))X^3.                                  \tag{8}
\]

The denominator counts the possible nonzero differences. This global
norm is too large for an error of order X. Equation (8) does not assert
the same lower bound on the minor arcs, and does not rule out a new
estimate using their signed coefficient.

## 4. Averaging over shifts cannot certify the specified shift

Write W_h(X)=sum_(X<n<=2X) Lambda(n)Lambda(n+h). The inspected
averaged-correlation theorem gives, for fixed A>0 and 0<epsilon<1/2,
W_h=S(h)X+O(X/log^A X) except at O(H/log^A X) shifts in a window of
radius H, where X^(8/33+epsilon)<=H<=X^(1-epsilon). The window may be
centered at 2: its condition 0<=h_0<=X^(1-epsilon) then holds eventually.
These are the actual quantifiers of
[Theorem 1.3(i)](https://arxiv.org/pdf/1707.01315); they do not identify
which shifts are exceptional.

For every fixed A, H/log^A X tends to infinity in that range. The
following error array is consequently compatible with the stated
exceptional-set conclusion for every A simultaneously:

\[
 e_X(h)=-CX\,1_{h=2},\qquad
 \widetilde W_h(X)=\mathfrak S(h)X+e_X(h)\quad(h\ne0).
                                                               \tag{9}
\]

There is just one exceptional nonzero shift. The diagonal h=0 can be
retained as a separate exception. All other errors vanish, and
the model value at shift 2 is zero because S(2)=C. On positive shifts
up to H its average absolute and squared errors are exactly

\[
 \frac1H\sum_{h=1}^H|e_X(h)|=\frac{CX}{H},\qquad
 \frac1H\sum_{h=1}^H|e_X(h)|^2=\frac{C^2X^2}{H}.      \tag{10}
\]

These even satisfy every fixed logarithmic saving of the corresponding
averaged scale, while losing the entire main term at shift 2 at every X.
The array is a counterexample to the inference from the stated aggregate
bounds alone. It is not a model of the actual primes, a construction
preserving their progression data, or a disproof of a fixed-shift estimate.

Further averaging over X does not repair this inference: the same
exceptional shift occurs at each scale in (9). Choosing A as a function
of X is not authorized by a theorem stated for each fixed A; its
constants and thresholds depend on A.

More quantitatively, an absolute first-moment error bound
sum_h |e_X(h)|<=X H epsilon_X yields only |e_X(2)|<=X H epsilon_X.
A second-moment bound sum_h |e_X(h)|^2<=X^2 H epsilon_X^2 yields
|e_X(2)|<=X sqrt(H) epsilon_X. To force o(X) using these inequalities
alone requires H epsilon_X=o(1) or sqrt(H) epsilon_X=o(1), respectively.
Arbitrarily large *fixed* logarithmic savings do not meet either
requirement when H is a fixed positive power of X.

Thus no gain in the coefficient of T+R follows from the inspected
shift averages. A useful new theorem would have to rule out shift 2
as a persistent exception, or supply its signed coefficient directly.

## 5. A positive Fourier density with the critical cancellation

The following explicit comparison sharpens the global-norm test. It
retains a positive major-arc coefficient, the diagonal size, nonnegative
Fourier coefficients, and upper bounds of order X at nearby shifts,
while its shift-two coefficient is exactly zero.

Let X be divisible by six, M=X/2, 1<=c<=2, t=4-2c, rho=6-2c, and
w=1-2/X. Use the normalized Fejer kernel

\[
 K_M(\alpha)=\frac1M\left|\sum_{j=0}^{M-1}e(j\alpha)\right|^2
 =\sum_{|j|<M}(1-|j|/M)e(j\alpha).
\]

Take any D=X log X+O(X); it can be the actual E_X. Put

\[
 \begin{split}
 H_X(\alpha)&=X\left[2K_M(2\alpha)+\frac t2
     (K_M(2\alpha-1/3)+K_M(2\alpha+1/3))\right],\\
 f_X(\alpha)&=D-\rho X+H_X(\alpha)
                     -2c(X-2)\cos(4\pi\alpha).
 \end{split}                                                    \tag{11}
\]

Since H_X>=0 and rho+2c=6, f_X>=D-6X+4c>0 eventually.
Its mean is D. At shift h=2j with 0<|h|<X, the coefficient of H_X is

\[
 (X-|h|)[2+t\cos(2\pi j/3)]
 =\begin{cases}
   \rho(X-|h|),&3\mid j,\\
   c(X-|h|),&3\nmid j.
  \end{cases}
\]

The final cosine in (11) cancels precisely the coefficients at h=2
and h=-2. All remaining coefficients are nonnegative; the odd ones
vanish, and the nonzero even ones are at most 4c(X-|h|), because
rho<=4c. Beyond this support they are zero. Also
f_X(0)=X^2+D-6X+4c, so the value at zero has the expected leading
size X^2 of |A_X(0)|^2.

All kernel centers of H_X lie at rationals with denominator at most six.
The Fejer tail outside distance P/X of those centers has total mass
O(X/P). On the major arcs the flat and cosine terms contribute at most
(D+O(X)) times the major-arc measure, which is O(P^3 log X). Consequently

\[
 \Re\int_{\mathfrak M}f_Xe(2\alpha)
      =c(X-2)+O(X/P+P^3\log X)=cX+o(X),\qquad
 \Re\int_{\mathfrak m}f_Xe(2\alpha)=-cX+o(X).        \tag{12}
\]

One may choose c=C: indeed 1<C<2. An elementary lower bound follows
by comparing the Euler product with the product over all odd integers:
sum_(k>=1)1/(2k)^2<1/2 and the product of (1-a_k) is at least
1-sum a_k. The upper bound follows from the nontrivial factor at three.
Thus (12) matches the required major-arc leading constant and still
allows its complete cancellation. All positivity inequalities obtained
by integrating f_X against a nonnegative kernel hold automatically.

This is a comparison Fourier density, not |A_X|^2 for actual Mangoldt
coefficients. It does not preserve the full rational-arc profiles from
Siegel-Walfisz, the individual shifted-prime asymptotics, or all the
arithmetic data in the repository. It rules out a positive conclusion
from the listed aggregate positivity, energy, major-total, and nearby
upper bounds alone. It is not an impossibility theorem for the circle
method or for a method that uses additional prime structure.

## 6. Stronger one-variable distribution: a separate budget test

This section is a conditional diagnostic. No Elliott-Halberstam input
is proved or assumed in the repository. Let Y=2X+2, z=sqrt(Y), and
sieve a(n)=1_(X<n<=2X)Lambda(n+2) by all odd primes below z. Call its
mass S_z. Every surviving odd n is prime, because a composite n<=2X
has a prime factor at most sqrt(2X)<z. Conversely all primes n in the
interval survive for large X. Extra even survivors have n+2 a power
of two, with total mass e_2<=log Y. Therefore

\[
 Q_{\rm tw}\ge \log X\,S_z-\log X\,e_2-E_{\rm pp}. \tag{13}
\]

For an odd squarefree d, the exact sequence remainder is

\[
 r_X(d)=\psi(Y;d,2)-\psi(X+2;d,2)-X/\varphi(d),\qquad
 |r_X(d)|\le2E_d(Y).
\]

Suppose hypothetically that a level D=floor(X^theta) satisfies
log X sum_(d<=D, d odd squarefree) E_d(Y)=o(X). Write
V(z)=prod_(2<p<z)(1-1/(p-1)) and let f be the standard lower
linear-sieve function. For 1/2<theta<=1, fix 1<s_0<2theta and use
the sublevel D_0=z^(s_0), which is at most D for all large X. This
keeps the sieve parameter fixed as required by the cited theorem.
For fixed approximation epsilon>0, the candidate leading coefficient is

\[
 L(s_0)=2e^{-\gamma}f(s_0),\qquad
 Q_{\rm tw}\ge C L(s_0)X-\mathcal E_{\theta,s_0,\varepsilon}(X),
                                                               \tag{14}
\]

with the following nonnegative residual budget, for some fixed
coefficient bound J_epsilon:

\[
 \begin{split}
 \mathcal E_{\theta,s_0,\varepsilon}(X)={}&
 X f(s_0)|\log X\,V(z)-2Ce^{-\gamma}|
 +\varepsilon X\log X\,V(z)\\
 &+2J_\varepsilon\log X
       \sum_{\substack{d\le D\\d\ \text{odd and squarefree}}}E_d(Y)
 +\log X\log Y+E_{\rm pp}.
 \end{split}                                                    \tag{15}
\]

The product limit is log X V(z)->2C exp(-gamma), and the distribution,
even-input and prime-power terms are o(X).
Fix epsilon first, take the limit, and then let epsilon decrease to zero.
The normalization and the fact f(s)=0 for s<=2 are from
[Tao, linear-sieve Theorem 2 and equations (10)–(11)](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/).
Every allowed s_0 has f(s_0)=0. The limiting coefficient as s_0
increases to 2theta is likewise L_theta=2 exp(-gamma) f(2theta)=0
throughout 1/2<theta<=1. For theta<=1/2
the cited positive-s theorem is not applicable at this threshold;
ordinary nonnegativity already supplies the same zero lower budget.

Ordinary EH would supply each fixed theta<1, not the endpoint D=X
without an additional uniformity assertion. Taking theta up to one
still gives f(2)=0. Even granting the hypothetical endpoint input
does not create a positive leading coefficient in this application.

Stronger distribution can reduce the middle-prime upper bound without
altering that conclusion. To preserve its support when theta grows,
choose z_q=(1/2)min(q,sqrt(D/q)). Then z_q<q, q does not divide a
sieve modulus d, and q is the unique largest prime in qd. With
u=1/5, v=21/100, and alpha(t)=min(t,(theta-t)/2), the corresponding
paper upper coefficient is

\[
 K_\theta(v)=e^{-\gamma}\int_u^v
   \frac{1-t}{t\alpha(t)}
       F\left(\frac{\theta-t}{\alpha(t)}\right)dt.   \tag{16}
\]

For clarity, define the finite main sums over the actual primes U<q<=W,
with s_q=log(D/q)/log z_q,

\[
 M_\theta(X)=\sum_q\frac{\log(2X/q)}{\varphi(q)}V(z_q)F(s_q),\qquad
 H_\theta(X)=\sum_q\frac{\log(2X/q)}{\varphi(q)}V(z_q) .
\]

The complete finite upper bound is T<=C K_theta(v) X+E_T, where

\[
 E_T=X|M_\theta(X)-C K_\theta(v)|+\varepsilon X H_\theta(X)
   +2J_{\theta,\varepsilon}\log(2X)
      \sum_{\substack{m\le D\\m\ \text{odd and squarefree}}}E_m(Y).
                                                               \tag{17}
\]

The support qd is odd and squarefree, so the stated hypothetical
distribution controls precisely this last sum. The first term keeps
the actual outer floors, log 2, D rounding, product and prime-summation
errors. Uniformly in the active q, log z_q/log X tends to alpha(t)
and s_q tends to (theta-t)/alpha(t). Uniform product asymptotics and
the reciprocal-prime summation then give M_theta->C K_theta and
H_theta=O(1). The bound beta'_W(b)<=log b introduces no additional
replacement error. Thus E_T=o(X)+O(epsilon X), with epsilon fixed
until after the limit.

The sieve application must also be uniform over q. This follows from
the compact-uniform formulation, or a finite mesh of fixed sieve
parameters: the active s_q stay in a fixed compact subset of (1,infinity),
the minimum z_q tends to infinity, and F is uniformly continuous there.
For a mesh point below s_q use level z_q^(s_mesh)<=D/q; the resulting
approximation loss is included in epsilon H_theta. The finite mesh
gives one common threshold and coefficient bound J_(theta,epsilon).
Allocate epsilon/2 to the sieve approximation and epsilon/2 to the
mesh comparison, so their combined loss is the one displayed in (17).

For 1/2<=theta<=4/5 the *limiting* sieve parameter is between two and
three. The finite parameter can exceed three by O(1/log X) at the
upper endpoint; continuity of F is used before substituting its
limiting expression. Thus (16) reduces to

\[
K_\theta(v)=\frac2\theta\log\frac vu+
       \frac{2(1-\theta)}\theta\log\frac{\theta-u}{\theta-v}.
\]

The upper-sieve support and bounded-error formulation used here is the
one in [Lichtman, Theorem 2.10 and equations (2.3)–(2.5), version 2](https://arxiv.org/html/2109.02851v2#S2.SS2).

For hypothetical theta=3/5 and 4/5 this is approximately 0.196391
and 0.130379, respectively. For theta>4/5 the F(s) correction above
s=3 must be retained; substituting the same elementary formula at
theta=1 is not justified. These conditional class improvements
supply no companion bound for R and hence no total saving.

The precise obstruction is the zero prime-isolating lower-sieve
coefficient, not merely the current size of the progression remainder.
This conclusion concerns this stated linear-sieve application. It does
not assert that every possible use of EH, GEH, or stronger arithmetic
information has been excluded. Both tests in this note leave the best
certified complete loss at T+R<=CX+o(X), with zero positive margin.
