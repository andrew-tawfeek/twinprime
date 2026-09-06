# Extracting shift two from tuple sieves

Checkpoint: 2026-09-05. The certified positive margin in the
[complete signed budget](SIGNED_TOTAL_BUDGET.md) remains zero.
This assessment tests larger tuples, the enlarged two-coordinate
criterion with vanishing marginals, and signed combinations of
weights. It does not repeat the standard M2 optimization already
excluded in [PLAN.md](../PLAN.md).

The enlarged two-coordinate functional below has exact optimum
2, still insufficient for its strict prime-pair criterion.
Larger standard tuples also fail the extraction budget, for a
separate combinatorial reason. These are limits of the specified
criteria, not an impossibility theorem about all sieve methods.

## 1. The precise number of prime coordinates needed

Fix k>=2 and an admissible set H={h_1,...,h_k} of distinct nonnegative
integer offsets. Join two offsets when their difference is 2.
The resulting graph is a matching plus isolated vertices.
Indeed a vertex of degree two would produce h,h+2,h+4,
covering all residues modulo 3 and contradicting admissibility.

Let e be its number of edges. Its independence number is

\[
 \alpha=k-e\ge\lceil k/2\rceil.
\]

For an integer n, put P_i(n)=1_(n+h_i prime), P=sum_i P_i,
and let E count the edges whose two vertices are prime.
Let Z count components with no prime vertex, including isolated
nonprime vertices. The exact Boolean identity is

\[
 \boxed{E=P-\alpha+Z.}                                  \tag{1}
\]

On an edge this is ab=a+b-1+(1-a)(1-b); on an isolate it
is 0=a-1+(1-a). Thus E>=P-alpha. The threshold is sharp:
one occupied vertex per edge and every isolate occupied gives
P=alpha and E=0. At least alpha+1 prime coordinates force
a twin edge. Merely obtaining some two primes in a large
tuple does not.

For any nonnegative weights w_n on N<=n<2N, define

\[
 S_1=\sum_n w_n,\quad S_2=\sum_n w_nP(n),\quad
 {\cal T}_w=\sum_n w_nE(n),\quad {\cal Z}_w=\sum_n w_nZ(n).
\]

Then

\[
 {\cal T}_w=S_2-\alpha S_1+{\cal Z}_w
             \ge S_2-\alpha S_1.                        \tag{2}
\]

The favorable Z term is not an independent gain. Its edge
contribution expands as 1-P_i-P_j+P_i P_j, reintroducing
the very fixed-pair correlation being sought.

## 2. The full standard-tuple lower budget is negative

Use the weights and hypotheses of
[Maynard, Proposition 4.1](https://arxiv.org/pdf/1311.4600).
Let theta be the distribution exponent, choose fixed
0<delta<theta/2, and put R_s=N^(theta/2-delta).
Write B_N for the source's small-prime primorial; it is
unrelated to the signed ledger's power cutoff W. For its
fixed smooth nonzero F on sum t_i<=1, set

\[
 \kappa_s=\theta/2-\delta,\qquad
 A_N=\frac{\varphi(B_N)^kN(\log R_s)^k}{B_N^{k+1}},
 \quad I=\int F^2,\quad
 J_i=\int\left(\int F\,dt_i\right)^2dt_{\ne i}.
\]

With the source's nonzero-integral conditions, its conclusion
has the exact residual notation

\[
 S_1=A_NI+r_1,\quad
 S_2=A_N\kappa_s\sum_iJ_i+r_2,\qquad r_1,r_2=o(A_N).
\]

All tuple, function, primorial and distribution errors are
retained as their actual differences r_1 and r_2. Equation
(2) therefore gives the conservative finite lower budget

\[
 {\cal B}_N
 =A_N\left(\kappa_s\sum_iJ_i-\alpha I\right)
       -|r_2|-\alpha|r_1|,\qquad
 {\cal T}_w\ge{\cal B}_N.                               \tag{3}
\]

Each simplex fiber has length at most 1. Cauchy-Schwarz
gives J_i<=I, so

\[
 \kappa_s\sum_iJ_i-\alpha I
 \le(\kappa_s k-\alpha)I<0                              \tag{4}
\]

for theta<=1 and delta>0. Under the available BV exponents
theta<1/2 it is at most -kI/4. The sharper standard bound
[M_k<=k log k/(k-1)](https://arxiv.org/html/1407.4897),
from Polymath8b Corollary 6.4, also keeps the normalized prime count
strictly below k/2 even in the limiting theta=1 calculation.
No numerical optimization of these weights changes this
fixed-pair extraction threshold.

For clarity, a positive budget would transfer to the
repository's exact target. Suppose e>0, M_N=max_n w_n>0,
and N>=max(H)+2. Set Y=N-1. Every extracted lower prime
lies in (Y,4Y], and has at most e representations, one per
edge. Its genuine logarithmic pair weight is at least
(log N)^2. Consequently

\[
 Q_{\rm tw}(Y)+Q_{\rm tw}(2Y)
 \ge\frac{(\log N)^2}{eM_N}{\cal T}_w
 \ge\frac{(\log N)^2}{eM_N}{\cal B}_N.                   \tag{5}
\]

The two dyadic intervals are disjoint. This avoids dropping
translated endpoints, and no prime-power error is needed:
E already requires two genuine primes. One dyadic sum is at
least half any positive lower bound in (5). Its size must
retain the maximum weight M_N; existence of a positive
weighted term alone does not imply a linear-density bound.

If that half-bound were G_N>0 at a selected scale X equal
to Y or 2Y, the total ledger would give

\[
 T(X)+R(X)\le CX-G_N+
        |J(X)-CX|+D_{\rm cl}(X)+D_\beta(X).
\]

The exact identity additionally subtracts Epp, so dropping
it here only weakens the upper bound. No new favorable
0.263 saving is counted. In the actual calculation (3)
has negative main term and nonpositive error deductions,
so (5) supplies no positive G_N.

## 3. The full two-coordinate marginal criterion has optimum 2

The stronger
[Polymath8b, Theorem 3.14](https://arxiv.org/html/1407.4897)
allows a larger support with signed F and vanishing
marginals. At k=2, fix 0<epsilon<1 and put

\[
 a=1-\varepsilon,\quad b=1+\varepsilon,\quad a+b=2,\qquad
 D=\{(x,y)\ge0:x+y\le2\}.
\]

Its admissible real L2 functions F are supported on D,
with

\[
 \int F(x,y)\,dy=0\ (x>b),\qquad
 \int F(x,y)\,dx=0\ (y>b).
\]

The numerator is

\[
 {\cal J}_a(F)=
   \int_0^a\left(\int_0^\infty F(x,y)\,dx\right)^2dy+
   \int_0^a\left(\int_0^\infty F(x,y)\,dy\right)^2dx.
                                                        \tag{6}
\]

The source would require J_a(F)/I(F)>2/theta to force the
two coordinates prime, under GEH[theta], 0<theta<1.
Here is a direct calculation for exactly this domain and
these marginal constraints:

\[
 \boxed{\sup_{F\ne0}\frac{{\cal J}_a(F)}{\int_DF^2}=2.}  \tag{7}
\]

### Upper bound

Take arbitrary real u,v in L2(0,a), and write
U(t)=integral_0^t u, V(t)=integral_0^t v. The dual
representative for the two low marginals is

\[
 S(x,y)=u(y)1_{y\le a}+v(x)1_{x\le a}\quad ((x,y)\in D).
\]

On the region x>b, only the u term survives. Subtract
its vertical-fiber mean U(2-x)/(2-x). On y>b, similarly
subtract V(2-y)/(2-y). Leave the other points unchanged;
call the resulting function P_S. The two correction
regions are disjoint because b>1. Marginal vanishing gives
inner_product(F,S)=inner_product(F,P_S).

Direct integration of the disjoint corrections gives

\[
 \begin{split}
 \|P_S\|_2^2
 &=\int_0^a(2-t)(u(t)^2+v(t)^2)\,dt+2U(a)V(a)\\
 &\quad-\int_0^a\frac{U(t)^2+V(t)^2}{t}\,dt\\
 &=2(\|u\|_2^2+\|v\|_2^2)-(U(a)-V(a))^2\\
 &\quad-\int_0^a
   \left[\left(\sqrt t\,u(t)-\frac{U(t)}{\sqrt t}\right)^2
        +\left(\sqrt t\,v(t)-\frac{V(t)}{\sqrt t}\right)^2
   \right]dt\\
 &\le2(\|u\|_2^2+\|v\|_2^2).
 \end{split}                                           \tag{8}
\]

There is no missing singular endpoint term:
U(t)^2/t<=integral_0^t u(s)^2 ds makes the displayed
integrals finite, and absolute continuity gives
U(a)^2=2 integral_0^a U(t)u(t) dt. The same holds for V.
Cauchy-Schwarz followed by Hilbert-space duality now gives
sqrt(J_a(F))<=sqrt(2)||F||_2, proving the upper bound.

### Attainment

Let F=2 on [0,a]^2, F=1 on the two rectangles
[0,a] times (a,b] and (a,b] times [0,a], and F=0 elsewhere.
Its support lies in D because a+b=2. All marginals
beyond b vanish. Each low marginal equals 2, so

\[
 I(F)=4a^2+2a(b-a)=4a,\qquad
 {\cal J}_a(F)=8a.
\]

Thus equality in (7) is attained for every 0<epsilon<1.
This is distinct from the standard M2 constant and does
not change its value.

For the enlarged criterion, even the optimal leading
lower-budget coefficient is at most theta-1<0. Its
formal limiting value at theta=1 is zero, while the
criterion still needs strict positivity. Unspecified
remainder terms cannot turn equality into a certified
gain. The smaller epsilon-simplex class of Theorem 3.12
is contained in this class, so it also has ceiling at
most 2 at k=2.

### The omitted marginal tails are a new arithmetic input

For the same attaining F, each full marginal equals a on
(a,b], in addition to its value 2 on [0,a]. Thus the
untruncated numerator would have ratio

\[
 \frac{J_{1,\infty}(F)+J_{2,\infty}(F)}{I(F)}
 =\frac{8a+4\varepsilon a^2}{4a}
 =2+a\varepsilon>2.                                     \tag{9}
\]

Substituting this ratio into the criterion is invalid.
It adds an unevaluated prime-weighted contribution.
For example, epsilon=1/2 would give the formal ratio
9/4, and at theta=9/10 the formal normalized margin
would be 1/80. That number is not a proved lower bound.
One would need an actual bound for the added arithmetic
sum, its approximation error, and the support-regularization
loss before counting any part of it.

The modulus obstruction is concrete. With the theorem's
theta/2 rescaling, the tail reaches remaining-coordinate
divisor supports X^(theta b/2). Products from squaring
these weights can require prime progressions through
X^(theta b), beyond the available exponent theta.
For the displayed example theta b=27/20>1. The cited
GEH hypothesis does not justify that missing prime sum.
A successful switching or cancellation estimate would
be additional arithmetic, not a recovered consequence
of the existing functional evaluation.

This conclusion concerns the stated variational criterion.
In particular, it does not assert an upper bound for the
actual prime mass from the source's truncated-marginal
lower estimate, or promote the informal parity discussion
in that paper's Section 8 into a universal theorem.
The alternative support regions mentioned in its Section 9
are also not automatically covered by (7).

## 4. Signed weights and forced auxiliary composites retain defects

For a real signed weight v, write v_-=max(-v,0). The
exact identity (1) implies

\[
 \sum_n v_nE(n)
 =\sum_n v_n(P(n)-\alpha)+\sum_n v_nZ(n)
 \ge\sum_n v_n(P(n)-\alpha)-\sum_n(v_n)_-Z(n).           \tag{10}
\]

The last sum is a nonnegative missing defect. Taking
v=-1 on a Boolean configuration with no prime vertex
makes the first term alpha>0 while E=0; the defect is
exactly alpha. This is a finite algebraic counterexample
to discarding the defect, not a prime-distribution model.

Polarization, AB=((A+B)^2-(A-B)^2)/4, computes a difference
of quadratic sums but does not bound that defect.
Positive semidefinite combinations within the same
standard admissible weight family remain sums of squares
and retain (4). An indefinite combination needs the
additional signed-error estimate in (10).

Likewise, forcing auxiliary coordinates composite by
congruences changes the arithmetic input. Choose a
distinct fixed prime for each auxiliary offset, larger
than every offset difference, and impose divisibility of
that coordinate by its chosen prime. The Chinese remainder
theorem preserves coprimality of the target two coordinates
with these primes, but makes all auxiliary forms composite
for large n. Their individual prime-count contributions
are then zero. The transformed auxiliary linear forms
have a fixed prime divisor, so the original admissible
tuple theorem cannot still be applied to them. Discarding
them leaves a two-form problem; the former large-tuple
prime-count main term cannot be retained.

## 5. Qualitative tuple abundance alone does not select shift two

The set A={n>0:n=1 mod 4} has no pair at difference 2.
Every admissible k-tuple has a single parity, hence at
most two residue classes modulo 4. One class contains
at least ceil(k/2) offsets, and infinitely many translates
place that whole class in A. Thus even that simultaneous
family of qualitative tuple guarantees does not force
the desired edge.

There is also a version using actual primes. Let
A_P={p prime:p=1 mod 4}. It has no difference 2, but,
for every m>=2, every sufficiently large admissible tuple
has infinitely many translates with at least m members
of A_P. To see this, take the threshold k_m in
[Banks–Freiberg–Turnage-Buterbaugh, Theorem 1](https://arxiv.org/pdf/1311.7003).
For k>=2k_m-1, a largest modulo-4 subclass contains
k_m offsets. Shift them to constants 1 mod 4 and use
that theorem with leading coefficient g=4. The resulting
linear forms are admissible: at 2 they are odd, and at
odd primes multiplication by 4 is invertible and the
original admissibility excludes a common covering.

This does not assert ceil(k/2) actual primes, or that
A_P has the full distribution data of all primes.
It isolates the gap between unspecified prime clusters
and a prescribed pair, even when cluster elements are
genuine primes.

## 6. Complete-budget decision

The standard large-tuple test has the explicit negative
budget (3). The full k=2 marginal criterion has exact
optimum 2 and fails its strict threshold. Signed weights
retain (10)'s defect, and CRT conditioning removes the
auxiliary prime mass it would otherwise have used.

None supplies a positive Q_tw lower bound, hence none
improves the certified coefficient of T+R below one.
No further numerical search or substantial Lean
formalization of these insufficient criteria is justified
by this checkpoint. An additional pair-sensitive estimate,
with its full defect budget, is still required.
