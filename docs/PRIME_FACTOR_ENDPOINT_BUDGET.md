# The largest-prime-factor endpoint and the signed budget

Checkpoint: 2026-09-05. This assessment tests whether prime-factor
distribution can provide the missing fixed-shift gain in the
[total budget](SIGNED_TOTAL_BUDGET.md). It gives an exact cofactor
decomposition and disproves a uniform microscopic extension of
the continuous limiting law. It gives no positive twin-prime
estimate and justifies no new Lean endpoint.

## 1. The source and the scale it controls

[Bharadwaj–Rodgers, version 4, Proposition 2 and Lemma 8](https://arxiv.org/html/2402.11884v4#S1.SS3)
give shifted-prime factor correlations against fixed continuous
tests whose positive logarithmic coordinates sum to less than
the distribution exponent. The unconditional shifted-prime
input has exponent 1/2. Theorem 7 gives full Poisson–Dirichlet
weak convergence under level 1; this is conditional for shifted
primes. Theorem 11 is an upper bound at fixed parameters.
None supplies a shrinking-window lower asymptotic.

For the continuous Poisson–Dirichlet law, the largest coordinate
has upper-tail probability

\[
 {\mathbb P}(L_1>t)=\int_t^1\frac{du}{u}=-\log t
                  \qquad(1/2<t<1).
                                                        \tag{1}
\]

There can be at most one coordinate above t>1/2, so the
one-point correlation formula, equation (7) of that source,
gives (1). The difficulty is transferring it to a window
of width comparable to 1/log X at the endpoint 1.
The calculations below concern the actual shift 2.

## 2. An exact finite decomposition into integer cofactors

Let P+(n) be the largest prime factor of n>1. For fixed K>1
and X>K^2, define the genuine-prime weighted tail

\[
 H_K(X)=
 \sum_{\substack{X<n\le2X\\n+2\ {\rm prime}}}
 \log n\log(n+2)\,
 1_{\{P^+(n)/n>1/K\}}.
\]

As in the total ledger, Q_tw is the same weighted sum with
both n and n+2 prime. Then

\[
 \boxed{H_K=Q_{\rm tw}+D_K,}                             \tag{2}
\]

where the entire composite leakage is

\[
 D_K=
 \sum_{\substack{3\le k<K\\k\ {\rm odd}}}
 \ \sum_{\substack{q\ {\rm prime}\\
                  X<kq\le2X\\kq+2\ {\rm prime}}}
       \log(kq)\log(kq+2)\ge0.                          \tag{3}
\]

To prove the identity, write q=P+(n) and k=n/q.
The tail condition is exactly k<K. Since n+2 is an odd
prime for these n, both n and k are odd. The case k=1
is Q_tw, and every other possible k is at least 3.
Conversely, a term on the right has

\[
 q>X/k>K>k.
\]

Hence q is the unique largest prime factor of kq and
automatically satisfies the required tail condition.
The argument includes repeated prime factors of k.
The inner endpoints are exactly
floor(X/k)<q<=floor(2X/k); no endpoint term is discarded.

In particular,

\[
 \boxed{1<K\le3\quad\Longrightarrow\quad H_K=Q_{\rm tw}.} \tag{4}
\]

Equivalently, every odd composite n has P+(n)/n<=1/3.
The strict inequality in the definition of H_K matters
at K=3. Formula (4) supplies an identification, not a
lower bound for either side.

For K>3 the new sums in (3) require q and kq+2 to be
simultaneously prime. Their presence cannot be replaced
by an ordinary prime progression main term. Nor is
D_K a prime-power error: kq is composite even when
both displayed prime conditions hold.

## 3. The microscopic law has plateaus

Fix c>0 and consider the tail

\[
 \frac{\log P^+(n)}{\log n}>
              1-\frac{c}{\log(2X)},\qquad X<n\le2X.
                                                        \tag{5}
\]

Writing k=n/P+(n), its condition is

\[
 k<\exp\!\left(\frac{c\log n}{\log(2X)}\right).
\]

Thus its weighted mass is bounded below and above by

\[
 H_{\exp(c\log X/\log(2X))}
       \quad\hbox{and}\quad H_{e^c},                    \tag{6}
\]

respectively. For each fixed c these two tails eventually
agree exactly: their cofactor cutoffs converge from below
to e^c, and the interval between them eventually contains
no allowed integer k. If e^c is an integer, that endpoint
is excluded by both strict inequalities. The same statement
holds for the unweighted counts.

Consequently, for every fixed 0<c<log 3, (5) is exactly the
genuine twin-prime set at all sufficiently large X. In fact
the exclusion of composite n follows directly from
log(n/P+(n))>=log 3.

This rules out the proposed uniform extension

\[
 \vartheta_X(c)=
 -\log\!\left(1-\frac{c}{\log(2X)}\right)
                   +o(1/\log X),                      \tag{7}
\]

where vartheta_X(c) is the proportion of prime outputs
n+2 in the dyadic interval satisfying (5).
Choose two distinct c_1,c_2 in (0,log 3).
The actual left sides of (7) are identical. The proposed
right sides differ by

\[
 \frac{c_2-c_1}{\log(2X)}+O(1/\log^2X),
\]

which is not o(1/log X). Therefore (7) cannot hold for
both c_1 and c_2, regardless of how many twin primes exist.
This does not contradict fixed-parameter weak convergence.
It shows that a valid microscopic main term must retain
the discrete cofactor contributions in (2)-(3).

The fixed continuous tests supplied unconditionally by
the cited correlation lemma also vanish on every fixed-K
endpoint layer eventually. If a selected factor is the
largest one, its logarithmic coordinate tends to 1 and
leaves the allowed support. Every factor of the bounded
cofactor k has coordinate tending to 0, also outside
the compact support in the positive orthant. This is
a direct support calculation, not an estimate of the
mass in that layer.

## 4. Finite conversion from probabilities to the actual budget

Let

\[
 N_X=\#\{X<n\le2X:n+2\ {\rm prime}\},\qquad
 \vartheta_K=\frac{\#\{\hbox{terms counted by }H_K\}}{N_X},
\]

when N_X>0. Set L=log X and
Delta=log(2X+2)-L. The pointwise logarithmic bounds give
the exact decomposition

\[
 H_K=L^2N_X\vartheta_K+r_{\log},\qquad
 0\le r_{\log}\le
        (2L\Delta+\Delta^2)N_X\vartheta_K.               \tag{8}
\]

N_X is the actual finite prime-output count, including
the shifted endpoints. Classical PNT gives
lambda_X=L N_X/X -> 1. Equations (2) and (8) give

\[
 \frac{Q_{\rm tw}}X
   =\lambda_X L\vartheta_K-\frac{D_K}X+\frac{r_{\log}}X.
                                                        \tag{9}
\]

For a proposed endpoint approximation
vartheta_K=a_K/L+e_K, with fixed finite a_K, (9) becomes

\[
 \frac{Q_{\rm tw}}X=
 a_K-\frac{D_K}X+
 a_K(\lambda_X-1)+\lambda_X L e_K+\frac{r_{\log}}X.
                                                        \tag{10}
\]

Every conversion term is retained. An error e_K=o(1)
alone is too large here. The stronger e_K=o(1/L) would
make its term o(1); in that case (8) also gives
r_log=o(X). Such a microscopic estimate is not supplied
by the source, and the continuous candidate (7) is
incompatible with the exact plateaus.

Using genuine H_K and D_K avoids adding or removing
prime powers inside these quantities. The complete
signed identity, with the ledger's actual J, is

\[
 \boxed{T+R=J-H_K+D_K+r_{\rm cl}+r_\beta-E_{\rm pp}.}     \tag{11}
\]

For example, cofinal estimates

\[
 H_K\ge hCX-E_H,\qquad D_K\le dCX+E_D,\qquad
 h-d=\delta>0,\quad E_H,E_D\ge0,
\]

would give

\[
 Q_{\rm tw}\ge\delta CX-E_H-E_D,
\]

and

\[
 T+R\le(1-\delta)CX+
 |J-CX|+D_{\rm cl}+D_\beta+E_H+E_D-E_{\rm pp}.            \tag{12}
\]

These hypothetical errors must satisfy E_H+E_D=o(X)
for the indicated fixed margin. The favorable
-Epp in (12) may be discarded for an upper bound;
it is not counted twice. The middle-prime 0.263 bound
is not added as a separate saving to this direct estimate.

For K<=3 the needed H_K lower bound is already a twin
lower bound. For larger K the full leakage remains.
Neither case produces a positive margin from the
available factor-correlation theorem. The best certified
complete margin remains zero; M4-M6 remain unresolved.
