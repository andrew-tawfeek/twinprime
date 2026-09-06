# Exceptional-character bias and the complete twin-prime budget

Checkpoint: 2026-09-05. The middle-prime class bound is verified, but
the certified positive margin in the
[complete signed budget](SIGNED_TOTAL_BUDGET.md) remains **zero**.
This paper tests a different source of arithmetic information:
quadratic-character bias from a sufficiently close real zero.
It yields a positive budget under an explicit zero-existence
hypothesis. That hypothesis is not proved, and no unconditional
endpoint or further Lean formalization is claimed.

Write C=2 C2, and retain X, J, T, R, D_cl, D_beta and Epp exactly
as in the total ledger. In particular,

\[
 Q_{\rm tw}=J-T-R+r_{\rm cl}+r_\beta-E_{\rm pp},\qquad
 |r_{\rm cl}|\le D_{\rm cl},\quad |r_\beta|\le D_\beta.
                                                        \tag{1}
\]

## 1. A nonnegative model exposes the composite leakage

Let chi be a real quadratic Dirichlet character, including its zero
values at integers not coprime to its modulus. Define Dirichlet
convolutions

\[
 a_\chi=1*\chi,\qquad
 G_\chi=\chi*\log=a_\chi*\Lambda,\qquad
 \Delta_\chi=G_\chi-\Lambda.
                                                        \tag{2}
\]

These are exact identities, since log=1*Lambda. Multiplicativity and
the prime-power formula give

\[
 a_\chi(p^j)=\sum_{i=0}^j\chi(p)^i=
 \begin{cases}
 j+1,&\chi(p)=1,\\
 1\text{ if }j\text{ is even, and }0\text{ otherwise},
      &\chi(p)=-1,\\
 1,&\chi(p)=0.
 \end{cases}
\]

Thus a_chi is nonnegative, a_chi(1)=1, and

\[
 \Delta_\chi(n)=
 \sum_{\substack{d\mid n\\d>1}}a_\chi(d)\Lambda(n/d)\ge0.
                                                        \tag{3}
\]

For the unrestricted model correlation and its complete defect set

\[
 \begin{split}
 {\cal M}_\chi(X)&=\sum_{X<n\le2X}G_\chi(n)G_\chi(n+2),\\
 {\cal D}_\chi(X)&=\sum_{X<n\le2X}
  \bigl(\Delta_\chi(n)\Lambda(n+2)
       +\Lambda(n)\Delta_\chi(n+2)
       +\Delta_\chi(n)\Delta_\chi(n+2)\bigr).
 \end{split}
\]

Then the exact genuine-prime identity is

\[
 Q_{\rm tw}={\cal M}_\chi-{\cal D}_\chi-E_{\rm pp},
 \qquad {\cal D}_\chi\ge0.                              \tag{4}
\]

The model is a majorant. Positivity alone does not make it a prime
minorant; an upper bound for its entire defect is needed.
No asymptotic for either unrestricted quantity in (4) is asserted.
In particular, the published correlation theorem used below must
not be read as supplying separate small errors for these two sums.

There is nevertheless an exact reason character bias can help.
If n is squarefree, then

\[
 G_\chi(n)=\sum_{p\mid n}\log p
                  \prod_{\substack{\ell\mid n\\\ell\ne p}}
                       (1+\chi(\ell)).                 \tag{5}
\]

For a composite n, two distinct prime divisors with chi=-1 make
every summand vanish. Consequently composite leakage on this
squarefree support requires at most one such divisor. This
statement includes primes dividing the conductor, whose character
value is zero rather than minus one. For distinct primes p,r,

\[
 \Delta_\chi(pr)=(1+\chi(r))\log p+(1+\chi(p))\log r.
\]

At a square, Delta_chi(p^2)=(1+chi(p))log p. Higher prime powers
and nonsquarefree composites are still present in (3)-(4).
No squarefree-removal error has been silently discarded.
Obtaining the required bias is new arithmetic, not a consequence
of choosing the notation chi.

## 2. A published estimate that would make the total margin positive

[Matomäki–Merikoski, Corollary 1.1(i)](https://academic.oup.com/imrn/article/2023/23/20337/7111993)
states the following specialization. If a primitive quadratic
character of conductor q>=2 has a real zero
beta=1-1/(eta log q), eta>=10, then for a fixed a>=1 there is a
constant K_a, independent of q, eta and t, such that

\[
 |F(t)-Ct|\le K_a t e^{-a\sqrt{\log\eta}},
 \quad q^{10}\le t\le q^{10\log\eta},\qquad
 F(t)=\sum_{n\le t}\Lambda(n)\Lambda(n+2).
                                                        \tag{6}
\]

The source's fixed-shift corollary already absorbs the
conductor-dependent correction from its general theorem into its error.
No such term is being dropped from (6). This external input is
not formalized here.

Now take the integer X=q^10 and fix a=1, writing K=K_1>0.
Both X and 2X lie in the stated window: q>=2 and eta>=10 imply
2q^10<=q^(10 log eta). Thus no endpoint extrapolation or rounding
is required. Define the actual signed prefix error

\[
 e_\chi(t)=F(t)-Ct,\qquad
 e_{\rm dyad}=e_\chi(2X)-e_\chi(X),\qquad
 D_{\rm zero}=3KX e^{-\sqrt{\log\eta}} .
\]

Subtracting the two prefixes, rather than treating their errors
as the same quantity, gives

\[
 W_2=CX+e_{\rm dyad},\quad
 |e_{\rm dyad}|\le D_{\rm zero},\quad
 \boxed{Q_{\rm tw}\ge CX-D_{\rm zero}-E_{\rm pp}.}       \tag{7}
\]

All composites in the Mangoldt correlation are charged by the
existing exact Epp. There is no logarithmic unweighting, no change
of the shift, and no second prime-power deduction.

Choose a fixed eta_0>=10 sufficiently large that

\[
 3K e^{-\sqrt{\log\eta_0}}\le C/4.                       \tag{8}
\]

If conductors q with a zero of quality eta>=eta_0 are unbounded,
then X=q^10 is cofinal. Since Epp=o(X), equations (7)-(8) give

\[
 Q_{\rm tw}(X)\ge CX/2
\]

on all sufficiently large scales selected this way. This would
prove twin-prime infinitude. The source does not provide a
numerical value of K, and no numerical eta_0 is asserted.

The transfer to the actual signed loss is also explicit. From
W2=J-T-R+r_cl+r_beta, put

\[
 E_0=|J-CX|+D_{\rm cl}+D_\beta=o(X).
\]

Then

\[
 \boxed{T+R\le D_{\rm zero}+E_0\le CX/4+E_0.}           \tag{9}
\]

Here Epp is absent because (9) uses W2 directly; it remains in
the genuine-prime bound (7). The middle-prime allowance 0.263
is not counted as another saving. Under the stated hypothesis
this mechanism would improve the full leading loss from 1 to
at most 1/4, with E0 as its complete remaining budget.

## 3. The missing quantifier is an unbounded supply of zeros

The sufficient hypothesis established by this calculation is

\[
 \forall Q\ \exists q>Q,\ \chi,\ \beta:\quad
 \chi\text{ primitive quadratic of conductor }q,\quad
 L(\beta,\chi)=0,\quad
 0<1-\beta\le\frac1{\eta_0\log q}.                       \tag{10}
\]

Neither the repository nor the cited theorem proves (10).
Quality eta tending to infinity is sufficient but stronger than
needed: a fixed quality above the threshold in (8), attained at
unbounded conductors, already suffices.

A single zero has a fixed finite eta and supplies only a bounded
scale window. It cannot be reused for arbitrarily large X.
For bounded conductors, there are finitely many characters, and
their L-functions are nonzero at one and continuous there.
Their zero-free neighborhoods of one give a common finite upper
bound on the possible quality. Thus an unbounded-quality sequence
would also force unbounded conductors, but its existence remains
unproved.

The checked
[real-zero power gap](../TwinPrime/Analytic/SiegelZeroGapUnconditional.lean#L28)
has the direction

\[
 \forall\varepsilon>0\ \exists d_\varepsilon>0:
 \qquad 1-\beta\ge d_\varepsilon q^{-\varepsilon}
                                                        \tag{11}
\]

for actual zeros in its stated logarithmic region. It bounds
possible zeros away from one; it does not produce any. When it
applies to a zero in (10), it gives
eta<=q^epsilon/(d_epsilon log q). This is compatible both with
no such zeros and with an unbounded sequence of fixed quality.
For any fixed eta_0 and epsilon>0,
q^epsilon/(eta_0 log q) tends to infinity, so a hypothetical gap
1/(eta_0 log q) does not contradict (11).

The proof of the uniform
[Siegel value lower bound](../TwinPrime/Analytic/SiegelValue.lean#L23)
uses an exhaustive case split for an auxiliary zero. That split
does not assert its existence in either the final theorem or
the zero-free branch. Even the existence of zeros arbitrarily
close to one in absolute distance, without a conductor-relative
rate, would not by itself supply (10): the numerical parameters
1-beta_k=1/k and q_k=ceil(exp(k^2)) have eta_k tending to zero.
This example concerns quantifiers, not actual Dirichlet zeros.

There is also no conflict with the proved Siegel-Walfisz input.
At the selected X=q^10, the exceptional conductor q exceeds
(log X)^B eventually for every fixed B. It is outside that
theorem's fixed-polylogarithmic conductor range. The averaged
BV theorem does not assert a small relative error for each
individual conductor q, so it cannot be used to infer the
nonexistence of the zero either.

Taking the contrapositive of the established implication, a
failure of twin-prime infinitude would force the conductors in
(10) to be bounded. It does not make that boundedness false.
The alternative with no sufficiently close zeros at large
conductors remains open for the twin-prime problem. The
[earlier distribution test](DISTRIBUTION_AND_FOURIER_BUDGET.md)
already shows that the assessed lower linear sieve has zero
prime-isolating coefficient even if granted one-variable
distribution through any exponent at most one. That calculation
does not turn this alternative into a positive signed estimate.

## 4. Decision for the current proof program

The character mechanism is different from an unrestricted divisor
moment: its potential saving comes from arithmetic bias suppressing
composite leakage. Equations (7) and (9) demonstrate that its
published conditional estimate would fit the complete budget.
Equation (10) is the unsupplied input.

Accordingly the unconditional ledger remains unchanged. Neither
formalizing the cited conditional theorem nor restating (10) as
a new Lean premise would discharge M4-M6. No substantial
formalization of this route is justified without new evidence
for (10), or a separate estimate that gives a positive total
margin in its complementary case.
