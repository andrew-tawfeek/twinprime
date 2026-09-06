# Exact finite centering and a logarithmic-scale target

Checkpoint: 2026-09-05. All seven modules below passed the full root build
(8916 jobs). All 17 new public theorems occur in the integrated audit of
1255 unique selected declarations, with only Classical.choice, propext and
Quot.sound and zero errors. The 261-file project source scan is clean.
Independent review covered the finite identities, error bounds, cutoff
applications and conditional endpoint. The positive signed gain remains
unproved. This does not complete M4-M6 or the Twin Primes Conjecture.

## 1. Keep the finite classical terms

Write L=log(2X+2), and use the repository's actual terms A, H, I, B and W2.
Define

\[
 J(U,V;X)=X S(U)+F(U)M(U,X)-XQ(U,V),
\]

where S is `smoothedTotientSum`, F is `oddMoebiusTotientSum`, M is
`logarithmicMass`, and Q is the full `totientTypeIMain`, including its
shared-prime correction. These are finite sums, not limiting coefficients.
[ClassicalCorrelationCenter](../TwinPrime/Analytic/ClassicalCorrelationCenter.lean)
proves the exact identity

\[
 W_2-(B+J)=(A-XS)+(H-FM)-(I-XQ).                    \tag{1}
\]

For positive integer cutoffs U,V with UV<=X, its actual finite bound is

\[
 |W_2-(B+J)|\le
 8L\sum_{1\le q\le UV}E_q(2X+2)+3E_{\rm even}(U,V,X),       \tag{2}
\]

with E_q the maximal progression error and
E_even=(UV+1)L*evenProgressionBound(X). The constants retain the three
odd errors 2+4+2 and all three even errors. No limit for S, F or Q is
needed to prove (2).

## 2. Actual error control at every fixed logarithmic power

Let U(X),V(X) be arbitrary natural-valued functions, eventually at least
one, with UV<=X^a eventually for a fixed 0<=a<1/2. Then, for every fixed
natural k,

\[
 \frac{|W_2(X)-(B(U,V;X)+J(U,V;X))|}{X}L^k\longrightarrow0. \tag{3}
\]

[LogPowerDistribution](../TwinPrime/Analytic/LogPowerDistribution.lean)
applies the actual BV estimate with a logarithmic exponent chosen after k.
For the isolated weighted progression sum L^k*sum E_q/X, exponent k+1
gives an eventual upper bound 2^k K/log X. Polynomial slack below 1/2
absorbs the required logarithmic restriction on the modulus range.

[LogPowerEvenBudget](../TwinPrime/Analytic/LogPowerEvenBudget.lean) uses
the existing bound 4(2X+2)^(a+1/2)L^2. Its quotient by X tends to zero
after any fixed logarithmic weight, since a+1/2<1. The proof reuses the
general power-versus-log lemma already in
[BilinearExceptional](../TwinPrime/Analytic/BilinearExceptional.lean).

[ClassicalCenterPrecision](../TwinPrime/Analytic/ClassicalCenterPrecision.lean)
combines these estimates with (2). It also proves the corresponding
all-logarithmic-power estimate for the actual Type I remainder I-XQ.
The unconditional BV theorem is supplied by
[ClassicalDistribution](../TwinPrime/Analytic/ClassicalDistribution.lean).
[PrimePowerLogPrecision](../TwinPrime/Analytic/PrimePowerLogPrecision.lean)
separately proves Epp(X)L^k/X->0 from the existing explicit square-root
bound, retaining every excluded nonprime contribution.

These statements hold for each fixed k; they do not give uniformity when
k grows with X. Nor do they imply an error smaller than X^alpha for a
fixed alpha<1. In particular, they do not justify a square-root-sized
positive target for B+J.

## 3. Centered cutoff transfer

For V,W<=X the exact relation is

\[
 (B(U,V)+J(U,V))-(B(U,W)+J(U,W))
   =(I(U,V)-XQ(U,V))-(I(U,W)-XQ(U,W)).              \tag{4}
\]

Thus the centered cutoff change has the precision in (3) whenever both
products lie below fixed powers smaller than 1/2. The earlier uncentered
o(X) cutoff theorem alone did not have this precision.

[QuarterClassicalCenter](../TwinPrime/Analytic/QuarterClassicalCenter.lean)
supplies actual primary and quarter applications: U=floor(X^(1/5)),
V=U or floor(X^(1/4)), with product exponents 2/5 and 9/20. It also combines
the quarter estimate with the proved prime-only beta replacement. This
controls complete signed sums; arbitrary further restrictions do not follow.

## 4. A sufficient gain which can be sublinear

[ConditionalClassicalCenter](../TwinPrime/ConditionalClassicalCenter.lean)
uses (3) and the Epp estimate to prove the implication

\[
 \begin{gathered}
 c>0,\quad k\in\mathbb N,\quad
 \forall Y\ \exists X\ge Y:\quad
 B(U,V;X)+J(U,V;X)\ge \frac{cX}{\log^k(2X+2)}
 \\
 \Longrightarrow\quad \text{infinitely many twin primes}.
 \end{gathered}                                                    \tag{5}
\]

The elementary support and product conditions from Section 2 are explicit
arguments. There is no unproved BV argument. At a sufficiently large good
scale, |W2-(B+J)|+Epp is strictly smaller than the displayed gain, so W2>Epp.
The existing exact dyadic endpoint then gives a genuine twin pair above
each requested threshold.

The signed gain in (5) is an unproved theorem argument, not an axiom and
not a consequence of the error estimates. No lower bound for B+J of this
size has been obtained. The original PLAN's B* route remains available;
this alternative does not discharge its signed obligation.

Merely replacing J by CX and observing B+CX>0 is insufficient. At the
level of abstract identities, A=CX, K=-h(X), B=-CX+h(X), W2=Epp=0 satisfies
the known normalized limits whenever h=o(X). Taking h=X^(3/4) even
preserves every fixed logarithmic improvement while producing a positive,
unbounded B+CX. This is a counterexample to that inference from the stated
limits, not a model of the actual arithmetic functions. Retaining the
finite J removes this particular error-budget ambiguity; it creates no sign.

## 5. Additional routes checked

Cutoff averaging does not generate missing positivity: for fixed U,X,
B(U,V)-I(U,V) is independent of V<=X. Normalized averages of the exact
decomposition preserve the same W2, while zero-sum cutoff averages cancel
it. Scale averaging would need an independent signed estimate as well.
The almost-all-scales theorem of Tao and Teräväinen treats bounded
multiplicative factors. Inserting the prime shift and the scale-dependent
truncated smooth coefficient is outside those hypotheses; no applicable
transfer was found.
[Primary source, version 2](https://arxiv.org/abs/1809.02518v2).

Asymmetric powers U=X^u,V=X^v with 0<u, v>1/3 and u+v<1/2 simplify a V-rough
part to at most two prime factors. Put eta=1-2v. The two-prime part has
a<=2X/(V+1)^2 of size X^eta, and admissibility gives u<eta/2. Its absolute
estimate still involves sum |m_U(a)|/a. The de la Bretèche-Dress-Tenenbaum
mean-square theorem gives order A for sum_(a<=A)m_U(a)^2 when U and A/U
both grow, and a global O(A) upper bound. Cauchy-Schwarz and partial
summation therefore give only O(1+log(A/U)) for that harmonic mass; this
does not prove a vanishing signed constant as eta decreases. This last
application is our inference from the source's mean-square result, not a
lower bound for the actual shifted weighted sum.
[Primary source, Theorem 1.1 and (1.5)](https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf).

Even a prime smooth part U<a<=V contributes a negative sum over p and
ap+2 both prime. Modulus a is small, but BV does not retain primality of
the quotient p; switching gives p>X/V>sqrt(X). This checked coefficient
class remains a concrete unresolved case.

A search for logarithmically weighted positivity also found Ren's
arXiv:2511.12944. Its current version is withdrawn, citing an invalid final
integral calculation. It is not used as a mathematical input.
[Withdrawal record, version 3](https://arxiv.org/abs/2511.12944v3).

The subsequent [smoothing and sign review](SMOOTHED_SIGNED_GAIN_REVIEW.md)
computes the full logarithmic cutoff average's nonzero main displacement.
It retains the larger averaged center, gives an exact negative-change
witness, and checks a genuinely applicable weighted second moment. None
of these mechanisms supplies the required signed gain.
