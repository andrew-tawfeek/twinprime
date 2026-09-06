# The cube-cutoff rough-parity identity

`TwinPrime/RoughParity.lean` implements PLAN.md Section 9. Its finite identities
are unconditional under the displayed integer range conditions. Its final
twin-prime implications retain the required estimates as hypotheses.

For natural numbers `X,z`, assume

\[
 3\le z<X,\qquad 2X+2<z^3.
\]

Let `P(z)` be the product of every prime at most `z`, and set

\[
 R(X,z)=\{n:X<n\le2X,\ \gcd(P(z),n(n+2))=1\}.
\]

The Lean definitions are `roughDyadicSet`, `roughDyadicCount`,
`roughLiouvilleLeft`, `roughLiouvilleRight`, `roughLiouvilleProduct`, and
`roughParityCombination`. They use the existing integer-valued Liouville
function, cast to the reals in sums, and the existing dyadic twin count `N2`.

## Multiplicity and endpoints

Both members of each surviving pair are at least two and strictly below
`z^3`. Every prime factor is strictly greater than `z`, since the primorial
includes the prime `z` when `z` is prime.

Here is the elementary factorization argument formalized by
`prime_or_semiprime_of_rough`. Write `n=p m`, with `p` its least prime factor.
If `m=1`, then `n` is prime. Otherwise `m>=2`. Since `p>z` and `n<z^3`, one
has `m<z^2`. Every prime factor of `m` is also greater than `z`, so the
existing square-cutoff primality lemma makes `m` prime. Thus `n` is prime or
`p q`, with no requirement that `p` and `q` differ.

Consequently the total prime-factor count **with multiplicity** is one or
two. A prime square has count two and Liouville value `+1`; its prime selector
vanishes. The proof neither assumes squarefreeness nor discards prime squares.
The conditions `3<=z<X<n` explicitly exclude `n=0,1`; the shifted member is
also at least two. The largest shifted member is `2X+2`, which explains the
strict cube condition on that endpoint.

Every twin with lower member in `(X,2X]` survives: both of its prime members
exceed `X`, hence exceed `z`. Therefore no small-prime-pair correction is
needed.

## Exact identities

On `R`, the single selector `1-lambda(n)` is two for a prime and zero for a
semiprime. The two-factor selector has the following values:

| Factor counts `(Omega(n),Omega(n+2))` | `lambda(n)` | `lambda(n+2)` | Product of selectors |
|---|---:|---:|---:|
| `(1,1)` | -1 | -1 | 4 |
| `(1,2)` | -1 | +1 | 0 |
| `(2,1)` | +1 | -1 | 0 |
| `(2,2)` | +1 | +1 | 0 |

`rough_liouville_weighted_identity` proves, for every real weight `a(n)`,

\[
 4\sum_{\substack{X<n\le2X\\n,n+2\ \mathrm{prime}}}a(n)
 =\sum_{n\in R}a(n)(1-\lambda(n))(1-\lambda(n+2)).
\]

No positivity assumption on `a` is needed. Taking `a=1` and expanding proves
`rough_parity_identity`:

\[
 4N_2(X)=S-L_0-L_2+L_{02},
\]

where `S=#R`, `L0=sum_R lambda(n)`, `L2=sum_R lambda(n+2)`, and
`L02=sum_R lambda(n)lambda(n+2)`.

The product correlation alone cannot distinguish `(1,1)` from `(2,2)`:
both have total even parity and product `+1`. The separate correlations carry
information needed by this identity.

## Explicit conditional endpoint

`twinPrimeConjecture_of_cofinal_roughParity_pos` turns cofinal positive values
of the displayed combination, at admissible cutoffs, into the existing
`TwinPrimeConjecture`. This uses the existing equivalence with cofinal
positivity of `N2`. The positive-combination hypothesis is an exact interface,
not a newly established lower bound.

`twinPrimeConjecture_of_rough_distribution_and_parity` separates sufficient
inputs. Choose a cutoff function `z(X)`, a real lower-bound function `M(X)`,
a constant `delta>0`, and a threshold `X0`. Its hypotheses are:

1. For every `X>=X0`, the cutoff satisfies the displayed range conditions.
2. For every such `X`, `0<M(X)<=S(X,z(X))`.
3. Cofinally in `X>=X0`,

   \[
    L_0+L_2-L_{02}\le(1-\delta)M(X).
   \]

On those intervals the combination is at least `delta M(X)>0`. Thus there
is a twin beyond any prescribed bound. The theorem imposes no unsupported
prediction that the three correlations separately have mean zero. No estimate
for either the rough count or the required parity combination is proved here.

## Verification

Standalone verification command, run from the repository root:

```powershell
lake env lean TwinPrime/RoughParity.lean
```

This command passed without warnings. A second check through `lean --stdin`
printed the axioms of the prime-or-semiprime lemma, the weighted identity, the
four-correlation identity, and the final distribution-and-parity endpoint.
Each depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The file is now imported through `TwinPrime.lean`. The integrated full
`lake build` passed, reporting **8710 jobs**. The integrated axiom/type audit
checked **121 selected declarations** with no unexpected dependencies.
The file introduces no axioms, `sorry`, or `admit`.

These checks verify the finite identities and conditional implications. The
rough-count and parity estimates required by the endpoint remain unproved.
