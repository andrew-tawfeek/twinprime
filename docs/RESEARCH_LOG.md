# Research log

Entries are dated. Each records what was attempted, the outcome, and (for computations) the
command that reproduces it. Claims of the form "proved" refer to Lean-checked theorems in this
repository unless stated otherwise.

Correction notice (2026-09-04): historical dates and measured tables are preserved below.
The current [PLAN.md](../PLAN.md) and [parity note](PARITY.md) supersede the earlier
interpretations. Formal theorem types, numerical observations, and analytic hypotheses have
different status. In particular, no entry establishes a twin-prime lower bound.

## 2026-09-04 — Setup, sieve validation, plan

* Toolchain: `elan`, Lean `leanprover/lean4:v4.32.0`, and Mathlib tag `v4.32.0`.
  `lake build` of the skeleton succeeds (Mathlib oleans from cache).
* Wrote `compute/twinsieve` (Rust, multithreaded bit-packed odd-only segmented sieve).
  Validation against known values:

  | x     | pi_2(x)   | literature | ok |
  |-------|-----------|------------|----|
  | 1e6   | 8169      | 8169       | ✓  |
  | 1e7   | 58980     | 58980      | ✓  |
  | 1e8   | 440312    | 440312     | ✓  |
  | 1e9   | 3424506   | 3424506    | ✓  |

  Time to `1e9`: 0.11 s. Brun-constant extrapolation `S(1e9) + 4 C_2 / log(1e9) = 1.9021602...`
  versus the accepted `B_2 ≈ 1.902160583`. Command:
  `compute/twinsieve/target/release/twinsieve 1e9 1e3 1e4 1e5 1e6 1e7 1e8 1e9`.
* Surveyed Mathlib `v4.32.0` for usable material: `NumberTheory/SelbergSieve.lean` (setup through
  the Λ² diagonalisation, no fundamental theorem), `NumberTheory/Chebyshev.lean`
  (`θ(x) ≤ x log 4`), `NumberTheory/Wilson.lean` (both directions of Wilson),
  `NumberTheory/Harmonic/Bounds.lean` (log bounds for harmonic sums),
  `NumberTheory/AlmostPrime.lean` (`IsAlmostPrime`, `IsSemiprime`; no Chen).
  Mathlib does **not** contain Mertens' theorems, the Brun–Titchmarsh inequality, Bombieri–
  Vinogradov, or any bounded-gaps result. Consequence: Phase 2 must avoid Mertens (elementary
  route recorded in `PLAN.md`).
* Wrote `docs/PLAN.md`.
* Ran the sieve to `1e13` (1293 s). All checkpoints agree with the literature
  (OEIS A007508): `pi_2(1e10) = 27412679`, `pi_2(1e11) = 224376048`,
  `pi_2(1e12) = 1870585220`, `pi_2(1e13) = 15834664872`. Ratio `pi_2(x) / (2 C_2 ∫_2^x dt/log²t)`
  is `1.000004` at `1e13`; Brun-constant extrapolation `1.9021605711` (Nicely: `1.902160583`).
  Table in `data/twin_counts_1e13.tsv`; command:
  `twinsieve 1e13 1e3 1e4 1e5 1e6 1e7 1e8 1e9 1e10 1e11 1e12 2e12 5e12 1e13`.
* Located Arend Mellendijk's `selberg-sieve4` (Lean 4.7-era) project. It contains the Selberg
  fundamental theorem (`Selberg.lean`, 442 lines) and a Brun–Titchmarsh application, but its
  twin-prime application file is a 50-line stub containing `sorry`. So Brun's theorem for twin
  primes is new formal work; the fundamental theorem can be ported onto Mathlib's
  `SelbergSieve` structure (which is the upstreamed part of the same project).



## 2026-09-04 (later) — Phase 2 complete: Brun's theorem machine-checked

All of the following are Lean 4 theorems in this repository, compiled against Mathlib `v4.32.0`,
checked with `#print axioms` to depend only on `propext`, `Classical.choice`, `Quot.sound`
(script: `scripts/Axioms.lean`, run with `lake env lean scripts/Axioms.lean`).

| Lean name | Statement |
|-----------|-----------|
| `SelbergSieve.selberg_bound_simple` | fundamental theorem of the Selberg upper-bound sieve: `siftedSum ≤ X/S + Σ_{d∣P, d≤y} 3^{ω d} |R_d|` |
| `TwinPrime.Sieve.twinRoots_eq` | `r(r+2) ≡ 0 (mod d)` has `2^{ω d}` roots for odd squarefree `d` |
| `TwinPrime.Sieve.twinSieve_abs_rem_le` | `|R_d| ≤ 2^{ω d}` for the twin sieve |
| `SelbergSieve.selbergBoundingSum_ge_sum` | Mertens-free lower bound for `S` via completely multiplicative expansion |
| `TwinPrime.Sieve.twinCount_le_explicit` | `π₂(x) ≤ (z+1) + (x+1)/L(z)² + z²(1+log z²)^6` for `z ≥ 16` |
| `TwinPrime.twinCount_le` | `π₂(x) ≤ 2^33 · x/(log x)²` for all `x ≥ 2` |
| `TwinPrime.twinCount_isBigO` | `π₂(x) = O(x/(log x)²)` |
| `TwinPrime.brun` | **Brun (1919)**: `Summable (fun p : twinPrimes => 1/p)` |

Line counts: `Sieve/Fundamental.lean` 572, `Sieve/ErrorSum.lean` 134, `Sieve/Expansion.lean` 171,
`Sieve/TwinSieve.lean` ~330, `Sieve/TwinBound.lean` ~350, `Brun.lean` ~380.

Design decisions that mattered:
* Sifting only by *odd* primes (`oddPrimorial`) so that `ν(p) = 2/p < 1` on every sifting prime
  and the CRT count is exactly `2^{ω d}`; the prime 2 contributes nothing to the upper bound.
* Support `{n(n+2) : n < x+1}` (an injective image) so Mathlib's `BoundingSieve` applies
  verbatim; twin primes `p > z` are counted by the sifted set.
* The lower bound `S ≥ (Σ_{a ≤ √z odd} 1/a)²` uses only harmonic-sum bounds, avoiding Mertens'
  theorem (absent from Mathlib).  Constant: `2^33`, not optimised.
* The remainder is controlled by counting residue classes with `Nat.count_modEq_card`.

Commits: `f08f2ec` (fundamental theorem), `afd0d9a`, `1de61f8`, `a82a246`, `4bc84c0` (Brun).

### What this does and does not say about the conjecture

Brun's theorem is an *upper* bound.  It is consistent with both finitely and infinitely many
twin primes.  The lower-bound direction is where every known method stops: any sieve of this
type (upper or lower bound) is blind to the parity of `Ω(n(n+2))`, and the twin-prime set
`{n : Ω(n) = Ω(n+2) = 1}` is a parity-constrained set.  Phase 3 records this obstruction
precisely and tests the numerical side of the Maynard–Tao functional for `k = 2`.


## 2026-09-04 (evening) — GPU experiments, Hardy–Littlewood constant, parity note

* **GPU sieve cross-check** (`compute/gpu/twinsieve_torch.py`, PyTorch):
  independent implementation reproduces `pi_2(10^6..10^10)` exactly (8169, 58980, 440312,
  3424506, 27412679) in 5.8 s.  Table: `data/gpu_twin_counts_1e10.tsv`.
* **Maynard–Tao functional** (`compute/gpu/maynard_mk.py`): floating-point Galerkin estimates on the GPU
  (piecewise-constant functions on the simplex, power iteration), compared with Maynard's rigorous
  upper bound `M_k ≤ (k/(k-1)) log k`:

  | k | grid estimate (uncertified) | Richardson (heuristic) | upper bound | needed for 2 primes under EH |
  |---|---|---|---|---|
  | 2 | 1.38572 | 1.3859 | 1.386294 | > 2 |
  | 3 | 1.64095 | 1.6465 | 1.647918 | > 2 |
  | 4 | 1.81051 | 1.8458 | 1.848392 | > 2 |
  | 5 | 1.89258 | 2.0110 | 2.011797 | > 2 |

  A first run had a wrong simplex mask (`sum i ≤ N-2` instead of `N-k`), producing "lower
  bounds" above the rigorous upper bound for `k ≥ 4`; the bug was caught precisely because the
  upper bound is a theorem.  Fixed; all values now sit below the upper bound and increase with `N`.
  Corrected conclusion: `M_2 = 1/(1-W(1/e)) = 1.38593… < 2 log 2 < 2`, by
  [Polymath8b, Corollaries 6.3–6.4](https://arxiv.org/html/1407.4897).
  The standard two-coordinate criterion cannot reach twin primes even at level 1.
  The old equality with `2 log 2` was false. The `k=5` extrapolation above 2 is
  not a certified lower bound; rounding control is also needed for finite-grid certificates.
* **Formal**: `TwinPrime/HardyLittlewood.lean` defines the twin prime constant
  `C₂ = ∏_{p>2}(1 − 1/(p−1)²)` as a convergent infinite product (`Multipliable`), proves
  `0 < C₂ ≤ 1`, states `HardyLittlewoodConjecture := π₂(x) ∼ 2 C₂ x/(log x)²`, and proves it
  implies the twin prime conjecture.  `TwinPrime/Conditional.lean`: growth/lower-bound/HL
  implications, density zero, Brun's constant `brunConstant > 0`.
* Wrote `docs/PARITY.md`: the parity obstruction as it applies to the formalised sieve.


## 2026-09-04 (night) — First lower-bound theorem: twin rough numbers

* `TwinPrime/Sieve/Legendre.lean`: Legendre's exact identity for any `BoundingSieve`
  (`siftedSum = ∑_{d∣P} μ(d) A_d`, hence `siftedSum ≥ X ∏_{p∣P}(1-ν p) − ∑_{d∣P}|R_d|`), the twin
  sieve with *all* primes `≤ z` (`twinSieveL`, `ν(2) = 1/2` via the root count `twinRoots 2 = 1`),
  the remainder bound `|R_d| ≤ ρ(d)`, `∑_{d∣P} ρ(d) ≤ 3^{π(z)}`, and the telescoping main term
  `∏_{p ≤ z}(1 − ν p) ≥ 1/z²`.  Result: `twinRough_count_ge`:
  `#{n ≤ x : n(n+2) coprime to primorial z} ≥ (x+1)/z² − 3^{z+1}` for `z ≥ 3`.
* `TwinPrime/TwinRough.lean`: with `z = ⌊log x/(2 log 3)⌋` this is `≥ x/(log x)²` for `x ≥ 2^24`
  (`twinRough_count_ge_of_large`), hence **`twinRough_infinite`**: infinitely many `n` such that
  every prime factor of `n(n+2)` exceeds `log n/(2 log 3)` — both `n` and `n+2` are simultaneously
  rough.  Axioms: standard three.
* Honest assessment: this is the weakest member of the family "Brun 1920 (9 prime factors) →
  Rényi → Chen (p+2 = P₂)".  Its value is structural: the library now contains a *lower-bound*
  sieve argument for the twin sequence, with the same remainder machinery as the upper bound.
  Improving `log n` to `n^{1/(c log log n)}` (Brun's pure sieve with Bonferroni truncation) needs
  Mertens-type bounds `∑_{p≤z} 1/p ≤ log log z + O(1)`, which are absent from Mathlib; that is the
  natural next formal target (`docs/PLAN.md`, Phase 3.4).


## 2026-09-05 — Brun's pure sieve: twin almost-primes with `O(log log n)` prime factors

New files (all `sorry`-free, standard axioms):

* `Sieve/Mertens.lean` — `∑_{p ≤ z} 1/p ≤ 8 (1 + log (⌊log₂ z⌋ + 1))` from Chebyshev's
  `θ(x) ≤ x log 4` (Mathlib) by dyadic blocks.  Mathlib has no Mertens theorem; this crude
  `O(log log z)` bound is all the sieve needs.
* `Sieve/Bonferroni.lean` — `∑_{j ≤ m} (−1)^j C(t, j) = (−1)^m C(t−1, m)`; a squarefree `g` has
  `C(ω g, j)` divisors with `ω = j`; the truncated Möbius function `μ·[ω ≤ m]` (odd `m`) is a
  lower-bound sieve; the lower-bound sieve inequality `∑_{d∣P} w(d) A_d ≤ siftedSum`.
* `Sieve/Rankin.lean` — `∑_{d∣P} h(d) = ∏_{p∣P}(1 + h(p))` for multiplicative `h`; Rankin's
  trick for tails (`ω ≥ m+1`) and heads (`ω ≤ m`); `∏(1+a) ≤ e^{∑a}`; `∏(1−t) ≥ e^{−3∑t}`.
* `Sieve/BrunLower.lean` — **exact Brun inequality** `brun_count_ge`: for every `z ≥ 1`,
  `#{n ≤ x : n(n+2) coprime to primorial z} ≥ (x+1) e^{−3ℓ(z)}/2 − e⁴ z^{m(z)}` with
  `ℓ(z) = 16(1 + log(log₂ z + 1))`, `m(z) = 2⌈3ℓ(z)⌉ + 1`.
* `BrunAlmostPrime.lean` — with `z = ⌊exp(log x/(1000 log log x))⌋`:
  `brun_count_ge_eventually`: the count is `≥ x/(4 (log x)^96)` for large `x`;
  **`brun_almostPrime_infinite`**: infinitely many `n` with `Ω(n) + Ω(n+2) ≤ 6000 log log n`.

This is Brun's 1919/1920 "pure sieve" argument in its simplest form.  Brun's own result (each of
`n`, `n+2` has at most 9 prime factors) needs the full combinatorial sieve with a bounded number
of iterations; Chen's `p+2 = P₂` needs Bombieri–Vinogradov plus the switching principle — both
beyond the present library.  The constants (`1000`, `96`, `6000`) come from the crude Mertens
bound and were not optimised.


## 2026-09-05 (later) — Brun's theorem with a bounded number of prime factors

The Brun–Hooley combinatorial sieve (Ford–Halberstam 2000) is now formalised and applied to
`n(n+2)`:

* `Sieve/BrunHooley.lean` — the pointwise inequality
  `∏ e_j ≥ ∏ U_j − ∑_j (U_j − L_j) ∏_{i≠j} U_i` for `L_j ≤ e_j ≤ U_j`, even/odd Bonferroni
  truncations, and the `Blocks` structure (pairwise coprime squarefree blocks with product `P`).
* `Sieve/BrunHooleySieve.lean` — expansion of block-sum products over tuples of block divisors
  (`sum_weights_prod_blockSumF`), factorisation of main terms by multiplicativity, the sieve
  inequality `siftedSum_ge_brunHooley`.
* `Sieve/BrunHooleyBounds.lean` — `|S_j − V_j| ≤ tail_j`, `0 ≤ T_j ≤ tail_j`, the main-term
  inequality `∏S − ∑ T ∏S ≥ (∏V)/2` under `∑ ε_j ≤ 1/8`, the remainder bound, and the **general
  Brun–Hooley lower bound** `siftedSum_ge_of_blocks`.
* `Sieve/BrunBlocks.lean` — blocks of primes by iterated square roots `t_{i+1} = ⌊√t_i⌋` (so the
  level `∏ t_i^{2k_i+1}` is a bounded power of `z`), block index via `Nat.findGreatest`, the
  uniform bound `∑_{p ∈ block} 1/p ≤ 16` from the dyadic Mertens estimate.
* `Sieve/BrunFinal.lean` — parameters `k_i = 120 + i`, `ε_i = e^{160} 2^{-(2k_i+1)}`, and the
  exact inequality `brunHooley_twin_count_ge`:
  `#{n ≤ x : n(n+2) coprime to primorial z} ≥ (x+1)e^{-96 r}/2 − (r+1) e^{4r} z^{972}`.
* `BrunBounded.lean` — with `z = ⌊x^{1/2000}⌋`: count `≥ x^{4/5}` for large `x`
  (`brunBounded_count_ge`), and **`brun_bounded_infinite`**:
  `{n : Ω n + Ω (n+2) ≤ 4001}.Infinite`.

This is the first formalisation (to my knowledge) of a Brun-type theorem with a *bounded*
number of prime factors for a twin-type pair.  Brun's own constant is `9 + 9 = 18`; ours is
`4001` because of the crude Mertens bound (constant `8` instead of `1`), the crude `∏(1−t) ≥
e^{−3∑t}`, and unoptimised `k_0 = 120`.  Improving the constant would be routine but long;
the structural content (bounded level ⇒ bounded `Ω`) is the point.  All files `sorry`-free,
standard axioms.

## 2026-09-05 (later still) — The parity obstruction as a Lean theorem

`TwinPrime/Parity.lean` (≈ 300 lines, `sorry`-free, standard axioms):

* `IsLowerMoebius μ⁻ := ∀ n, ∑_{d ∣ n} μ⁻(d) ≤ 1[n = 1]` (mirror of Mathlib's `IsUpperMoebius`)
  and the lower-bound sieve inequality `sum_lowerMoebius_le`:
  `∑_{d ∣ P} μ⁻(d) ∑_{d ∣ f n} a n ≤ ∑_{(P, f n) = 1} a n` for `a ≥ 0`.
* `prime_of_forall_prime_factor_gt`, `coprime_primorial_iff_twin`, `card_sifted_eq_twin`: for
  `z ≥ 3`, `z² > x + 2`, sifting `n(n+2)` by all `p ≤ z` leaves exactly the twin primes in
  `(z, x]`.
* **`parity_obstruction`**: for `z ≥ 3`, `z² > x`, and *every* `μ⁻` with `IsLowerMoebius μ⁻`,

      ∑_{d ∣ P(z)} μ⁻(d) · #{n ≤ x : d ∣ n(n+2)} ≤ ∑_{d ∣ P(z)} |μ⁻(d)| · |∑_{n ≤ x, d ∣ n(n+2)} λ(n)|.

  Proof: apply the sieve inequality to `a = 1 + λ(n) ≥ 0`, whose Type I data differ from those
  of the constant sequence by the Liouville sums `Λ_d`, and whose sifted sum vanishes because
  every sifted `n` is prime (`sum_one_add_liouville_sifted`).
* `parity_obstruction_level` (bounded weights of level `D`: right side `∑_{d ≤ D} |Λ_d|`),
  `parity_obstruction_general` (any `z`: bound by `2 #{sifted n : Ω(n) even}` + discrepancy),
  `sieve_expr_le_twin_count` (the same expression is a lower bound for `π₂(x) − π₂(z)`),
  and the mirror image `parity_obstruction_upper`: for every upper-bound sieve `μ⁺`
  (Mathlib's `IsUpperMoebius`), `2 (π₂(x) − π₂(z)) ≤ ∑ μ⁺(d) A_d + ∑ |μ⁺(d)| |Λ_d|`.
  A factor-two asymptotic conclusion requires a separate negligible-discrepancy estimate.

Numerics (`compute/parity/src/bin/liouville_disc.rs`, 28 s; cross-checked against a
brute-force Python computation at `x = 10⁶`): at `x = 10⁹`, over all squarefree `d ≤ 10⁴`,
`|Λ_d|/A_d ≤ 5.1·10⁻³` and `|Λ_d|/√A_d` has mean `0.76`, max `3.65` on the tested moduli.
These are finite observations. The former extrapolation `∑ |Λ_d| ≈ 2√(xD)` omitted
root multiplicities and logarithmic losses and proves no uniform asymptotic statement.
In current prose these discrepancies are called `D_d`, reserving `Λ` for von Mangoldt.

Meaning. For weights satisfying the stated lower-Möbius condition, the theorem bounds
the sieve expression by a discrepancy. No estimate for that discrepancy is part of the
theorem. Fixed-modulus estimates do not provide the rates and uniformity needed at a
growing level. Even an `o(x/log² x)` bound would exclude an expected-order sieve lower
bound, not every positive or unbounded bound. Bounding this upper comparison does not
prove a twin-prime lower bound. The current program isolates a separate signed estimate.

### Honest statement of position

No approach known to the author (sieve, circle method, or any combination) proves the conjecture;
the parity barrier blocks all pure-sieve routes and the circle method lacks the needed minor-arc
control. The plan therefore pushes formal verification to the frontier of what *is* known
(Brun), records the obstruction as a precise mathematical statement, and uses computation to
test any candidate idea before time is spent on it.

## 2026-09-04 — Execution of the revised proof program

The append position preserves the original entries' dates. The source baseline is
`5cf66a63bbc33b36f3c8d90373d2f6cce108f72a`; subsequent entries record later developments.

Implemented the corrected parity interpretation and repaired the twin sieve's odd
endpoint, including its reciprocal sum. Repeated checkpoint counts now agree at
final limits 5 and 6: π₂(5)=2 and S(5)=0.876190476190476. Parity ratios with zero
denominators now show `inf` or `undefined`. Existing data and release binaries were
preserved; repaired release builds are under each crate's `target/verified`.
The Rust test suites passed 7 twin-sieve tests and 6 parity tests.

Added seven Lean modules: `Correlation`, `Analytic.Vaughan`,
`Analytic.TruncatedMangoldt`, `Analytic.Decomposition`, `Analytic.Cutoff`,
`Analytic.FactorRanges`, and `ConditionalBilinear`. They prove the exact dyadic
endpoint, sublinear prime-power error, finite cutoff decomposition, coefficient
bounds, explicit progression and factor-pair sums, and the conditional budget.
The fixed-cutoff theorem `twinPrimeConjecture_of_primary_estimates` retains exactly
the mixed, Type I, and signed bilinear estimates as analytic hypotheses.

`python -m unittest discover -s compute -p test_correlation.py -v` passed 6 tests,
including 8,000 exact Vaughan identities. The independent exact-coefficient
diagnostic reproduced the plan's three finite examples at X=1000,10000,100000;
all decomposition residuals and factor-box coverage checks passed exactly.
Displayed logarithmic values use binary64 and are not interval certificates.
Results and provenance are saved under `compute/correlation_results/2026-09-04`.

[ANALYTIC_REVIEW.md](ANALYTIC_REVIEW.md) identifies the classical source inputs,
checks the shared-prime correction on paper, and expands the first dispersion
attempt. Its diagonal admits a paper bound; the required signed off-diagonal
correlation remains unproved. No new estimate supplies the positive margin in (B*).

[PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) is the current status ledger.
M0 and M2 are implemented, M1 remains partial because formula (Q) is not yet a
general Lean theorem, and M3–M6 remain incomplete. The full proof goal is not
satisfied. No unconditional twin-prime theorem has been added.

Final integrated verification: `lake build` passed (8686 jobs), and
`lake env lean scripts/Axioms.lean` passed with only the three standard axioms
for all 46 audited declarations. The printed final theorem type preserves its
three analytic hypotheses. A 31-file source scan found no proof placeholders,
new axioms, `native_decide`, `unsafe`, or `implemented_by`.

## 2026-09-04 — Classical applications and the exact totient correction

Completed M1's remaining finite formula (Q) in `Analytic.MoebiusTotient`,
including the noncoprime totient correction and the exact recurrence for Fₚ.
`MoebiusTotientAsymptotics` proves the full shared-prime correction tends to
zero from F→0 when U→∞, without a restriction on V. The proof uses the
uniform bound |Fₚ|≤M/(p−2) and a summable prime-power majorant.
`TotientMainAsymptotics` bounds the odd Λ/φ sum by 6log²(V+1) and derives
Q(U,U)→0 from the single explicit input F(t)log²(t+1)→0.

Added the exact integer-endpoint progression API and a named, unproved
maximal Bombieri–Vinogradov input. Proved the cutoff range and logarithmic
loss estimates, even-modulus exception bounds, weighted A and I estimates,
discrete partial summation, and the H estimate. H uses the exact discrete
main mass, so no integral approximation is left unstated. The resulting
`tendsto_typeICorrection_div_of_inputs` derives K/X→0 from BV and logarithmic
Möbius cancellation. The new endpoint
`twinPrimeConjecture_of_classical_inputs_and_bilinear` exposes exactly BV,
the smoothed limit with constant 2C₂, F(t)log²(t+1)→0, and the cofinal signed
bound B*. None of those four assumptions has been proved by this work.

`BilinearSign` formalizes coefficient identities on primes, prime powers,
and rough numbers. The [sign review](BILINEAR_SIGN_REVIEW.md) gives a paper
o(X) bound for the proper-prime-power exceptional subrange, but the complete
assembled bound is not yet a Lean theorem and does not control the main
composite contribution. [FAILED_APPROACHES.md](FAILED_APPROACHES.md) now
includes exact finite counterexamples to a universal pointwise −log n bound,
a nonpositive off-diagonal claim, and a positive margin inferred only from
finite Type I moments. The three-point switch is explicitly a model, not the
actual von Mangoldt sequence or an asymptotic BV counterexample.

Integrated verification: full `lake build` passed (8700 jobs). All 82 axiom
audits passed using only the three standard axioms, and the printed endpoint
type retains its four hypotheses. All 45 project Lean files were scanned for
proof holes or trust bypasses; none was found. Eleven Python correlation/sign
tests passed, as did the focused exact Type I switch checker. Independent
review found no mathematical/type mismatch in the H/Q/K reductions.

Current status: M0–M2 implemented, M3 partially implemented, M4–M6 incomplete.
The goal is not satisfied. Classical BV and the two Möbius/totient limits
still require Lean proofs, and the signed fixed-shift estimate B* remains
the missing mathematical breakthrough.

## 2026-09-04 — Ordinary Mertens reduction, exceptional removal, and rough parity

The classical reductions now need just one ordinary Möbius input:
`MertensLogSix`, the eventual bound `|M(t)| ≤ Kt/log⁶t` for some K≥0.
`MoebiusHyperbola` proves from the exact hyperbola identity that M(t)/t→0
implies the ordered reciprocal sum S(t)→0. `MoebiusAbel` gives explicit
log⁻⁵ reciprocal tails. `MoebiusBoundary` uses harmonic convolution and
discrete partial summation to prove the smoothed constant 1 and logarithmic
moment −1 from the same Mertens input. No boundary constant or unconditional
summability of μ(n)/n is assumed.

`MoebiusSmoothing` proves the exact convolution bridge to the odd μ/φ sums,
retaining real division inside the smoothed logarithm. `SmoothingSummability`
proves the correction's absolute, square-root-weighted, and logarithmically
weighted summability and evaluates its signed sum as 2C₂. `SmoothingLimits`
transfers both ordinary limits by dominated convergence. `MertensReduction`
packages these results, including A/X→2C₂ and K/X→0 after adding BV.
The new endpoint `twinPrimeConjecture_of_bv_mertens_and_bilinear` has exactly
three hypotheses: maximal BV, `MertensLogSix`, and the cofinal signed bound B*.
The two classical inputs remain unproved in Lean; B* remains mathematically open.
See [CLASSICAL_REDUCTION.md](CLASSICAL_REDUCTION.md) for the proof map.

`DivisorGrowth` proves τ(n)³≤4096n and hence τ(n)≤16n^(1/3).
`BilinearExceptional` uses this to show that restricting B to non-prime-powers
n with prime n+2 changes the sum by o(X), uniformly in eventually positive
cutoffs. With Y=2X+2, the formal estimate is
`|B−Bprime| ≤ (2/log2)Y^(1/2)log³Y + 32Y^(5/6)log²Y`.
It differs from the stronger exponent-3/4 absolute-mass estimate in the paper
sign review. The main composite contribution and its required margin remain
uncontrolled.

`RoughParity` proves the finite prime-or-semiprime classification, including
prime squares, and `4N₂=S−L₀−L₂+L₀₂` under the precise cube-root roughness
conditions. Its alternative conditional endpoint keeps both the rough-count
lower bound and parity estimate visible. The
[asymptotic-sieve application review](ASYMPTOTIC_SIEVE_REVIEW.md) checks the
Friedlander–Iwaniec hypotheses against the shifted prime sequence. That route
requires a distribution range beyond exponent 2/3 as well as a different
bilinear estimate; it does not follow from BV or silently establish PLAN's B*.

Integrated verification: full `lake build` passed (8710 jobs). All 121 selected
axiom audits passed using only the three standard axioms. The printed newest
endpoint retains its three hypotheses. A scan of all 55 project Lean files
found no proof holes, project axioms, `native_decide`, `unsafe`, or
`implemented_by`. Independent mathematical reviews found no mismatch in the
hyperbola normalization, harmonic boundary proof, smoothing limits, exceptional
removal, or rough-parity identity. Computational source did not change during
this stage; the previously passed regression suites remain the recorded checks.

Current status: M0–M2 implemented; M3 has the classical applications and all
displayed Möbius/totient bridges, but still needs proofs of BV and quantitative
Mertens. M4–M6 remain incomplete. No unconditional twin-prime theorem has been
added, and the full proof goal is not satisfied.

## 2026-09-04 — Signed dispersion and an elementary prime-to-Mertens route

The previous stage made verified progress; the twin-prime conjecture remains unproved.
Reinspection confirmed that the newest checked endpoint still had the three
explicit arguments BV, `MertensLogSix`, and B*. This stage addressed both
the classical dependency and the first signed dispersion calculation.

`Analytic.Dispersion` identifies each box with the exact corresponding
restriction of `bilinearPairs`. It proves weighted Cauchy–Schwarz with the
full signed off-diagonal, including both orientations and both hyperbolic
cutoffs. Its finite diagonal estimates are
`M*T*D <= (2X)^2 log^4(4X+4)` and, for `U<=2M`,
`T*D/X^2 <= 8 log^4(4X+4)/U`.
`DispersionGrowth` absorbs every fixed logarithmic power in the primary
cutoff. Together these give a Lean theorem that the square-root diagonal
contribution is o(X), even with any fixed logarithmic loss, along every
geometrically admissible box sequence. This is a per-box result; a full
dyadic partition and the signed off-diagonal estimate are not supplied.
Independent review confirmed the signs, constants, and theorem scope.

The [prime-to-Mertens paper proof](PNT_MERTENS_REDUCTION.md) gives a useful
reduction of the classical prerequisites. From `psi(x)=x+O(x/log^6 x)`,
partial summation constructs c with `sum Lambda(n)/n=log x+c+O(log^-5 x)`.
The centered coefficient `a=Lambda*Lambda-Lambda log-2c*1` has summatory
error O(x/log^5 x) and absolute reciprocal mass O(log^2 x).
The exact identity `mu*a=mu log^2-2c epsilon`, a second hyperbola split,
and a weighted finite-supremum contraction then prove Mertens log^6 decay.
The proof uses no assumed Möbius cancellation or inverse-zeta boundary value.
It has been independently checked on paper.

`BombieriVinogradovPsi` formally extracts the prime estimate from modulus
one of the existing BV hypothesis, including all integer endpoints through
`2X+2`. `MoebiusSelberg` formally proves the logarithmic Leibniz rule and
the centered convolution identity, including its finite divisor-pair form.
The real-endpoint transfer, centered analytic estimates, and contraction
remain to be formalized. Consequently the checked twin-prime endpoint
still keeps Mertens as a separate argument; no paper proof was inserted as
a Lean assumption or axiom.

The [Chen-weight review](CHEN_WEIGHT_REVIEW.md) selects the positive part of
the actual Chen minorant at roughness x^(1/8), retaining the square and
triple corrections. Its exact mass is `T+E/2+B`, with squares in the balanced
semiprime term B. The source lower coefficient is
`kappa=2(log(3/2)-J)>0`, but the compatible leakage upper coefficient
`2log6+4` gives the negative difference `-4log2-2J-4`.
A zero-twin assignment satisfies the listed aggregate constraints; it is
explicitly not a prime model or full BV counterexample. The selected
weight therefore has no demonstrated improvement for the new parity input.
Small exact checks covered 1,129 shifted values and seven mass/parity
identities, and rational logarithm bounds certified positivity of kappa.
No large enumeration or computational source change was made.

Integrated verification: full `lake build` passed (8714 jobs), and all 139
selected axiom audits passed with only `propext`, `Classical.choice`, and
`Quot.sound`. Printed types retain the original three endpoint hypotheses,
the complete signed off-diagonal, and the geometric assumptions of the
diagonal limit. All 59 project Lean files passed the source scan for proof
holes, project axioms, and trust bypasses. Existing older linter warnings
remain; the new modules produced none.

The next classical implementation step is the analytic prime-to-Mertens
implication just proved on paper. The principal mathematical gap is still
B*: neither the diagonal saving nor the Chen-weight assessment controls
the remaining signed contribution to its required margin. M3, M4, and M6
are incomplete, and the full proof goal is not satisfied.

## 2026-09-04 — Formal components of the elementary prime-to-Mertens argument

The previous goal turn was verified progress. Reinspection confirmed the
same three-argument conditional endpoint and the paper implementation map.
This stage added seven Lean modules for that selected classical argument.

`PrimeReal` extends an integer prime-error estimate to real endpoints,
retaining its logarithmic exponent and absorbing the floor discrepancy
with explicit constant `2^k K+1`. `PrimeReciprocal` applies the existing
generic Abel theorem to `Lambda(n)-1`, constructs a centering constant c,
and gives reciprocal remainder `((32+2/log2)K+1)/log^5 N`.
`PrimeReciprocalReal` bounds the floor-log discrepancy by `2/x` and retains
the same c at real endpoints, changing a remainder constant C to `32C+2`.
The prime estimate remains a consequence of the explicitly assumed BV;
no prime-number theorem or value of c was assumed as a new axiom.

`Hyperbola` proves the general integer convolution decomposition under
`Y*Z<=X<(Y+1)*(Z+1)` over any commutative ring, including zero cutoffs.
Its real version uses `yz=x`, floors only summation cutoffs, and retains
real ratios inside the summatory functions. `SelbergSummatory` instantiates
the actual prime square-root convolution and the Möbius-centered identity,
including the term `-2c` and the exact overlap rectangle.

`SelbergCoefficientBounds` proves, using only elementary Chebyshev bounds,
`sum_{n<=N}|a(n)|/n <= D(2+log N)^2`, where
`D=(log4+4)^2+(log4+4)+2|c|`. The paper used a slightly sharper shifted
logarithm; the formal bound has the same limiting contraction coefficient
when the head cutoff is x^delta. It does not bound the signed summatory
function A(x).

`SupremumContraction` proves that local upper bounds and an eventual
inequality `f(x)<=theta*sup_{a<=t<=x}f(t)+E`, with `0<=theta<1`, imply a
global upper bound. For nonnegative f it also supplies an absolute bound.
The proof neither assumes a globally bounded supremum nor requires it to
be attained. It does not establish the contraction inequality for Möbius.

Integrated verification: full `lake build` passed (8721 jobs). The selected
axiom audit passed for all 157 declarations, with only `propext`,
`Classical.choice`, and `Quot.sound`. Printed types retain the final
endpoint's three arguments and the arithmetic-free hypotheses of the
general supremum lemma. All 66 project Lean files passed the source scan
for proof holes, project axioms, `native_decide`, `unsafe`, and
`implemented_by`. New modules check without linter warnings; older warnings
are unchanged. Computational sources were not changed or rerun.

The remaining steps of this classical reduction are now explicit: prove
the logarithmically weighted prime estimate and centered signed error
`A(x)=O(x/log^5 x)`, bound the tail and overlap in the Möbius hyperbola,
and derive the actual normalized Möbius contraction before applying the
general absorption theorem. The [implementation map](PNT_MERTENS_REDUCTION.md)
tracks these obligations. The checked endpoint still assumes Mertens
separately, BV itself remains unproved here, and the new signed estimate B*
remains open. The full proof goal is not satisfied.

## 2026-09-04 — Complete Lean reduction from BV to quantitative Mertens

The previous goal turn was verified progress. This stage added eleven Lean
modules and completed the selected BV-to-Mertens argument. The new theorem
`MaximalBombieriVinogradov.mertensLogSix` has only the named BV hypothesis.
`twinPrimeConjecture_of_bv_and_bilinear` consequently has just BV and the
cofinal signed B* estimate as arguments; the earlier endpoints remain available.

`LogFactorial` bounds the error in the finite sum of logarithms by the
harmonic sum. `PrimeLog` uses discrete partial summation with BV's maximal
ordinary error to obtain the weighted prime main term `x log x - x` with
error `O(x/log^5 x)`, including real endpoint corrections. Together with
the existing prime and reciprocal estimates, `SelbergCenteredError` and
`PrimeToSelberg` prove the centered signed summatory error `A(c,x)=O(x/log^5 x)`.
The constant c is constructed by the reciprocal sum, and the floor term
`2c(x-floor x)` is retained explicitly.

`SelbergMoebiusError` controls the second hyperbola strip and overlap with
only `|M(x)|<=x`, giving the required `O(x/log^4 x)` remainder at a fixed
power cutoff. `LogKernel` proves the natural reciprocal-log kernel bound
with constant `1+14^5`. `MoebiusLogWeight` proves exact discrete unweighting
and its real extension, including the final fractional interval. This
preserves coefficient one on the weighted Möbius sum and contributes
`[128(1+14^5)+4]W(x)/log x` after normalization.

`WeightedMertens` proves local boundedness of the actual weighted supremum
and bounds the short hyperbola head using the proved absolute coefficient
mass. `ContractionParameters` fixes delta after that mass constant.
`MertensContraction` establishes the actual eventual contraction, applies
the checked absorption theorem, and restricts its global bound to natural
endpoints. `PrimeToMertens` discharges its centered-error premise from BV.
No global supremum bound or Möbius cancellation is assumed in this chain.

Scope: the formal statement is BV implies MertensLogSix. The broader
ordinary eventual prime-error implication in equation (1) of the paper
note remains a paper result, since the formal weighted-prime step directly
uses BV's maximal ordinary error. An independent review found no gap in
the assembled signs, real floors and logarithms, or local supremum argument.

Verification: full `lake build` passed (8732 jobs). The integrated axiom
audit passed for 190 selected declarations, using only `propext`,
`Classical.choice`, and `Quot.sound`. The printed endpoint type has exactly
BV and B*. A source scan of all 77 project Lean files found no proof holes,
new axioms, `native_decide`, `unsafe`, or `implemented_by`. New modules have
no linter warnings; existing older warnings are unchanged. Computational
sources were unchanged and their suites were not rerun.

M3 still requires a proof of the named BV theorem in Lean. The signed B*
estimate still requires new mathematics, and no unconditional twin-prime
theorem has been obtained. M4–M6 and the full proof goal remain incomplete.

## 2026-09-04 — Finite character foundations for maximal BV

The previous goal turn was verified progress: BV-to-Mertens was completed
in Lean and the refined endpoint retained BV and B*. Reinspection confirmed
that no quantitative BV, Siegel–Walfisz, or large-sieve theorem is available
in the pinned library. This stage adds seven modules toward the remaining
classical theorem, without changing the two-argument twin-prime endpoint.

`CharacterSums` proves the exact character expansion of a reduced
progression and identifies the principal-character correction.
`CharacterMaximal` subtracts the principal linear term and bounds the
actual progression maximum by the sum of centered character maxima over
every integer endpoint through T. No principal character is discarded.

`CharacterExceptions` bounds the noncoprime mass by
`log q+2sqrt(T)log T`: the excluded primes divide q and the other terms
are bounded by the existing ψ−θ estimate. Replacing a character by its
inducing primitive character costs at most this mass. `CharacterPrimitiveReduction`
proves that principal status is preserved, transfers the endpoint maxima,
and sums the error over moduli. The character count φ(q) cancels its
averaging denominator exactly. Primitive inducing multiplicities remain
explicit in the resulting sum; conductor regrouping is not yet proved.

`CharacterExceptionGrowth` bounds the accumulated error at T=2X+2 by
`13 Q sqrt(X) log X`. With Q≤sqrt(X)/log^(A+2)X and log X≥13, it is at
most X/log^A X. The eventual theorem is uniform over Q and independently
selected endpoints at every modulus. The combined progression reduction
now uses the exact endpoint and logarithmic range of the BV obligation.

`PrimitiveGauss` proves |τ(χ)|²=q for all positive moduli, including
composite q and q=1, using the pinned finite double Fourier transform.
`CharacterLargeSieveTransfer` establishes unit-group orthogonality and
Parseval, the exact Gauss factorization, and the finite q/φ(q) transfer
inequality for arbitrary finite coefficient sums. The additive large-sieve
estimate itself is not assumed or asserted in that theorem.

The source-backed [BV implementation note](BV_REDUCTION.md) identifies the
remaining conductor regrouping, additive large sieve, maximal bilinear
mean values, and uniform small-conductor input. An independent review
found no mismatch in principal centering, zero endpoints, modulus one,
primitive multiplicities, inverse conventions, or error normalization.

Verification: full `lake build` passed (8739 jobs); all 226 selected axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Type
inspection confirms that the twin-prime endpoint still has BV and B* as
arguments and that the new finite transfer has no analytic premise. All
84 project Lean files passed the source scan for proof holes, project
axioms, `native_decide`, `unsafe`, and `implemented_by`. New modules have
no linter warnings. Older warnings and computational sources are unchanged;
the computational suites were not rerun.

The remaining BV work is substantial established analysis. B* still
requires new mathematics. Neither BV nor an unconditional twin-prime
theorem has been proved, and the full proof goal remains incomplete.

## 2026-09-04 — Conductor weights and a large sieve with harmonic loss

`CharacterConductor` proves exact regrouping by primitive conductor,
including the principal character of conductor one and all its inducing
multiplicities. `TotientReciprocal` defines the correction
`h=(μ/n)*(1/φ)`, proves `h(p)=1/(p(p−1))` and `h(p^k)=0` for k≥2,
and obtains absolute summability from the excess bound `2/p²`.
The exact harmonic convolution gives
`Σ_{n≤N}1/φ(n)≤Cφ(1+log N)` for a fixed `Cφ≥1`. Totient
supermultiplicativity then proves
`Σ_{k≤Q/r}1/φ(rk)≤Cφ(1+log Q)/φ(r)`.

`ConductorReduction` applies these results at the exact maximal BV
endpoint, with its existing absorbed replacement error. `ConductorAbel`
proves the finite tail bound
`Σ_{R₀<r≤Q}a(r)/r≤A/R₀+B(1+log(Q/R₀))+2DQ` from a nonnegative
cumulative quadratic bound. Its exact identity also covers R₀=Q.

The additive large-sieve proof is now constructed from finite ingredients.
`AdditiveKernel` uses the geometric series and Jordan's inequality to
bound the interval kernel by `min(N−M,1/(2‖θ mod1‖))` off the diagonal.
`FiniteLargeSieve` proves Schur's finite inequality and Cauchy–Schwarz
duality for complex matrices. `SeparatedReciprocal` orders separated
positive points and splits signs to bound reciprocal mass by harmonic
sums. `AdditiveLargeSieve` applies this to centered circle representatives,
proves the actual Gram row bounds, and obtains constant
`N−M+H_card/δ`. `RationalFrequencySeparation` proves 1/(qr) spacing
and uniqueness of reduced unit frequencies, including q=1.
`RationalLargeSieve` builds the complete unit-frequency family, proves
the phase bridge to the standard additive character, and sums the Gauss
transfer. Its rational additive and primitive-character second-moment
estimates have exact constant `N−M+Q² H_(Σ_{q≤Q}φ(q))` and the proved
upper bound `N−M+Q²(1+2log(Q+1))`, valid also for Q=0 and empty intervals.
The character inverse convention remains explicit.

An independent review found no missing multiplicity, principal term,
phase sign, inverse convention, or empty-range exception. It also
identified an essential bookkeeping distinction: the harmonic large
sieve has a logarithmic loss compared with the sharp classical version.
The remaining maximal Vaughan proof must carry this loss explicitly;
its logarithmic exponent has not yet been proved. The
[BV implementation note](BV_REDUCTION.md) now uses a generic fixed
exponent K when describing the remaining assembly.

The maximal product-cutoff bilinear estimate, Type I character bounds,
coefficient estimates, and uniform Siegel–Walfisz still require proofs.
The conductor-one prime error must be established independently of BV;
using the existing BV-derived estimate would be circular. These classical
steps do not resolve B*, and no unconditional twin-prime theorem is claimed.

Verification: full `lake build` passed (8749 jobs); all 279 selected axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The printed primitive-character large-sieve type has no analytic premise;
the twin-prime endpoint still requires BV and B*. All 94 project Lean
files passed the source scan for proof holes, project axioms, `native_decide`,
`unsafe`, and `implemented_by`. The ten new modules check without linter
warnings. `git diff --check` passed. Older lints and computational sources
are unchanged, so the computational regression suites were not rerun.
The twin-prime conjecture remains unproved.

## 2026-09-04 — Character cancellation, adaptive dyadic sums, and the exact staircase

`CharacterInterval` proves the unconditional Pólya–Vinogradov bound
`norm(Σ_{M≤n<N}χ(n))≤sqrt(q)H_q≤sqrt(q)(1+log q)` for primitive
characters at every q>1. Same-modulus residue spacing is 1/q, and the
Gauss factorization reduces the interval sum to the already checked
additive kernels. Composite q and empty intervals are included. Modulus
one remains in the separate small-conductor work.

`CharacterLogInterval` proves complex finite Abel summation and the
logarithmic prefix bound `2sqrt(q)(1+log q)log T`, including T=0.
Uniform shorter-prefix and clipped Type I outer-sum bounds follow.
`CharacterBilinear` proves primitive inversion reindexing, the direct
large-sieve convention, weighted Cauchy–Schwarz, and actual rectangular
bilinear first-moment estimates in both character conventions.

`DyadicMaximal` introduces the complete binary-tree energy. Each prefix
costs a factor k+1, while the weighted tree energy costs another k+1
from the fixed-interval second moment. `DyadicIntervalCover` constructs
exact interval covers with at most 2(k+1) blocks, proves containment and
no shared block across disjoint target intervals, and derives actual
adaptive disjoint-interval variation with loss 2(k+1)². The number of
intervals does not enter the bound.

`CharacterMaximalLargeSieve` applies these proved inequalities to the
primitive-character family. It allows endpoints and disjoint finite
interval families to depend on each character. Its maximal-prefix
theorem chooses an actual finite maximizer inside each character sum;
no maximal estimate is a new assumption.

`DyadicStaircase` proves the exact identity for a nonincreasing boundary
and its specialization to `min(N+K,max(N,T/m+1))`, preserving `mn≤T`.
It includes T=0, N=0, K=0 and requires only a positive m-interval start.
The [maximal Type II note](BV_MAXIMAL_ROUTE.md) derives the remaining
combination by staircase depth and the Vaughan box estimates on paper.
An independent review checked the constants, adaptive endpoints, no-reuse
injection, last-index boundaries, and logarithmic budget. The combined
maximal product-cutoff first moment and Vaughan assembly still require
formal proofs; uniform Siegel–Walfisz and B* remain unresolved.

Verification: full `lake build` passed (8756 jobs). All 325 selected axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
Type inspection confirms that the maximal character theorem has no analytic
premise; the disjoint-family theorem has only its explicit finite validity
and disjointness conditions. The twin-prime endpoint still requires BV and
B*. All 101 project Lean files passed the source scan for proof holes,
project axioms, `native_decide`, `unsafe`, and `implemented_by`. The seven
new modules check without linter warnings. `git diff --check` passed.
Older lints and computational sources are unchanged; computational suites
were not rerun. The twin-prime conjecture remains unproved.

## 2026-09-04 — Maximal bilinear first moments and the full finite Type II mean

Fifteen new Lean modules complete the finite maximal Type II chain.
`IntervalFamilyLargeSieve` sums a fixed disjoint family without a depth or
interval-count loss. `WeightedBilinear` proves the nested weighted
Cauchy–Schwarz inequalities and the explicit baseline-plus-level constant.
`DyadicStaircaseGeometry` proves disjointness of equal-height nodes, their
left children, and the antitone-boundary correction intervals.
`DyadicStaircaseLevels` groups every internal correction exactly once.

`DyadicStaircaseFirstMoment` combines the proved second moments into a
first moment for arbitrary character-dependent antitone boundaries.
`CharacterMaximalBilinear` applies it to the actual primitive-character
family and exact product cutoff. Each character may select any natural
cutoff; choosing an actual finite maximizer gives the maximal theorem.
Its loss is `2(k+1)(j+1)`, and only the first interval start must be positive.
The inverse-character version is also proved. No analytic hypothesis has
been added in place of the missing maximal estimate.

`BilinearBoxPolynomial` proves the scalar box polynomial and its
`C=Q²L` specialization. `VaughanBoxCoefficients` retains the strict lower
cutoffs and common upper cutoff and proves both dyadic energy budgets.
`DyadicNatPartition` and `DyadicBilinearPartition` give exact global
power-of-two partitions. This avoids silently treating arbitrary cutoffs
as power-of-two box lengths.

`CharacterVaughan` proves the exact Type II pair identity and full Vaughan
character identity, retaining `characterPsi (min t V) χ` as the low term.
`CharacterVaughanBox` applies the maximal bilinear theorem to the actual
masked coefficients. `VaughanActiveBoxes` proves discarded box sums and
maxima vanish and derives the half-cutoff, product, cardinality, and depth
bounds. `CharacterVaughanDyadic` proves the exact active-box identity and
controls the full Type II maximum by active box maxima.

Finally, `CharacterVaughanMean` proves

```text
Σ_{q≤Q} (q/φ(q)) Σ_{χ primitive} max_{0≤t≤T}|S_II(t,χ)|
 ≤ 2D⁴ log(T)L_Q [T + QT(1/√(U/2)+1/√(V/2)) + Q²√T],
D=clog 2 (T+1),  L_Q=1+2log(Q+1).
```

Only U,V>0 are assumed. The finite theorem includes Q=0 and T=0,1;
the inverse-character mean also checks. An independent review confirmed
the support masks, low term, exact maxima, inactive-box removal, and the
two separate D² factors. The full von Mangoldt mean and BV remain unproved.

The new [Type I route](BV_TYPEI_ROUTE.md) changes the next implementation
step. Direct PV with cube-root cutoffs loses excessive powers at R≈√T.
Choosing BV-internal cutoffs `floor(T^(1/8))` instead makes the direct
Type I budgets small enough and leaves the sufficient Type II exponent
15/16. The paper derives an explicit combined target with a sixth power
of log T, uses the existing exact character-cardinality API, and records
the needed finite Type I identities, weighted counting, and floor/log
comparisons. Those steps still need Lean proofs. Uniform Siegel–Walfisz,
including conductor one, must be proved independently; B* is unchanged.

Verification: the full root build passed (8771 jobs), and all 376 selected
axiom reports passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Type inspection confirms that the Type II theorem requires only U,V>0;
the twin-prime endpoint still has exactly BV and B* as hypotheses. The
source scan covers 116 project Lean files without proof holes, project
axioms, `native_decide`, `unsafe`, or `implemented_by`. All fifteen new
modules check without linter warnings. Older lints and computational
sources are unchanged, so computational suites were not rerun. The goal
remains active and incomplete.

## 2026-09-04 — Full maximal character mean and centered conductor tail

Eleven new Lean modules implement the Type I route and complete the finite
Vaughan mean. `CharacterVaughanTypeI` proves both exact positive-divisor
factorizations with natural quotient endpoints and the full four-term identity.
`CharacterTrivialBounds` supplies the low-term and conductor-one bounds, actual
finite maxima, and the exact centered-to-uncentered bridge for nonprincipal
characters. `CharacterTypeIBounds` applies the proved uniform primitive
Pólya–Vinogradov estimates to both Type I sums and their maxima.

`PrimitiveCharacterCounting` proves exact character cardinality and the weighted
primitive counting bounds. `CharacterTypeIMean` combines Type I, the low term,
conductor one, and the previously proved maximal Type II estimate. No
cancellation estimate is applied to the principal character of conductor one.

`BVInternalCutoffs`, `BVLogComparisons`, and `VaughanMeanParameters` prove the
floor, square-root, power, depth, and logarithmic comparisons at the internal
cutoff `W=floor(T^(1/8))`. `VaughanMeanValue.primitive_character_mean_value`
then proves, for `T≥256` and `1≤R≤sqrt(T)`,

```text
Σ_{1≤q≤R} (q/φ(q)) Σ_{χ primitive} max_{0≤t≤T}|Σ_{0<n≤t}Λ(n)χ(n)|
 ≤ C₀ [T + T^(15/16)R + sqrt(T)R²] log⁶T,
C₀ = 5 + 16(2/log2)⁴.
```

This is a proved mean-value theorem with only the stated numerical conditions.
The maximum remains inside each character sum. The exponent 15/16 suffices
for a future BV deduction; the twin-correlation cutoff remains unchanged.

`ConductorMean` bridges the actual centered primitive mass for conductors
greater than one to the proved cumulative mean. The instantiated theorem
`sum_large_primitiveCharacterMass_le` gives, for `1≤R₀≤Q≤sqrt(T)`,

```text
Σ_{R₀<r≤Q} primitiveCharacterMass(T,r)/φ(r)
 ≤ C₀ log⁶T [T/R₀ + T^(15/16)(1+log(Q/R₀)) + 2sqrt(T)Q].
```

The three coefficients used in finite Abel summation are fixed in T.
`SmallConductorMean` proves the complementary counting bound from an explicit
uniform centered-error hypothesis. The finite progression criterion now
combines both parts and includes Q=0 and Q<R₀ via `min(R₀,Q)` and a conditional
tail. It does not assert or assume that the small-conductor hypothesis has
already been proved.

Independent review checked Type I support, natural quotients, exact counts,
conductor one, endpoint maxima, cutoff constants, logarithmic losses, and
conductor-summation ranges. The new [small-conductor source audit](SIEGEL_WALFISZ_ROUTE.md)
records the analytic continuation, nonvanishing, and logarithmic-derivative
APIs present in the pinned Mathlib, and the missing uniform quantitative
steps. Qualitative nonvanishing does not supply Siegel–Walfisz. An independent
uniform small-conductor estimate, asymptotic absorption at T=2X+2, and the
fully quantified BV conclusion remain. The signed fixed-shift bound B* is
unchanged and open.

Verification: the full root build passed (8782 jobs). All 421 selected axiom
reports passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Printed types confirm the numerical-only assumptions of the full mean and
large-conductor tail, the explicit small-conductor hypothesis of the finite
progression criterion, and exactly BV and B* at the final twin-prime endpoint.
The source scan covers 127 project Lean files without proof holes, project
axioms, `native_decide`, `unsafe`, or `implemented_by`. All eleven new modules
check without linter warnings. Older lints and computational sources are
unchanged; computational suites were not rerun. The full proof goal remains
active and incomplete.

## 2026-09-04 — Complete SW-to-BV assembly and finite Dirichlet tails

Seven new Lean modules complete the conditional classical distribution
assembly and begin the independent analytic small-conductor work.
`SiegelWalfisz` defines the exact pointwise and maximal centered statements
with positive real logarithmic exponents, uniform constants and natural
thresholds, and every primitive conductor including one. These are
propositions, not asserted theorems or new axioms.

`SiegelWalfiszMaximal` proves the uniform pointwise-to-maximal implication.
Endpoints through `T/log^(A+2)T` use the elementary centered bound
`t log t+t`. Larger endpoints are eventually above both sqrt(T) and the
pointwise threshold, and satisfy `log T≤2log t`. Increasing the conductor
exponent from B to B+1 makes the pointwise condition valid at every such t.
The chosen constant is `max(2,C*2^A)`. No endpoint or conductor is allowed
to select a separate threshold.

`BVConductorGrowth` proves the actual outer-weighted conductor tail is
at most `Ktail X/log^A X` at T=2X+2, uniformly over admissible R₀,Q,
with `Ktail=768CφC₀+1`. The finite proof retains the numerical margin
`log^(A+8)X≤X^(1/16)`, proved eventually from logarithm-versus-power growth.
`BVSmallConductorGrowth` chooses `R₀=ceil(log^(A+9)X)`, proves its range
inside `log^(A+10)(2X+2)`, and absorbs the small mass and outer logarithm
from a centered SW estimate with error exponent `2A+12`. It also checks
both the finite mean's square-root range and the replacement-error range.

`BombieriVinogradovFromSW` assembles these results into the exact
`MaximalBombieriVinogradov` proposition from either maximal or pointwise
SW. The modulus exponent is B=A+9; the combined constant is
`12CφC+Ktail+1`. The threshold is chosen before Q, and Q=0 and Q<R₀
are included. The new `ConditionalSiegelWalfisz` endpoint consequently
derives twin-prime infinitude from centered pointwise SW and the unchanged
signed B* hypothesis. The former BV+B* endpoint remains available.
Independent pointwise SW itself is still unproved.

`CharacterDirichletTail` proves an actual analytic ingredient independently
of any distribution hypothesis. Complex-power variation and finite Abel
summation give, for primitive χ modulo q>1, 1≤M≤N, and σ=Re(s)>0,

```text
|Σ_{M<n≤N} n^(-s)χ(n)|
 ≤ sqrt(q)(1+log q) M^(-σ) (1+|s|/σ).
```

The same estimate proves Cauchy convergence of ordered partial sums on
σ>0 and a quantitative bound from every positive M to their limit.
For σ>1, absolute L-series convergence identifies that limit with
`LFunction χ s` and gives the corresponding L-function truncation bound.
No absolute or unconditional summability is asserted on the larger
half-plane. Local uniform convergence, holomorphy and identification on
σ>0, the principal ζ truncation, and the later zero-free, exceptional-zero,
and quantitative inversion steps still require proofs.

Independent reviews checked the cutoff powers, all constants and threshold
quantifiers, principal centering, short endpoints, empty tail cases,
complex-power variation, exact finite Abel endpoints, and the scope of
the ordered-limit and L-function identifications. No circular BV/Mertens
input was found in the SW-to-BV chain. The full conjecture remains open
in this repository because independent SW and B* are still missing.

Verification: the full root build passed (8789 jobs), and all 441 selected
axiom reports passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Printed types retain precisely pointwise SW and B* in the newest twin-prime
endpoint, SW in each BV implication, and the actual half-plane restrictions
in the character-series theorems. The source scan covers 134 project Lean
files without proof holes, project axioms, `native_decide`, `unsafe`, or
`implemented_by`. All seven new modules check without linter warnings.
`git diff --check` passed; existing older lints and computational sources
are unchanged. Computational suites were not rerun. The full goal remains
active and incomplete.

## 2026-09-04 — Positive-half-plane truncation and local zero bounds

Seven new Lean modules advance the independent analytic input to SW.
`CharacterDirichletContinuation` uses the proved finite Dirichlet tails to
obtain uniform convergence on every region `δ≤Re(s), |s|≤H` with δ>0.
The ordered limit is holomorphic on Re(s)>0. Analytic uniqueness identifies
it with the existing nonprincipal L-function by agreement near s=2.
For primitive χ modulo q>1 and every natural M≥1, this proves

```text
|L(s,χ) − Σ_{1≤n≤M}n^(−s)χ(n)|
 ≤ sqrt(q)(1+log q) M^(−Re(s))(1+|s|/Re(s)),  Re(s)>0.
```

There is no new cancellation input and no assertion of absolute or
unconditional series summability in the critical strip.

`LFunctionLowerBound` separates the coefficient at two and telescopes
the remaining inverse-square sum. For every character of positive modulus,
including principal characters, `|L(s,χ)−1|≤3/4` when Re(s)≥2.
Consequently `|L(s,χ)|≥1/4` and `|1/L(s,χ)|≤4` there.

`LFunctionGrowth` applies the M=1 truncation bound to get
`|L(s,χ)|≤1+B(q)(1+|s|/Re(s))`, where
`B(q)=sqrt(q)(1+log q)`. It proves uniform bounds on closed disks in
the positive half-plane and Cauchy estimates for every derivative, with
the actual disk margin `Re(s)−R` retained. These bounds apply to primitive
q>1 characters; no principal pole is suppressed.

`LFunctionZeroCount` combines the circle growth estimate and center lower
bound with Mathlib's Jensen inequality. At any center c with Re(c)=2,
the total analytic zero multiplicity in the closed disk of radius 5/4 is
at most

```text
[log16 + 2log q + log(|c|+2)] / log(6/5).
```

The outer radius is 3/2, wholly within Re(s)≥1/2. The proof uses
`B(q)≤q²` and an upper circle budget `4q²(|c|+2)`; the center inverse
bound contributes the remaining factor four. The formal left side is an
integer divisor sum cast to the reals. This is a zero-count estimate,
not a zero-free region.

`LFunctionLogDerivative` identifies the actual `−L'/L` with the twisted
von Mangoldt series for Re(s)>1 and bounds its norm by the real,
nonnegative `−ζ'/ζ(Re(s))`. The coefficient inequality
`3+4Re(z)+Re(z²)≥0` for |z|≤1 gives the actual three-four-one derivative
inequality with χ at σ+it and χ² at σ+2it. The first term is the full ζ
term, so integers noncoprime to q remain accounted for. These results
include principal characters and modulus one above Re(s)=1.

`ZetaTruncation` derives the sharp finite Euler error by integrating
complex-power variation on each unit interval. The pole-corrected ordered
sum is `Σ_{1≤n≤M}n^(−s)+M^(1−s)/(s−1)`. `ZetaContinuation` regularizes
it by multiplication by s−1, obtaining entire approximants for M≥1 and
locally uniform convergence on Re(s)>0. Analytic uniqueness identifies
the limit with Mathlib's entire principal regularization, whose value at
s=1 is one. Dividing away from one and returning to the sharp finite tail
gives

```text
|ζ(s) − Σ_{1≤n≤M}n^(−s) − M^(1−s)/(s−1)|
 ≤ (|s|/Re(s)) M^(−Re(s)),  Re(s)>0, s≠1, M≥1.
```

Independent reviews checked local uniformity, analytic uniqueness,
cutoff-zero handling, the principal pole, finite Euler signs, Cauchy disk
margins, Jensen constants and multiplicities, and every logarithmic-
derivative phase/sign. The next local analytic gap is a quantitative
logarithmic-derivative expansion after removing the actual nearby zeros;
the new [zero-free route](L_FUNCTION_ZERO_FREE_ROUTE.md) records the
available factorization and holomorphic-logarithm tools. Quantitative zero
exclusion, exceptional-real-zero control, prime-sum inversion, and uniform
SW remain unproved. B* is unchanged, so the full goal is still incomplete.

Verification: the full root build passed (8796 jobs). All 515 selected
axiom reports passed with only `propext`, `Classical.choice`, and `Quot.sound`.
The type audit confirms the exact positive-half-plane and pole restrictions,
the integer zero-divisor sum, the above-one logarithmic-derivative range,
and the unchanged pointwise SW+B* hypotheses of the twin-prime endpoint.
The source scan covers 141 project Lean files without proof holes, project
axioms, `native_decide`, `unsafe`, or `implemented_by`. All seven new modules
check without linter warnings. `git diff --check` passed. Older lints and
computational sources are unchanged; computational suites were not rerun.
The twin-prime conjecture remains unproved.

## 2026-09-04 — Actual-zero expansion and one-sided logarithmic derivatives

This checkpoint proves the quantitative local logarithmic-derivative bridge
identified in the preceding entry. It adds twelve Lean modules and 69 public
theorems. No independent distribution estimate or signed bilinear bound is
assumed inside these new analytic results.

`HolomorphicLog` constructs the normalized holomorphic logarithm on a ball.
`AnalyticLogDerivativeBound` combines Borel–Carathéodory on radius 5/4 with
Cauchy on radius 1/8, giving the explicit constant 144 on the closed unit
disk. `HolomorphicZeroRemoval` removes the actual divisor on a compact
subset: the quotient extends across its removable singularities, is
nonzero on the removed-zero set, and the factorization holds even at the
original zeros. `ZeroFactorBounds` proves the natural multiplicity count
agrees with the integer divisor sum and bounds the same quotient throughout
the outer disk. `ZeroFactorLogDerivative` differentiates the actual finite
polynomial and preserves that quotient.

For f holomorphic near the radius-3/2 disk, f(c)≠0, and outer-circle bound
M≥1, `LocalLogDerivativeExpansion` proves on the closed unit disk, at f(z)≠0,

```text
|f′/f(z) − Σρ D(ρ)/(z−ρ)| ≤ C_loc [1+log(M/|f(c)|)],
C_loc = 144(1+log 5/log(6/5)).
```

Here D is the actual analytic divisor on the closed radius-5/4 disk. The
proof uses |P|≥(1/4)^N on the outer circle, |P(c)|≤(5/4)^N, maximum modulus,
and Jensen. The normalized logarithmic budget is bounded by
1+log(M/|f(c)|)+N log 5. `LFunctionLocalExpansion` specializes this to
primitive q>1, Re(c)=2, with remainder
C_loc[1+log 16+2log q+log(|c|+2)]. Its evaluation-point nonvanishing can be
discharged on Re(z)≥1 using the existing qualitative theorem.

`LFunctionEulerCorrection` proves the actual differentiated inducing identity,
including principal inducing characters, with correction norm≤log q.
`ZetaLogDerivative` retains the pole explicitly, proves growth and derivative
bounds for Z=(s−1)ζ, and obtains |Z|≥1/3 on |s−1|≤1/4 and
|−ζ′/ζ−1/(s−1)|≤40 on the punctured radius-1/8 disk.

`LFunctionZeroSigns` proves positivity of real reciprocal contributions from
the actual divisor and multiplicity≥1 at a selected zero.
`LFunctionZeroInequality` therefore proves, for 1<σ≤9/8 and an actual zero
β+it with β≥3/4,

```text
Re(−Lχ′/Lχ(σ+it)) ≤ K(q,t) − 1/(σ−β),
K(q,t)=C_loc[1+log 16+2log q+log(|2+it|+2)].
```

The companion without the selected term and conductor monotonicity of K
also check. `ZeroFreeArithmetic` proves the scalar contradiction with
E>0, 0≤δ≤1/(20E), and a=1/(4E): 4/(a+δ)>3/a+E. The actual assembly of
character-square induction and three-four-one remains the next formal
step; see `L_FUNCTION_ZERO_FREE_ROUTE.md`. No quantitative zero-free-region
theorem has been claimed. The real-character exception, Siegel control,
uniform inversion, independent centered SW, and signed B* remain unproved.
The final twin-prime endpoint is still explicitly conditional on SW and B*.

Verification: the full root build passed with 8808 jobs. The axiom audit
passed for 584 selected declarations, including all 69 new theorems, using
only Classical.choice, propext, and Quot.sound. Printed theorem types retain
the stated domain/nonvanishing conditions and the final SW+B* hypotheses.
The scan of 153 project Lean files found no holes, new axioms, or trust
bypasses. New modules have no linter warnings. Independent reviews checked
the factorization at zeros, disk margins, maximum-modulus quotient, integer
multiplicities, logarithmic constants, Euler signs, principal pole, and
selected-zero signs. Computational sources were unchanged this checkpoint;
previous computational regression results and data were preserved.

## 2026-09-04 — Logarithmic zero-free regions and the possible real exception

This checkpoint adds nine Lean modules and 91 public theorems. It applies
the preceding actual-zero expansion to both character-square branches,
proves uniqueness and simplicity of the possible near-one zero, and proves
an independent zero-free region for regularized zeta. No distribution or
signed bilinear estimate is assumed in these new theorems.

`LFunctionInducedBound` bounds the negative logarithmic derivative for any
nonprincipal character by passing to its actual primitive conductor. It
also proves the principal inducing identity with its negative Euler
correction sign. `ZetaLocalExpansion` applies the actual-divisor expansion
to Z(s)=(s−1)ζ(s), whose value at one is one, and bounds the zeta logarithmic
derivative while retaining the pole at every height.

`LFunctionConjugateZeros` proves conjugation for nonprincipal L-functions
by analytic uniqueness, and bounds contributions of two distinct actual
zeros. `LFunctionNonquadraticZeroFree` and `LFunctionQuadraticZeroFree`
combine these bounds with three-four-one. The quadratic branch retains
the principal pole at twice the height and excludes sufficiently large
heights. `LFunctionNearOneZeros` treats the remaining rectangle: its
actual zero sum is at most 5E₀, whereas each zero contributes at least
3E₀. Thus there is at most one zero, and its actual meromorphic order is
one. For quadratic characters, conjugation forces that zero to be real.

Put C_loc=144(1+log 5/log(6/5)) and

```text
K(q,t) = C_loc[1+log 16+2log q+log(|2+it|+2)],
Kζ(t)  = C_loc[1+log 16+2log(|2+it|+2)],
E_N(q,t) = 120+4K(q,t)+K(q,2t)+log q,
E_Q(q,t) = 120+4K(q,t)+Kζ(2t)+log q,
E₀(q) = 40+K(q,0),
R(q,t) = E_N(q,t)+E_Q(q,t)+4E₀(q).
```

`LFunctionZeroFreeRegion` proves that any zero β+it of a primitive
character of modulus q>1 with β≥1−1/(40R(q,t)) has t=0, χ²=1, and
actual meromorphic order one. There is at most one such zero for each
fixed primitive character, including comparisons at different heights.
This is not a Page theorem comparing different characters or moduli.

`ZetaZeroFree` proves that regularized zeta has no zero when
β≥1−1/(80Eζ(t)), where Eζ(t)=120+4Kζ(t)+Kζ(2t). The proof combines its
existing nonvanishing near the pole with the three-four-one contradiction
at larger heights, retaining both principal pole terms. The regularized
statement includes s=1; its actual-zeta corollary explicitly excludes it.

`ZeroFreeLogarithms` proves the budget comparisons that give the widths

```text
primitive: 1/[4000C_loc(1+log q+log(|t|+4))],
zeta:      1/[8000C_loc(1+log(|t|+4))].
```

The primitive conclusion retains its possible unique simple real
quadratic exception. No lower bound for that exception's distance from
one has been proved. Uniform prime-sum inversion and independent
Siegel–Walfisz remain unfinished; signed B* remains an independent open
fixed-shift estimate. The exact twin-prime endpoint still takes pointwise
SW and B* as explicit arguments, so the full proof goal is not satisfied.

The [exceptional-zero audit](SIEGEL_EXCEPTION_ROUTE.md) identifies a useful
next quantitative bridge. The existing Cauchy growth estimate loses a
factor of order √q, which is too costly to convert a Siegel lower bound
for Lχ(1) into an arbitrary-power zero-distance bound. Truncating at M=q
instead gives the paper estimate |Lχ′(u)|≤10 exp(2)(log q)² for q≥256
and 1−1/log q≤u≤1. Its formalization remains to be done. The audit also
records the positive prime-power coefficients of the four-factor product
ζ Lχ₁ Lχ₂ L(χ₁χ₂), including ramified cases, and distinguishes finite
positivity from the still-missing quantitative residue comparison.

Verification: the full root build passed with 8817 jobs. The axiom audit
passed for all 675 selected declarations, including all 91 new public
theorems, with only Classical.choice, propext, and Quot.sound. Printed
types retain the actual-zero, domain, primitivity, and pole restrictions
and the final SW+B* hypotheses. The scan of 162 project Lean files found
no proof holes, project axiom declarations, or trust bypasses. The nine
new modules have no linter warnings. Independent reviews checked branch
boundaries, Euler correction signs, actual multiplicities, reciprocal
inequalities, both principal poles, and logarithmic-width comparisons.
Computational sources and data were unchanged in this checkpoint, so
their regression suites were not rerun. The twin-prime conjecture remains unproved.

## 2026-09-04 — Quantitative zero-to-value bounds and the positive product

This checkpoint adds eight Lean modules and 52 public theorems. It proves
the near-one derivative estimate identified in the preceding audit,
handles finite conductor ranges, formalizes the conditional arbitrary-power
conversion, and constructs the actual positive four-factor product.

`LFunctionZeroValue` restricts the complex derivative to a real segment
and proves the exact mean-value estimate. For primitive q>1 and an actual
real zero β∈[3/4,1], its coarse consequence is

```text
|Lχ(1)| ≤ [4+14√q(1+log q)] * (1−β).
```

`LFunctionNearOneGrowth` removes that fixed conductor-power loss. Actual
truncation at M=q, a harmonic-sum bound, and Cauchy's inequality give

```text
q≥256,  1−1/log q≤u≤1  ⇒  |Lχ′(u)|≤10 exp(2)(log q)².
```

The circle of radius 1/log q has real part at least 1/2 and norm at most
5/4. The function bound on it is 10 exp(2)log q. The proof uses neither
an exceptional-zero estimate nor a prime-distribution input.
`LFunctionLogarithmicZeroValue` therefore gives
`|Lχ(1)|≤10 exp(2)log²q(1−β)` and its division form for actual nearby
real zeros. Its width comparison applies this result to the possible zero
in the checked logarithmic region.

`LFunctionFiniteConductors` uses qualitative nonvanishing and finite
character groups to obtain a positive lower bound for all nonprincipal
L(1) values with 0<q≤Q. Combined with the coarse derivative estimate, it
gives a positive uniform gap for every real primitive zero with 1<q≤Q,
including zeros below 3/4. No quantitative dependence on Q is claimed.

`SiegelZeroGap` proves `(log q)²≤16q^(ε/2)/ε²`. A supplied value estimate
`|Lχ(1)|≥c q^(−ε/2)` consequently gives a zero gap at least
`[cε²/(160 exp(2))]q^(−ε)` at large q. Taking a minimum with the proved
finite-conductor gap covers all q>1. The final conversion explicitly
assumes the uniform Siegel value lower bound for every positive exponent;
it does not prove that input. Reality and the quadratic-character
conclusion come from the already proved zero-free region.

`QuadraticProductCoefficients` defines the actual Dirichlet convolution
`c=ζ*aχ₁*aχ₂*a(χ₁χ₂)` for characters at a common modulus. It proves
multiplicativity and c(1)=1 without quadratic hypotheses. For χ₁²=χ₂²=1,
it proves that every coefficient is a nonnegative real and c(n²)≥1 for
n≠0. The key exact paired identity is
`(aχ₂*a(χ₁χ₂))(n)=χ₂(n)(ζ*aχ₁)(n)`. Prime-power alternating support,
swapping the characters where necessary, and finite convolution establish
positivity with no infinite-product interchange.

`QuadraticProductLSeries` proves absolute summability and the exact
identity with ζ(s)Lχ₁(s)Lχ₂(s)Lχ₁χ₂(s) on Re(s)>1. Under the explicit
three nonprincipal conditions, its entire regularization has value
Lχ₁(1)Lχ₂(1)Lχ₁χ₂(1), which is nonzero, and the actual punctured residue
limit equals that value. Distinct nonprincipal quadratic characters
satisfy the product-character condition. Equal or principal factors are
not included in this simple-pole assertion.

`QuadraticProductPartialSums` identifies the actual finite complex
Dirichlet sum at a real exponent with its real weighted sum. It proves
nonnegativity, monotonicity in the cutoff, and a lower bound of one for
X≥1, at every real exponent. There is no infinite-series identification
below the line of absolute convergence.

The updated [exceptional-zero route](SIEGEL_EXCEPTION_ROUTE.md) records a
paper derivation of the next quantitative residue comparison through
repeated finite hyperbola identities and Abel continuation. Its proposed
pair, triple and four-factor summatory exponents are 1/2, 2/3 and 3/4,
respectively, with conductor and logarithmic losses retained. These
estimates, the ordered triple-limit identification, and exact inducing
Euler factors still require proofs. The uniform Siegel value lower bound,
prime-sum inversion, independent SW, and signed B* remain unfinished.

Verification: the full root build passed with 8825 jobs. The axiom audit
passed for all 727 selected declarations, including all 52 new public
theorems, with only Classical.choice, propext and Quot.sound. The printed
types retain the unproved uniform value hypothesis, actual-zero and
nonprincipal restrictions, Re(s)>1 for the L-series identity, and the
final twin-prime endpoint's SW+B* inputs. The scan covers 170 project
Lean files with no proof holes, project axioms or trust bypasses. All
eight new modules check without linter warnings. Independent reviews
checked disk margins, constants, power absorption, finite-conductor
quantifiers, coefficient signs, convolution identities and pole scope.
Computational sources and data were unchanged; their regression suites
were not rerun. The twin-prime conjecture remains unproved.

## 2026-09-04 — Character cancellation and the actual four-factor main term

This checkpoint adds 14 Lean modules and 85 public theorems. Complete-period
cancellation, finite hyperbola identities, and ordered Dirichlet continuation
now prove a summatory main term for the actual positive four-factor product.
The main coefficient is identified with the three L(1) values; it is not an
assumed residue or an unspecified limit.

`CharacterPeriodSum` proves zero complete periods for every nonprincipal
character at a positive modulus q, reduces an arbitrary natural prefix to
its remainder modulo q, and proves the q and 2q prefix/interval bounds.
`ComplexHyperbola` extends the exact real-endpoint hyperbola formula to
complex arithmetic functions. `ConvolutionHyperbolaBound` bounds the overlap
using a cancellation bound in one factor and a length bound in the other.
For two actual nonprincipal factors the resulting bound is `3q√x`.

`CharacterConvolutionMass` proves absolute pair and triple masses at most
`x(1+log x)` and `x(1+log x)²`, respectively. The factors can have different
moduli and need not be nonprincipal for these absolute estimates.
`ReciprocalPowerSums` proves the explicit sum bound
`Σ_{1≤n≤floor x} n^(−α) ≤ x^(1−α)/(1−α)` for 0≤α<1, including the zero
cutoff and α=0, and its square-root specialization.

`CharacterConvolutionCancellation` uses the actual three nonprincipal
factors at a common modulus, with real cutoffs x^(2/3) and x^(1/3), to get
`10q²x^(2/3)(1+log x)`. `CharacterConvolutionPower` absorbs the logarithm
using `1+log x≤13x^(1/12)` and obtains `130q²x^(3/4)`, including the
natural-prefix statement at N=0. None of these cancellation results needs
primitivity or a prime-distribution premise.

`PowerDirichletTail` proves finite weighted tail bounds from the explicit
prefix bound `|A(N)|≤CN^α`. Its ordered truncation error is
`2C M^(α−Re(s))(1+|s|/(Re(s)−α))` for Re(s)>α≥0. The new
`PowerDirichletContinuation` constructs the ordered limit independently
of a choice of α or C, proves local uniformity and holomorphy on that
half-plane, and identifies it by analytic uniqueness from a farther right
half-plane. Absolute summability is used only where separately justified.

`CharacterConvolutionContinuation` discharges the prefix hypothesis for
the actual triple convolution and identifies its ordered series with
`Lχ₁(s)Lχ₂(s)Lχ₃(s)` on Re(s)>3/4. At s=1 this gives actual reciprocal-sum
convergence and error at most `1300q²M^(−1/4)`. The three nonprincipal
conditions are retained so the product is holomorphic through one. No
absolute summability claim is made on the enlarged half-plane.

`ZetaConvolutionHyperbola` isolates the finite reciprocal head, floor error,
second strip, and overlap. `ZetaConvolutionPowerBounds` proves the explicit
power estimates for these pieces. `ZetaConvolutionAsymptotic` uses real
cutoffs y=x^(4/5), z=x^(1/5). If the triple cancellation constant is C,
the reciprocal tail, strip, and overlap cost respectively 20C, 4C, and C
times x^(4/5); the absolute head mass supplies the remaining logarithmic
factor. `CharacterConvolutionAsymptotic` therefore proves

```text
|S(x) − λx| ≤ (1+3250q²)x^(4/5)(1+log x)²,  x≥1,
λ = Lχ₁(1)Lχ₂(1)Lχ₃(1),
S(x) = Σ_{n≤floor x} (ζ*aχ₁*aχ₂*aχ₃)(n).
```

The actual quadratic-product specialization has λ equal to its entire
regularization at one. All three factors must be nonprincipal; a distinct
quadratic companion discharges the product-character condition. Positivity
is a separate checked property requiring both quadratic identities. The
new summatory estimate itself holds for arbitrary three nonprincipal
characters at a common positive modulus.

The updated [exceptional-zero route](SIEGEL_EXCEPTION_ROUTE.md) audits the
next Abel continuation step, its pole sign, and an explicit integral
remainder for Re(s)>4/5. That weighted residue comparison remains future
work. Its auxiliary-zero dichotomy also retains exact conductor transport,
real signs, and nonprincipal L(1) upper bounds as obligations. The uniform
Siegel value lower bound, prime-sum inversion, independent SW, and signed
B* remain unproved. The twin-prime conjecture remains unproved.

Verification: the full root build passed with 8839 jobs. The integrated
axiom audit passed for 812 selected declarations, including all 85 new
public theorems, with only Classical.choice, propext and Quot.sound and
zero Lean errors. The printed types retain the three nonprincipal
conditions, exact real cutoffs, ordered-convergence domain, and the final
twin-prime endpoint's SW+B* arguments. The source scan covers 184 project
Lean files with no proof holes, project axioms or trust bypasses. All 14
new modules passed standalone checks without linter warnings. Independent
reviews checked period and floor endpoints, reciprocal tails, exponent
arithmetic, actual residue identification, and absence of hidden analytic
inputs in the character specializations. Computational sources and data
were unchanged in this checkpoint, so their regression suites were not
rerun. The root PLAN's original assessment remains intact.

## 2026-09-04 — Uniform Siegel value bound and exceptional-zero power gap

This checkpoint adds 18 Lean modules and 84 public theorems. It completes
the quantitative residue comparison and both branches of the auxiliary-zero
argument. The new `siegel_value_lower_bound` has the exact uniform type

```text
∀ε>0, ∃c>0, ∀q>1, ∀ primitive χ modulo q with χ²=1,
  c q^(−ε) ≤ ‖Lχ(1)‖.
```

It assumes neither a value estimate, an exceptional-zero bound, nor a
prime-distribution theorem. Its constant is uniform over the character
and conductor. No effective dependence on ε is asserted.

The centered coefficients are `d=c−λ·zeta`, with λ the actual regularized
quadratic-product value at one. `QuadraticCenteredCoefficients` proves
their exact finite identities and the all-N prefix bound
`441(1+3250q²)N^(9/10)`. `QuadraticCenteredFunction` removes the pole with
the derivative-valued slope at one of the actual centered numerator.
`QuadraticCenteredContinuation` identifies the ordered d-series with
`F(s)−λζ(s)` on Re(s)>9/10 using absolute convergence only on Re(s)>1.
The resulting real tail bound is
`18522(1+3250q²)N^(−1/20)` for 19/20≤β≤1.

`ZetaRealTruncation` retains the positive pole denominator `1−β` below
one. `ResidueCutoff` makes the centered tail at most one half at the
natural ceiling `N=ceil((37044(1+3250q²))^20)`.
`QuadraticResidueComparison` keeps the exact finite product value, zeta
sum and centered tail. It combines `T_N(β).re≥1` with `F(β).re≤0` to get
`(1−β)/(4N^(1−β))≤‖λ‖`; an actual product zero is a specialization.
No nonnegativity of λ is silently required in that real-part argument.
`ResidueConductorBound` proves `N≤Aq^40`, where
`A=2(37044·3251)^20`, and the resulting denominator comparison.

`LFunctionPeriodBound` proves the actual ordered continuation and
`‖Lχ(1)‖≤5+log q` for every nonprincipal character, including imprimitive
ones. `LFunctionInducedValue` bounds the finite inducing multiplier by
`1+log Q` through the exact prime-subset expansion and a harmonic sum.
It also proves zero preservation and positive-half-plane zero equivalence.
`CharacterCommonLevel` transports primitive conductors and quadratic
identities to Q=q₀q. Different primitive conductors remain distinct, so
the three character factors are nonprincipal.

`QuadraticAuxiliaryComparison` consequently proves the actual target
value lower bound

```text
‖Lχ(1)‖ ≥ δ / [20‖Lχ₀(1)‖ A^δ Q^(40δ)(1+log Q)^3],
δ=1−β,
```

when the common-level product has nonpositive real part. The fixed
auxiliary-zero corollary discharges that condition using the exact
change-of-level identity. The auxiliary L-value is nonzero by the
already proved qualitative theorem.

The other branch uses actual real signs. `LFunctionRealSign` proves
reality of quadratic L-values, fixes their positive sign at two, and
uses an explicit zero-free real interval to preserve that sign down to
β. Zeta's real part is negative on 19/20≤β<1 by its checked truncation
at N=1. `QuadraticNoZeroTransport` transfers a supplied global primitive
quadratic zero exclusion to all three nonprincipal common-level factors.
`QuadraticAuxiliaryCharacter` supplies the fixed primitive complex
character modulo four, including a kernel-checked proof of its conductor.

For each ε>0, `SiegelValue` sets δ₀=min(1/20,ε/80). If a primitive
quadratic zero lies in [1−δ₀,1), it fixes that character and zero before
quantifying over targets. Otherwise it uses the character modulo four
at β=1−δ₀ and the proved negative product real part. Neither branch
reverses the zero-to-small-value implication or assumes auxiliary zeros
exist. `SiegelValuePower` absorbs the logarithmic cube with ε/6 and
uses `40δ≤ε/2`. `SiegelValueFromComparison` retains the factor q₀^(−ε)
and takes a minimum with the positive finite-conductor constant for all
q≤q₀. This includes every character of the auxiliary conductor.

`SiegelZeroGapUnconditional` now supplies the actual value theorem to
the earlier zero-to-value conversion. For every ε>0 it proves one d>0
uniform over primitive q>1 such that any zero in the checked logarithmic
region is real, belongs to a quadratic character, and has
`1−β≥d q^(−ε)`. The original conditional conversion remains available.
Its former value hypothesis is now discharged in the new theorem.

The independent reviews found no hidden analytic input, sign reversal,
conductor loss, or quantifier problem. The optional improper-integral
Abel route was not needed; the checked centered ordered-series argument
supplies the weighted comparison. The remaining classical step is
quantitative uniform prime-sum inversion and independent centered SW,
including conductor one. The signed fixed-shift input B* and the full
twin-prime conjecture remain unproved. The twin-prime conjecture remains unproved.

Verification: the full root build passed with 8857 jobs. The integrated
axiom audit passed for 896 selected declarations, including all 84 new
public theorems, with only Classical.choice, propext and Quot.sound and
zero Lean errors. The printed uniform value and power-gap types contain
no supplied value hypothesis. The final twin-prime endpoint still takes
independent pointwise SW and B* as explicit inputs. All 18 new modules
passed standalone checks without linter warnings; the source scan covers
202 project Lean files with no proof holes, project axiom declarations or
trust bypasses. Independent source reviews checked both dichotomy branches,
all-conductor quantifiers, constants, signs and exact analytic identification.
Computational sources and data were unchanged in this checkpoint, so their
regression suites were not rerun. The original root PLAN assessment is
preserved below its updated implementation banner.

## 2026-09-05 — Actual smoothed Mellin inversion and uniform contour estimates

The small-conductor route now has actual smoothed Mangoldt-character
inversion and a quantitative uniform primitive-character contour bound.
The complete formulas, source map, and remaining work are recorded in
[MELLIN_CONTOUR_ROUTE.md](MELLIN_CONTOUR_ROUTE.md).

The ramp kernel is 1/(s(s+1)). Its transform, vertical integrability,
and inverse are proved for every positive vertical line. Absolute
Dirichlet convergence gives summable norm integrals, justifying the
series/interchange step. The actual Mangoldt specialization requires
only a positive modulus, c>1, and x>0; it retains principal, imprimitive,
and modulus-one characters and the exact floor endpoint.

The former local radius-one expansion has a new radius-17/16 companion,
with derivative constant 288. The actual divisor disk stays 5/4 and
outer disk 3/2; older APIs and constants are preserved. The Siegel gap
now gives one positive d for a zero-free rectangle before any conductor,
character, or height is chosen. The zero-sum norm is bounded by actual
analytic multiplicity divided by the separation. With twice the width
and height margin two, this yields full complex logarithmic-derivative
bounds left of one. Regularized zeta is treated separately at all heights.

Finite Cauchy–Goursat gives right minus left equals i times bottom minus
top. The horizontal error is at most 2(c−a)x^c M/H²; the left integral
is at most π(1+a^(−2))x^a M, independently of height. Both inverse tails
cost 2x^c m(c)/H before normalization, where m(c) is the actual Mangoldt
Dirichlet mass. Its bound near one is 1/(c−1)+40. The assembled primitive
smoothed-sum theorem fixes the actual uniform Siegel constant and has
no supplied value, zero-free, inversion, or distribution premise.

The polylogarithmic family now has pointwise width and budget estimates:
for L≥1 and q≤L^B, the evaluation width is at least kL^(−1/2), and the
primitive norm budget is at most CL. Constants are positive and fixed
before q. The cap, the height margin, and both width halvings are retained.
These bounds give eventual versions with L=log x.

The principal pole kernel 1/((s−1)s(s+1)) is also inverted exactly; at
1/x its value is (x−1)^2/(2x), with error from x/2 at most one. Exact
finite unsmoothing of A(x)=Σa(n)(x−n) gives the sharp sum plus a short
interval remainder. For Mangoldt-character coefficients its norm is at
most (h+1)log(x+h), including floor and endpoint effects.

Remaining work is uniform asymptotic error absorption with c=1+1/log x
and H=(log x)^K, assembly of the principal contour with its main term,
and the final centered sharp-sum SW theorem. The signed fixed-shift B*
problem remains independent and unproved. The twin-prime conjecture remains unproved.

Verification: 102 new public theorems in 16 modules; every module passed
standalone Lean checking without warnings. The full root build passed
8873 jobs. The integrated audit passed 998 selected declarations using
only Classical.choice, propext, and Quot.sound, with zero Lean errors.
The source scan covers 218 project Lean files including the root import
file, with no holes, project axioms, or trust bypasses. Source review covered the
interchange majorants, contour orientation and normalization, both tails,
zero-divisor geometry, uniform constants, and finite endpoint conventions.
Final source checks and integration were completed. A separate independent
mathematical review of the assembled contour theorem was not completed.
No computational source or data was changed in this checkpoint, so the
computational regression suites were not rerun. Only the implementation
banner of root PLAN.md was updated; its original assessment is preserved.

## 2026-09-05 — Independent Siegel–Walfisz and completion of M3

Completed the classical distribution side of the root plan. The ten new
modules add 43 public theorems. `pointwise_siegel_walfisz` proves the
exact centered proposition with every positive pair of real logarithmic
exponents, a uniform constant and threshold, and conductor one included.
`ClassicalDistribution.lean` applies the existing maximalization and
SW-to-BV assembly, then the BV-to-Mertens reduction. No distribution
argument remains in the resulting SW, BV, or Mertens theorem types.

The principal contour is assembled from the actual identity
`−ζ′/ζ=1/(s−1)−Z′/Z`. Both inverse-integral summands are integrable;
their difference gives the regularized contour. Its pole weight
`(x−1)^2/(2x)` differs from x/2 by at most one. The conductor-one common
evaluation width fits within the zeta zero-free region, and its norm
budget is bounded by twice the corresponding primitive budget.

At L=log x, c=1+1/L, H=L^K, the principal contour budget is bounded by
`42 e x L^(1−K)+3C x L exp(−k sqrt L)+C e x L^(1−2K)`.
Taking K=A+2 and using square-root exponential decay gives a common
threshold for arbitrary logarithmic savings. This proves centered
smoothed SW uniformly over q≤L^B. The bounded pole correction is absorbed
using the proved eventual inequality L^A≤x.

Centered finite differences give the sharp error bound
`((x+h)|Eχ(x+h)|+x|Eχ(x)|)/h+(h+1)log(x+h)+h/2`.
Using smoothed exponent 2A+4 and h=x/L^(A+2) bounds this by
`(5C+5)x/L^A`. Every floor endpoint and the principal quadratic correction
is retained. The second endpoint is larger, so it satisfies the same
threshold and conductor bound. Natural restriction then gives the exact
`PointwiseSiegelWalfisz` interface.

The new `twinPrimeConjecture_of_signed_bilinear` supplies all classical
inputs and has only PLAN's cofinal B* bound as a premise. M0–M3 are now
implemented. This does not prove the conjecture: B* is still open, and
M4–M6 remain incomplete. The [classical proof map](CLASSICAL_DISTRIBUTION_THEOREM.md)
records the source-to-lemma chain and exact formulas; the root plan's
original assessment was preserved while its implementation banner was updated.

Verification: the full root build passed 8883 jobs. The integrated audit
passed 1041 unique selected declarations, including all 43 new public
theorems, with only Classical.choice, propext, and Quot.sound and no errors.
The printed endpoint type retains only B*. A source scan covers all
228 project Lean files, including the root import file, without holes,
project axiom declarations, or trust bypasses. All ten new modules compile
without new warnings. This checkpoint has implementation-source review and Lean
verification; no separate independent mathematical review was completed.
Computational code and data were unchanged,
so their already passing regression suites were not rerun. The full proof
remains unestablished.

## 2026-09-05 — Global dispersion budgets and two large-gcd removals

Added 62 public theorems in eight modules. The [range-removal proof map](DISPERSION_GCD_ROUTE.md)
records the exact formulas, constants, and source declarations. Every actual
factor pair is assigned uniquely to a right-closed dyadic box, including
powers of two. The full signed bilinear sum is exactly the sum of these
boxes, and their number is at most dyadicNatDepth(2X)^2. The diagonal root
budget over this growing family is o(X) even after any fixed logarithmic
loss at the primary fifth-root cutoffs.

The elementary rectangle count for gcd(d,e)>G is at most AB/G. Applying
it to the ordered distinct left-factor pairs gives
T*|Off_large|≤16X²L⁴/G, with L=log(4X+4). At G=ceil(L^10), summing the
root bounds over the entire box family costs at most 4(2/log 2)^2 X/L.
This is an unconditional o(X) contribution. The remaining quantity is
sum_boxes sqrt(max(T*Off_small,0)), which is still unestimated. Cancellation
in a signed sum of off-diagonals across boxes alone would not control it.

A separate restriction acts directly on the original factors (d,r),
retaining the exact signed coefficient μ(d)β_V(r)Λ(dr+2), product interval,
and d=r terms. Its pair count is at most 4MN/G and its box mass at most
8XL²/G. The complete original-factor large-gcd sum therefore satisfies
|B_large|/X≤8(2/log 2)^2/L^6 for X≥128. The exact identity B=B_small+B_large
proves (B−B_small)/X→0. This is a removal of an actual bilinear range,
not an estimate for its remaining small-gcd sum.

The [shifted-Möbius input audit](SHIFTED_MOBIUS_INPUT_AUDIT.md) checks five
primary papers. The inspected shift-average results do not isolate shift
two, the cofinal multiplicative-function theorem does not cover the actual
weighted coefficients, and the fixed-shift claims require additional
hypotheses. None supplies the missing small-gcd estimate. In particular,
ordinary BV does not discharge a progression hypothesis whose summands
already contain Möbius values on shifted primes.

Verification: full root build passed 8891 jobs. The integrated axiom audit
passed 1103 unique selected declarations, including every new theorem,
with only Classical.choice, propext, and Quot.sound and zero errors. The
source scan covers 236 project Lean files and found no holes, project
axioms, or trust bypasses. All eight new modules compiled without warnings.
Independent source review found no issues with signs, endpoints, pair
counts, or whole-family logarithmic losses. Computational code and data
were unchanged, so those regression suites were not rerun. The original
root PLAN assessment is byte-preserved from its assessment-date line.
M4 has these proved range estimates, but its total B* budget is not closed.
M0–M3 remain complete; M4–M6 and the twin-prime goal remain incomplete.

## 2026-09-05 — Thin active band, large prime squares, and the simultaneous residual

The previous goal turn was verified progress. This turn adds 45 public
theorems in four modules, refining the actual range estimates rather than
replacing the signed B* premise with another asserted analytic input.
See Sections 7–8 of the [dispersion proof map](DISPERSION_GCD_ROUTE.md).

A nonzero right-closed box satisfies X<4MN and MN<2X. Thus its dyadic
product exponent i+j lies in at most three adjacent levels. The map
(i,j)↦(i,i+j) proves cardinality≤3*dyadicNatDepth(2X). Every entry vanishes
outside this strict band, giving exact transport of B and all diagonal,
signed off-diagonal, large-gcd and small-gcd root budgets. At L=log(4X+4)
and G=ceil(L^10), the complete large-gcd dispersion error is now bounded
by 12(2/log2)X/L², and the original-factor large-gcd sum in absolute value
by 24(2/log2)X/L⁷, for X≥128. The full diagonal bound improves to
O(XL³/sqrt U); its already-proved arbitrary fixed logarithmic saving remains.

A distinct removal uses squarefreeness of the nonzero left Möbius factor.
If prime p satisfies p²|dr, then p²|r or p divides both d and r. The two
allocations are covered by images of positive hyperbola pairs ab≤T/p².
Counting such pairs by T(1+log T), then summing the inverse-square tail,
gives 2T(1+log T)/H for the union over primes p>H. This yields the actual
factorwise absolute bilinear mass bound 8XL³/H, uniformly in U,V. At H=G,
the normalized mass is at most 8/L⁷. The exact complementary split and
actual difference limit are proved for arbitrary cutoff functions.

The final joint residual keeps gcd(d,r)≤G and excludes every input dr
with p²|dr for a prime p>G. Its signed summand is unchanged. The difference
from actual B is the large-gcd sum plus a small-gcd/large-square intersection.
That intersection is controlled by the full factorwise absolute square mass;
no signed estimate is illicitly restricted. At primary cutoffs,

```text
abs(B−B_core)/X ≤ (24*(2/log2)+8)/L^7,  X≥128,
(B−B_core)/X → 0.
```

`structuredCore_condition_of_squarefree` also proves that every squarefree
input survives. Rough squarefree composites retain their negative grouped
coefficient. The removed ranges therefore do not settle the sign of B_core.

The [centering review](DISPERSION_CENTERING_REVIEW.md) gives the exact
positive gcd-one off-diagonal witness at X=14, the local factors retaining
d−e, and the beta expansion that introduces the growing coefficients db,eb.
Its paper center uses c(r)=1_(r odd)r/φ(r) times the exact interval sum of μ.
Both moving Mertens endpoints are bounded uniformly, giving a complete paper
O(X/log³X) center budget from proved inputs. The same bound controls its
square-root energy, so centering does not weaken the vanishing full-moment
budget requirement. The assembled center theorem is not formalized and the
centered correlation remains unproved.

The [input audit](SHIFTED_MOBIUS_INPUT_AUDIT.md) now includes primary-source
updates from 2025–2026. Quantitative fixed-shift multiplicative correlations
still have the wrong coefficient class and affine coefficient range. Ford's
shifted-prime model sees only the small-prime valuation vector, which does
not distinguish prime and rough semiprime bilinear coefficients. Recent
Möbius sign occurrence in progressions does not impose prime-shift support.
No applicable signed estimate for the residual was obtained.

A further exact grouping is available for investigation: when n=a*b has
1<a≤U, a contains the small-prime part and every prime divisor of b exceeds
U=V, the original grouped coefficient vanishes. For squarefree n>U in
general it is Λ(n)−m_U(a)log b. Thus the rough a=1 negatives and the smooth
part a>U remain. This observation is a paper identity, not a new range
estimate for the surviving signed core or a completed Lean module.

Verification: full root build passed 8895 jobs. All 45 new public theorems
occur in the integrated audit of 1148 unique selected declarations. Only
Classical.choice, propext, and Quot.sound occur; zero errors were reported.
All four new modules passed standalone checking and the full build without
warnings. The 240-file project Lean scan is clean. Independent source review
checked the band endpoints/count, both square allocations, actual coefficient
scope, overlapping restrictions, and paper center constants. Existing
computational programs and recorded data were unchanged, so their regression
suites were not rerun. The root PLAN assessment is preserved byte-for-byte
from its assessment-date line; only its implementation banner was updated.
M0–M3 remain complete. The signed B* estimate, M4–M6, and the requested
unconditional twin-prime proof remain incomplete; the twin-prime conjecture remains unproved.

## 2026-09-05 — Prime-beta replacement and exact small-part cancellation

Added 52 public theorems in seven modules, described in the
[prime-beta proof map](BILINEAR_PRIME_BETA_ROUTE.md). This changes the
coefficient decomposition while retaining an explicit absolute error budget.

For the original beta, a nontrivial small-prime part a with 1<a<=U forces
(mu_high(U)*beta(U))(ab)=0 for every positive U-rough b. Neither factor
needs to be squarefree. For squarefree U-smooth a of any size, the coefficient
is Lambda_high(U)(ab)-m_U(a)log b. In particular distinct primes p,q<=U<pq
give exactly +log b. These are grouped identities, not termwise deletions.

Define beta'(r) as the sum of log p over distinct prime divisors p>V.
The actual proper-prime-power summatory bound psi-theta<=C sqrt gives a
uniform reciprocal tail at most 3C/sqrt(V), including empty finite tails.
Counting positive pairs dr<=2X with e|r, then retaining the actual coefficient
weights, proves

```text
ErrorMass(U,V,X) <= 4 X log(4X+4)^2 * sum_(V<e<=2X) nonprimeMangoldt(e)/e
                  <= C_pp X log(4X+4)^2 / sqrt(V),   V>=1, X>=1.
abs(B(U,V,X)-Bprime(U,V,X)) <= ErrorMass(U,V,X).
```

The positive constant is uniform in U,V,X. For primary V(X) and arbitrary
U(X), normalized absolute mass and signed difference tend to zero, even
after multiplication by any fixed natural power of log(4X+4). Exact
factor-to-product grouping connects Bprime to mu_high*beta'.

The checked prime-only identity, for every positive smooth a and rough b,
is P_U(ab)-m_U(a)beta'_U(b), without squarefreeness. Here P_U retains only
primes above U and beta'_U(b) is a checked distinct-prime log sum. For a>1
the prime term is zero. The log-radical notation and additional sign-range
corollaries in the paper note are not separate Lean exports.

The remaining obstruction is explicit. When a is U-smooth and lies between
ceil(2X/U^2) and floor(2X/(U+1)), a positive nontrivial U-rough factor b in
the product interval is prime. Its contribution is a signed sum of
m_U(a) log p Lambda(ap+2). Modulus a exceeds BV; switching to p leaves the
smooth restriction and signed divisor weight, and expansion allows pd up
to U^3. Ordinary BV does not estimate this restricted progression sum.
The complete smooth-part moment still yields only Bprime>=-CX+o(X), which
permits cancellation of the entire positive main term. No B* margin follows.

Scratch diagnostics in .lake/build/small_prime_part_audit.py and its JSON
checked 595473 exact coefficient identities at four scales through X=10^6,
including 492888 exact middle-class zero checks. The recorded normalized
masses use binary64 and are not analytic bounds. Exact prime-log witnesses
show both signs in the surviving class; a squarefree example at U=55 has
coefficient -2 log(500029). The separate cube-rough diagnostic confirms the
finite parity identity but cannot distinguish prime-prime from
semiprime-semiprime even parity. These are diagnostics, not a proof of a limit.
Existing computational programs and recorded datasets were unchanged.

Verification: full root build passed 8902 jobs. All 52 new public theorems
are in the audit of 1200 unique selected declarations; only Classical.choice,
propext and Quot.sound occur, with zero errors. All seven modules checked
cleanly. Independent review covered every new source. The 247-file project
scan is clean; the original PLAN assessment SHA256 remains
459227843C2E2AFBDB42B4288B81713578D171373E9C0818E565A6A9333C67CE.
M0-M3 remain complete. B*, the M4 breakthrough, M5's complete alternative
requirements and M6 remain incomplete. The twin-prime conjecture remains unproved.

## 2026-09-05 — A proved polynomial right-cutoff removal

Added 38 public theorems in seven modules; see the
[cutoff-change proof map](CUTOFF_SHIFT_ROUTE.md). For arbitrary natural U
and V,W<=X the exact identity is B(U,V)-B(U,W)=I(U,V)-I(U,W). The finite
bound retains both Type I progression sums and both even-modulus budgets.

Generalizing the existing distribution application now proves that any
modulus function bounded eventually by X^a, a<1/2, lies in the actual BV
range for every fixed logarithmic restriction. Its complete error sum,
including a factor log(2X+2), is o(X). The even budget for independent
cutoffs is at most 4(2X+2)^(a+1/2)log²(2X+2) when UV<=(2X+2)^a, a>=0.
It is o(X) when a<1/2. No even-modulus exception is omitted.

With U=primaryCutoff, U*W<=X^a eventually implies W<=X eventually.
The integer inverse-floor bound then gives log(W+1)<=5log(U+1).
The proved F(U)log²(U+1) limit and shared-prime correction control the
complete mixed totient main coefficient. The actual classical theorems
therefore supply, for every natural-valued W and fixed 0<=a<1/2,

```text
U(X)*W(X) <= X^a eventually  ==>  I(U,W,X)/X -> 0,
                                (B(U,U,X)-B(U,W,X))/X -> 0.
```

The explicit quarterCutoff W=floor(X^(1/4)) has UW<=X^(9/20), leaving
BV slack 1/20 and an even error exponent 19/20. The final prime-beta
replacement at W also differs from original B(U,U) by o(X). The generic
product theorem allows power exponents theta<3/10 for W; a separate
power-cutoff family is not exported. This controls a complete signed beta
divisor band, not its absolute mass or an arbitrary further restriction.
The removed band contains contributions from right factors r much larger
than W, since their beta weights change too.

The resulting mixed coefficient is P_W(ab)-m_U(a)beta'_W(b) for positive
W-smooth a and W-rough b. Both repeated factors and b=1 are included.
The left truncation remains U. In particular, a prime with U<a<=W gives
exactly -beta'_W(b)<=0, now proved in Lean. The surviving prime-quotient
range has a approximately X^(1/2)..X^(3/4), p approximately X^(1/4)..X^(1/2),
and the signed weight m_U(a)log p Lambda(ap+2). Switching leaves the
smoothness/prime restrictions and can introduce moduli pd up to X^(7/10).
No lower-bound margin for this remaining sum was proved.

Additional investigation found the smallest-prime recurrence
m_U(p^nu c)=m_U(c)-m_floor(U/p)(c) for p not dividing c. Its iterated pair
remainder has both signs: for residual primes 7,11,13,17 the truncated
sum is -1 at 100 and 2 at 200. The recurrence was checked in 199920 finite
cases and its pair-tail version in 63661 smooth cases; neither yields a
valid one-sided deletion. These remain research diagnostics/paper identities.

Scratch prime-only diagnostics at the existing four scales made 79995 exact
coefficient checks on prime-shift support. At X=10^6 the rough contribution
is about -2.294204X, the pair-product favorable contribution +1.764781X,
and the residual +0.325984X. These binary64 masses are diagnostic only.
There are no negative nonrough coefficients on odd inputs for the tested
cutoffs U<=15; these scales therefore cannot test the eventual negative
residual. No scale increase was made. Reproduction files are
.lake/build/prime_beta_class_audit.py and .json; existing compute programs
and datasets are unchanged.

The source review checked Pascadi's factorability and smooth-function
conditions and Bharadwaj-Rodgers's restricted prime-factor correlations.
A seven-prime support example explicitly defeats the proposed factorability
of the actual nonzero weight; no shifted-prime existence is asserted for
that example. None of the inspected statements supplies the missing signed
prime-quotient estimate. Exact versions and applications are in the proof map.

Verification: full root build 8909 jobs; all 38 new public theorems audited;
1238 unique selected declarations with only Classical.choice, propext and
Quot.sound, zero errors. All seven new modules compiled without warnings.
Independent mathematical review covered every new module; 254 project Lean
files scanned clean. The root PLAN assessment remains byte-for-byte intact.
M0-M3 remain complete. B* remains unresolved and M4-M6 remain incomplete;
the full requested proof is not obtained and the goal
stays active.

## 2026-09-05 — Exact finite center with every fixed logarithmic precision

Added 17 public theorems in seven modules; see the
[finite-center proof map](CLASSICAL_CENTER_PRECISION.md). Define the actual
finite main expression J=XS(U)+F(U)M(U,X)-XQ(U,V), retaining the full shared-prime
Type I correction. The exact residual is R_A+R_H-R_I. For positive cutoffs
with UV<=X, its absolute value is at most 8 log(2X+2) times the full maximal
progression-error sum through UV, plus three complete mixed even budgets.

The BV application now allows any fixed natural logarithmic weight and any
modulus function eventually bounded by X^a, a<1/2. The even budget has the
same precision when 0<=a<1/2. The combined actual center error is therefore
o(X/log^k X) for every fixed natural k, without needing rates for S, F, or Q
relative to their limits. Proper-prime-power mass Epp satisfies the same
all-logarithmic-power conclusion from its explicit square-root bound.

The centered right-cutoff difference is exactly the difference of the two
Type I remainders. Its all-logarithmic-power estimate is instantiated at
the primary and quarter cutoffs. The quarter prime-beta replacement also
retains this precision, including an absolute error with log(2X+2) rather
than log(4X+4). These are complete-sum estimates; no arbitrary restriction
or absolute divisor-band estimate is inferred.

The alternative conditional endpoint assumes a cofinal gain
B+J>=cX/log^k(2X+2), with fixed c>0 and natural k. Actual BV and Epp estimates
show the total error is eventually strictly smaller than that gain, giving
W2>Epp and thus infinitely many genuine twin pairs. The gain remains an
explicit, unproved theorem argument. This permits a sublinear sufficient
target but does not prove positivity or discharge the original B*.

The exact centering matters: the abstract counterexample A=CX, K=-h,
B=-CX+h, W2=Epp=N2=0 satisfies the known normalized limits for h=o(X).
For h=X^(3/4), B+CX is positive and unbounded while even all fixed
logarithmic improvements hold. This only refutes an inference from those
limits; it is not a model of the actual arithmetic terms. The new J removes
that error-budget ambiguity but creates no positive mass.

The independent analytic investigation found no sign gain from asymmetric
cutoffs or averaging. With 0<u, v>1/3, u+v<1/2, two large primes simplify
the rough part but leave a harmonic absolute truncated-Möbius mass and
prime-quotient restrictions. The middle-prime negative class alone retains
a correlation of p and ap+2 both prime. The inspected mean-square and
almost-all-scales multiplicative-function statements do not supply its
needed estimate. A logarithmically weighted Twin Primes preprint found in
the source search is withdrawn and was not used. Exact sources and scope
checks are recorded in the proof map; no new numerical experiment was needed.

Independent review covered all seven modules and the paper note. It caught
a duplicate generic growth helper before integration; the final mixed-even
module reuses the existing BilinearExceptional theorem. Full root build:
8916 jobs. Axiom audit: 1255 unique selected declarations, including all 17
new public theorems, only Classical.choice/propext/Quot.sound, zero errors.
All new modules compile without warnings. The scan covers 261 project Lean
files with no holes, project axioms or trust bypasses. The PLAN assessment
is byte-for-byte unchanged. Existing compute programs and datasets are
untouched in this checkpoint. M0-M3 remain complete; M4-M6 and the full
requested Twin Primes proof remain incomplete. The twin-prime conjecture remains unproved.

## 2026-09-05 — Smoothing changes the bilinear main term

The next investigation targeted an actual signed gain rather than another
conditional endpoint. The [smoothing review](SMOOTHED_SIGNED_GAIN_REVIEW.md)
derives an exact averaged divisor coefficient and computes its full main
displacement. This is a paper result from the proved classical inputs, not
a newly exported Lean theorem.

Full logarithmic averaging over 1<=t<R has weights log((t+1)/t)/log R.
Its coefficient is exactly Lambda_R(n)/log R. For R=X^r, W=X^v with
0<r<=v and r+v<1/2, the averaged center divided by X tends to
C[1+(1-v)/r], rather than C. Both sharp and averaged centered expressions
approximate the same W2, so the actual averaged-minus-sharp bilinear sum
divided by X tends to -C(1-v)/r. No W2 asymptotic is assumed. At the
primary/quarter exponents this is -15C/4, with averaged center 19C/4.

The calculation retains the lower-cutoff boundary. It uses the exact
averaged center, logarithmic Cesaro growth of the quadratic smoothed totient
sum, the leading coefficient one of the odd Mangoldt/totient sum, and
uniform domination of the averaged shared-prime correction. A fixed-power
window S=X^s, 0<s<r, cancels the extra boundary and restores center CX+o(X).
This still supplies no signed gain. Treating full averaging as an o(X)
replacement without its changed center is ruled out.

Smoothing also fails a proposed pointwise monotonicity. At X=300,R=W=10,
n=381=3*127 with shifted prime383, the sharp prime-beta coefficient is zero,
but its logarithmic average is -log3*log127/log10. The exact finite A+H-I
term supplies the opposite change. A second witness uses the exact planned
cutoffs at X=1000: R=3,W=5,n=1011=3*337,shifted prime1013; the change is
-log337. The new `compute/smoothing_check.py` verifies both witnesses,
4,800 averaging identities and 9,600 direct prime-beta convolution identities
with exact integer logarithmic coefficients. Independent execution passed;
no floating-point sign or large-range experiment was used.

Goldston-Yildirim's mixed-moment theorem genuinely applies to the shifted-
prime weighted square of Lambda_R/logR and gives size CX/logR. Nevertheless
Cauchy and beta'<=log(2X) yield only O(X sqrt(logX)) at a polynomial cutoff.
The ordinary smoothed moments of Granville-Koukoulopoulos-Maynard do not
remove this remaining weighted positive-part problem. These are checks of
specific inequalities and losses, not an impossibility theorem for smoothing.

The distinct Fouvry-Radziwill prime-modulus convolution theorem accepts the
divisor-bounded smooth coefficient and prime quotient, but encoding ap+2 as
the prime modulus requires level Q of order X. Its length condition would
force the short factor below X^(-4/9-epsilon). The inspected Wright extension
also fails this level-one encoding. Mellin inversion supplies no positive
singular term for the actual twin-prime Dirichlet series, and Fourier energy
does not force its frequency-2 coefficient. These proposed routes retain
specific missing estimates; their applicability checks are in the paper note.

Independent review checked the main constant, displacement sign, fixed-power
windows, both finite witnesses, moment hypotheses, and convolution exponents.
No Lean source changed; the previous verified checkpoint remains 8916 build
jobs and 1255 audited declarations, with 261 project Lean files. No milestone
was promoted: M4-M6 and the full Twin Primes proof remain incomplete. The
original PLAN assessment is preserved and the twin-prime conjecture remains unproved.

## 2026-09-05 — Power-window audit: no signed-budget progress

The follow-up investigation checked whether quadratic-sieve optimality and
its secondary term could supply the missing positive-part bound. It cannot
be inferred from the inspected statements: the ordinary and shifted-prime
quadratic kernels differ, and the square fails to majorize the positive
part on actual composite support. Section 6 of the
[smoothing review](SMOOTHED_SIGNED_GAIN_REVIEW.md) records the precise failure.
The exact diagnostic now includes X=100000, S=3,R=10,W=17,
n=100055=5*20011, with prime shift100057 and 0<m_(S,R)(n)<1.

An independent audit of the Lean endpoint found its definitions, cofinal
quantifiers and error comparison substantive. No existing result inspected
discharges its signed gain. The first-moment and rough-input observations
recover the previously documented cancellation obstruction; they do not
advance the asymptotic budget. No Lean source changed. The full proof and
M4-M6 remain incomplete; the missing signed gain remains the blocker.

Verification: two separate executions both passed all 14,400 finite
identities and the three witnesses. The changed documents' 40 local links
and whitespace checks passed, and the original PLAN assessment hash is
unchanged. No Lean build was repeated because no Lean source changed.
After the same signed-gain gap persisted through the exact-center reduction,
full-smoothing calculation and power-window audit, the goal was marked
blocked, not complete. Continuing to restate that gap would not supply the
new arithmetic estimate required by M4.

## 2026-09-05 — Resumed work: a bound for the middle-prime class

The resumed run proves a new paper estimate for an entire negative class,
rather than another reformulation of the signed endpoint. For
U=floor(X^(1/5)), W=floor(X^v), and 1/5<v<3/10, let T_v be the actual
shifted-Mangoldt mass with prime smooth part q in (U,W] and W-rough
quotient, weighted by beta'_W. The
[middle-prime sieve proof](MIDDLE_PRIME_SIEVE_BOUND.md) gives
limsup T_v/X <= C K(v), where
K(v)=4log(5v)-2log((1/2-v)/(3/10)). At v=21/100, an exact rational
logarithm bound proves K(v)<263/1000, hence T_v<=0.263 C X eventually.
At v=1/4 this particular bound exceeds C X. No squarefree, semiprime, or
prime-quotient condition is silently imposed on the class.

Five new modules supply 37 checked theorems. They construct the actual
finite sieve, identify its exact odd-squarefree denominator, retain the
full 3^omega Selberg error, and prove that error negligible at every fixed
logarithmic scale under a fixed-power modulus cap below X^(1/2). Unique
largest prime factors give multiplicity one when the sieve support is
retained; a separate unrestricted reindexing gives the safe multiplicity
two bound. The finite aggregated class estimate includes its explicit main
sum and its full weighted error.

Integration verification passed the integrated build (8921 jobs) and an expanded
axiom/type audit (1292 unique selected declarations, including all 37 new
theorems). The audit found only Classical.choice, propext and Quot.sound,
with no errors. Independent checks reviewed the class identification,
denominator, product multiplicities, weighted Cauchy estimate, and actual
unconditional BV application. The original PLAN assessment hash remains
unchanged.

The complete asymptotic class estimate is not yet a Lean theorem: the
denominator asymptotic, uniform substitution, and outer prime summation
remain. The rough-composite loss and the two signed composite-smooth-part
masses are also unestimated. This progress does not discharge B*, the
cofinal logarithmic gain, or M4-M6. The twin-prime conjecture remains unproved.

## 2026-09-05 — Denominator asymptotic and uniform sieve substitution

The denominator obligation identified above is now proved in Lean. Four
additional modules supply 38 theorems: the actual multiplicative
coefficient and its normalized-Moebius correction; the correction's
local values and absolute summability; its Euler-product mass 1/C; and
the harmonic-convolution limit. The latter keeps the real floors and
natural division, subtracts h(0) for a general sequence, and uses only
absolute summability, with no hidden logarithmic moment. For the actual
arithmetic function h(0)=0.

Consequently S(z)/log z->1/C and log z/S(z)->C. A further checked theorem
substitutes the reciprocal bound simultaneously into every active member
of a growing sieve family, assuming its minimum active threshold tends
to infinity. The resulting class inequality retains the full weighted
error. The [proof map](MIDDLE_PRIME_SIEVE_BOUND.md) records all nine new
modules and the remaining threshold and prime-summation obligations.

A separate reviewed [rough-composite bound](ROUGH_COMPOSITE_SIEVE_BOUND.md)
preserves H=N_rough+P, where P is the actual prime-input contribution.
The paper upper/lower linear sieve gives
4C log(29/21)<=liminf H/X<=limsup H/X<=4C. Repeated factors and even
inputs have explicit negligible errors. Thus N_rough<=4CX-P+o(X), which
does not certify the remaining allowance. A proposed independent bound
N_rough<=0.737CX+o(X) would itself force a positive twin correlation.
The signed composite-smooth-part contribution has not been estimated.

Verification: full root build passed 8925 jobs; the axiom/type audit passed
for 1330 unique selected declarations, including all 75 new theorems in
nine modules, with only Classical.choice, propext and Quot.sound and no
errors. Independent reviews and standalone checks passed for the new
kernel, harmonic limit, Euler mass and uniform family limit. All 270
project Lean files passed the proof-hole/trust and whitespace scans.
The original PLAN assessment hash is unchanged. M4-M6 remain incomplete;
the active goal has not been declared complete or blocked.

## 2026-09-05 — Completed class bound and the remaining total budget

The complete middle-prime class bound is now proved in Lean:
T_(21/100)(X)<=0.263 C X eventually, with C=2 C2. The actual integer
thresholds, prime summation and full weighted progression error are
supplied. Centered Abel summation retains the floors and full variation;
proper prime powers, the p-to-phi(p) replacement, and logarithmic
rounding all have vanishing errors. At a=49999/100000 the exact
certificate for K_a is 961951827676901725/3657898403618589003<263/1000.
This fixed exponent below one half suffices for the stated bound. The
sharper limiting formula as a increases to one half remains a paper
consequence and is not needed by this Lean endpoint.

The progress metric for further work is the complete signed budget,
recorded in [SIGNED_TOTAL_BUDGET.md](SIGNED_TOTAL_BUDGET.md):

Q_tw>=0.737 C X-R-E_tot,

where R=N_rough+N_comp-P_comp and
E_tot=D_cl+D_beta+Epp+|J-CX|=o(X). All quantities use the same mixed
cutoffs. There is no omitted cutoff-change error or discarded positive
composite mass. A sufficient new estimate is R<=(0.737-delta) C X on
cofinally many scales for some fixed delta>0. No such estimate is proved;
the certified positive total margin remains zero. The upper bound for
one negative class must not be counted as an independent total saving.

Two paper tests address the remaining arithmetic. Charging the exact
least-prime Buchstab strips with ordinary upper linear sieves leaves
4 C X log((1/2-w)/w)+o(X), which exhausts the lower budget at w=1/4
before primes have been isolated. A different mechanism, scale averaging
and a four-mode multiplicative encoding of rough primes, still needs
relative correlation control on sparse support at fixed shift two.
The inspected absolute logarithmic correlation estimates and averages
over shifts do not provide that precision. Neither test improves the
complete inequality, so neither justifies substantial new formalization.

Verification: the root build passed (8936 jobs). The integrated axiom/type
audit passed for 1396 unique selected declarations, including every new
public theorem, with only Classical.choice, propext and Quot.sound and
zero errors. All 281 project Lean files passed proof-hole/trust and
whitespace scans. The original PLAN assessment suffix has unchanged
SHA256 459227843C2E2AFBDB42B4288B81713578D171373E9C0818E565A6A9333C67CE.
M4-M6 and the twin-prime conjecture remain unresolved.

## 2026-09-05 — Quantitative distribution and Fourier budget tests

The [new paper assessment](DISTRIBUTION_AND_FOURIER_BUDGET.md) tests
stronger one-variable distribution and additive Fourier control against
the complete signed budget. It obtains no positive total margin. No
additional Lean formalization was undertaken without an analytic gain.

At the prime-isolating threshold sqrt(2X+2), the lower linear-sieve
coefficient is 2 C exp(-gamma) f(2theta)=0 for every theta<=1.
The assessment retains its approximation, product, progression,
even-input and prime-power residuals. The application uses a fixed
sieve sublevel to respect the source theorem's quantifiers. Hypothetical
larger distribution exponents can lower the middle-class constant,
but do not bound R. The upper calculation keeps odd squarefree
moduli, q as their unique largest prime, a uniform finite parameter
mesh, and the full finite main-sum discrepancy.

For the additive route, exact shifted supports give the major/minor
identity with phase +2. A one-sided minor-arc bound
N_X>=-(1-delta) C X cofinally would improve the *total* loss T+R by
delta; the 0.263 bound is not counted again. The major-arc error
includes the actual approximation errors, singular-series tail and
singular-integral tail. The endpoint correction on equalizing supports
is exact. Cauchy-Schwarz gives only an X log X loss. Global L2 after
diagonal subtraction is at least (1/sqrt(2)+o(1))X^(3/2).

An explicit nonnegative Fejer comparison density has diagonal mean
D~X log X, nonnegative Fourier coefficients and nearby upper bounds,
major total C X+o(X), and shift-two coefficient exactly zero. Its minor
total cancels the entire leading term. Independent reviews checked the
coefficient cancellation, positivity, parameter C, support and arc tails.
It does not model actual Mangoldt coefficients or their full rational-arc
profiles. A separate exact error array shows why the inspected
almost-all-shift theorem permits shift 2 to be exceptional at every
scale, even with every fixed logarithmic saving.

The analytic value of this checkpoint is the quantified obstruction
and the resulting decision against formalizing these insufficient
estimates. The certified positive complete-budget margin remains zero.
The previously verified Lean build and axiom audit are unchanged.

## 2026-09-05 — Divisor switching and restricted moment budgets

The [divisor-switching assessment](DIVISOR_SWITCH_BUDGET.md) tests
actual arithmetic information from the shift-two Titchmarsh divisor
theorem against the complete budget. Its unrestricted divisor
minorant gives a lower expression with leading term
-kappa X log^2 X/2, including both Abel endpoint errors and the
prime-power defect. The same obstruction applies to the specified
class of fixed global polynomial prime minorants in the divisor count.

Restricting to squarefree rough inputs with prime shifted output
removes that large-scale obstruction, but requires a new restricted
moment estimate. For their mass M and divisor moment D, the exact
optimal bound is Q_tw>=max(0,2M-D/2). A cofinal bound
D<=4M-2delta C X would supply a positive total margin. The paper
does not prove it. Squarefree and shifted-prime-power removals are
bounded separately, including composite inputs to the latter.

The complete hyperbola identity retains prime and semiprime
divisors and the favorable multiplicity correction. The elementary
switched Selberg estimate has uniform constant 8C. Its balanced
region alone has an upper-charge coefficient at least 128/25=5.12,
exceeding even the available mass upper coefficient 4. This is
a lower bound on that upper estimate's charge, not on actual loss.
The better pointwise cap only restores a zero budget before the
other terms. Additional factorial moments express the missing
arithmetic but provide no proved gain.

Two independent reviews checked the finite defects, moment
optimization, divisor ranges, uniform sieve denominator, accumulated
error and rough-number asymptotic. Review clarified the clipped
interval length and the enlarged sum over all rough cofactors,
without a hidden restriction by shifted primality. The certified
positive complete-budget margin remains zero. No Lean source
changed, and the earlier build and axiom audit remain the verified
formal state. M4-M6 and the twin-prime conjecture remain unresolved.

## 2026-09-05 — Character bias and combined almost-prime constraints

The previous goal turn was progress: it recorded a reviewed
divisor-switching obstruction and changed the next analytic action.
This checkpoint tests a different mechanism in the
[character-bias budget](CHARACTER_BIAS_BUDGET.md).

The exact nonnegative model G_chi=(1*chi)*Lambda majorizes Lambda.
Its full shifted composite defect is displayed, including ramified
primes and prime powers. Two negative-character prime factors
annihilate its squarefree composite contribution. This explains
the possible arithmetic saving but does not estimate the defect.

The selected published Matomäki-Merikoski corollary does supply a
positive complete budget under a real zero of sufficient quality.
At X=q^10, subtracting its two prefix estimates costs
3KX exp(-sqrt(log eta)); removing Epp then gives the exact genuine
twin lower bound. A fixed sufficiently large quality, attained at
unbounded conductors, would yield Q_tw>=CX/2 cofinally.
The signed-loss transfer separately retains |J-CX|+Dcl+Dbeta,
with no duplicate Epp or middle-prime saving.

The missing condition is the unbounded supply of those zeros.
The inspected Lean Siegel value and zero-gap statements do not
produce zeros, and their actual region and quantifier restrictions
are preserved. A single zero supplies only a finite scale window.
The complementary case remains an unresolved signed-estimate problem.

The [combined Chen review](CHEN_WEIGHT_REVIEW.md#combining-the-existing-class-and-moment-inequalities)
also identifies the opposite orientations of its almost-prime
support and the rough-input support. It provides a compatible
leading assignment with zero twins satisfying the listed Chen,
moment, hyperbola and middle-prime budgets. A possible joint
leakage inequality is stated with its complete finite deficits;
none of the existing estimates supplies it.

Independent reviews checked the character algebra, source
hypotheses, dyadic endpoints, complete residuals and zero-existence
quantifiers. No unconditional positive margin was obtained.
No Lean source, import or axiom-audit selection changed. The
previous verified build remains the formal state; M4-M6 are open.

## 2026-09-05 — Fixed-pair extraction and an exact marginal ceiling

The previous goal turn was progress: it tested exceptional-character
bias and identified its missing zero-existence quantifier, while
the combined Chen estimates still allowed zero twin mass. This
turn tests a different mechanism in
[FIXED_PAIR_EXTRACTION_BUDGET.md](FIXED_PAIR_EXTRACTION_BUDGET.md).
The current PLAN already excludes standard M2 optimization; the
new work instead checks larger-tuple extraction and the full
two-coordinate marginal criterion in Polymath8b Theorem 3.14.

Admissibility makes the difference-2 graph a matching. Its
independence threshold is at least half the tuple size. The
exact occupied-edge identity retains the favorable empty-component
mass, and the standard Maynard lower budget stays negative.
The transfer to the actual dyadic twin sum keeps the maximum
weight and covers translated endpoints by two disjoint dyadic
intervals. Signed weights retain an explicit negative-part defect;
forcing auxiliary forms composite by CRT loses their prime mass.

For the enlarged two-coordinate marginal functional, a direct
Hilbert-space norm identity proves an upper bound 2 and a
piecewise constant function attains it for every permitted epsilon.
The proof includes the integrability at zero needed for arbitrary
L2 inputs. Thus this larger domain still cannot meet the strict
threshold. An untruncated-marginal substitution would give an
apparent positive coefficient, but its missing prime-sum input
can require moduli beyond the assumed distribution range.
That coefficient is explicitly not claimed as an estimate.

Independent reviews checked the exact norm calculation, source
conditions, graph identity, residual signs, finite transfer and
the congruence-class examples separating qualitative clusters
from a prescribed pair. No unconditional gain was obtained.
The certified full-budget margin is still zero. No Lean source,
import or audit selection changed; the prior formal verification
remains current. M4-M6 and the full conjecture remain open.

## 2026-09-05 — Gowers uniformity and a sparse fixed-shift comparison

[GOWERS_FIXED_SHIFT_BUDGET.md](GOWERS_FIXED_SHIFT_BUDGET.md)
tests quantitative Gowers uniformity as a mechanism distinct from
the previous tuple-sieve assessment. The inspected theorem retains
its exceptional-character correction; its affine-pattern theorem
does not apply to the dependent linear vectors of n and n+2.

The exact finite replacement is Q_tw=M+H+K-Epp, with one common
model, both mixed terms, and the actual shifted masks. Fourier
orthogonality gives a p^(3/2) product-of-U2-norms charge for K.
Padding is exact and masks cost only a logarithm, but the supplied
rate does not overcome the remaining polynomial loss. A bounded
quadratic-phase example verifies that loss cannot generally be
replaced by a logarithm.

A sparse probabilistic construction strengthens the obstruction.
Its normalized nonnegative weight has mean one, height O(log N),
support size asymptotic to N/log N, and no shift-two pairs.
Its centered Gowers norms are O_S(log N N^(-1/2^s)) for all
1<=s<=S simultaneously, for every fixed finite S. The separate
interval argument counts valid cubes and retains the exact four
boundary weights in its centered correlation.

Three independent reviews checked the primary-source hypotheses,
Fourier normalization, finite budget, probabilistic construction,
interval norm convention and signed-loss transfer. Review clarified
the Fourier counting measure and distinguished the padding endpoint
Y from the middle-prime loss T. These comparison weights do not
model all arithmetic information about the primes.

The complete budget still requires a new arithmetic estimate for
H+K, along with control of the model deficit. No positive actual
margin was obtained. No Lean source, import or audit selection
changed; the prior successful build remains the formal state.
M4-M6 and the twin-prime proof remain unresolved.

## 2026-09-05 — Weighted distribution and discrete endpoint cofactors

The previous Gowers assessment changed the next analytic action:
norm and density information alone could not supply the fixed-shift
gain. This turn tested actual weighted progression inputs and
then a different mechanism based on prime-factor distributions.

[CUTOFF_SHIFT_ROUTE.md, Section 6](CUTOFF_SHIFT_ROUTE.md#6-current-cutoff-weighted-distribution-and-its-full-residual)
now keeps the complete factorable-approximation error, coefficient
sum, outer tail and quotient-sieve defect. The enlarged seven-prime
support obstruction has positive limiting harmonic mass; this
invalidates one elementary o(X) deletion argument without asserting
a lower bound on actual prime-shift mass. Even on admissible moduli,
the current forced-prime-quotient range leaves a sieve parameter
below 1 at the tested 5/8 level.

Primary-source inspection also found Yang's preprint revised
3 September 2026. Its stronger convolution level keeps one integer
factor unweighted, and does not insert the extra shifted-prime
condition. The proof uses that unweighted variable in Poisson
summation. The arbitrary-coefficient result separately displayed
there is the older square-root-level theorem. Maynard's absolute
error theorem on product moduli was checked separately; its
maximum product exponent is below the current forced-quotient range.

[PRIME_FACTOR_ENDPOINT_BUDGET.md](PRIME_FACTOR_ENDPOINT_BUDGET.md)
gives the exact identity H_K=Q_tw+D_K for the largest-prime-factor
tail, with all odd integer cofactors k<K in D_K. For 1<K<=3 the
tail equals the genuine twin mass. This yields exact microscopic
plateaus and rules out an o(1/log X) extension of the continuous
limiting prediction at two distinct widths below log 3.

The endpoint calculation retains the actual prime-output count,
finite logarithmic-weight error, all cofactor leakage and the
signed-budget Epp term. Fixed-parameter weak convergence remains
uncontradicted; it supplies no such microscopic lower bound.
Independent review checked the source restrictions and finite
identities. The certified positive full-budget margin remains zero.
No Lean source, import or audit selection changed. The existing
middle-prime theorem and successful build were re-inspected;
no new formalization was justified or attempted.

## 2026-09-05 — Complete-budget gate and research impasse

The preceding goal turn made diagnostic progress: its exact
endpoint plateaus and source checks removed unsupported
applications. It did not improve the complete budget.
The same missing signed arithmetic estimate persisted through
the fixed-pair, Gowers, and weighted-distribution/endpoint turns.
The terminology of those mechanisms did not change the blocker.

The present gate audit re-read the actual Lean theorem arguments,
root imports, build and axiom logs, and the full error ledger.
The middle-prime class theorem has no unproved arithmetic premise.
The twin-prime endpoints still require hB or hgain explicitly.
Independent mathematical reinspection found no overlooked gain
from combining the existing class, rough-mass and composite-mass
inequalities. The favorable composite term is correlated with
the same identity and cannot be counted again.

The assessed exceptional-zero route has a positive conditional
budget, but its required unbounded zero supply is unproved.
The other assessed mechanisms retain an unestimated signed
correlation, a missing selector, or insufficient precision.
No currently justified next derivation from the available inputs
was identified that would improve the complete inequality.

This is an impasse in the present research run, not an impossibility
theorem about future approaches. A new arithmetic proof argument or
applicable input is required to resume substantive progress.
Further rephrasing or formalization of the same missing estimate
would not meet the research program's progress criterion. The full proof and
its unconditional Lean formalization remain incomplete.
