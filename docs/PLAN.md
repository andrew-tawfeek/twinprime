# Program

Historical program. The current dependency plan and corrections are in
[../PLAN.md](../PLAN.md). The phase labels below describe the original work, not completion
of the current proof goal. In particular, the parity inequalities do not themselves bound
the Liouville discrepancy or give a lower bound for twin primes.

Target: `{p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite`.

The plan is organised so that every step either (i) adds a machine-checked theorem to the
formal library, (ii) adds verified computational evidence, or (iii) sharpens the statement of
what remains. No step is allowed to be "we believe". The log in `RESEARCH_LOG.md` records the
outcome of each step, including failures.

## Phase 0. Infrastructure (2026-09-04)

* Lean 4 `v4.32.0` + Mathlib `v4.32.0`, with a successful `lake build`.
* Rust multithreaded segmented sieve (`compute/twinsieve`), exact `pi_2(x)` and Brun partial
  sums; validated against the literature values up to `1e9`; run to `1e13`.
* GPU sieve experiments implemented with PyTorch `2.13+cu130`.
* git initialised.

## Phase 1. Elementary formal layer (`TwinPrime/Basic.lean`)

1. `twinPrimes`, `TwinPrimeConjecture : Prop`, decidable membership, verified small cases.
2. Equivalent formulations: unbounded set; `∀ N, ∃ p > N`; `∃ᶠ n in atTop`; infinitely many `k`
   with `6k-1, 6k+1` both prime.
3. Structure: every twin prime `p ≥ 5` has `p % 6 = 5`; the pair is `(6k-1, 6k+1)`.
4. Clement's criterion (1949): for `n ≥ 2`, `n` and `n+2` are both prime iff
   `n (n+2) ∣ 4 ((n-1)! + 1) + n`. Proof from Wilson's theorem (Mathlib has both directions of
   Wilson).
5. Sufficient conditions, each as a theorem `H → TwinPrimeConjecture`: any eventual lower bound
   `pi_2(x) ≥ c x / (log x)^2`; the Hardy–Littlewood asymptotic; de Polignac for gap 2;
   Dickson's conjecture for the pair `(n, n+2)`.

## Phase 2. Brun: the sieve upper bound (`TwinPrime/Sieve/*`)

Mathlib (`Mathlib/NumberTheory/SelbergSieve.lean`) contains the Selberg sieve *setup*: bounding
sieves, upper-bound (Λ²) weights, and the diagonalisation of the main term. It stops before the
*fundamental theorem* (optimal weights, the bound `X / S(y)`, the `3^{ω(d)}` error bound). Plan:

1. Complete the fundamental theorem of the Selberg upper-bound sieve:
   `siftedSum ≤ X / S + Σ_{d ∣ P, d ≤ y} 3^{ω(d)} |R_d|`, with `S = Σ_{l ∣ P, l ≤ √y} g(l)`.
2. The twin sieve problem: support `{1..x}`, weight `1`, `P = ∏_{p ≤ z} p`,
   `ν(p) = ρ(p)/p` with `ρ(2) = 1`, `ρ(p) = 2` (`p` odd); `|R_d| ≤ ρ(d) ≤ 2^{ω(d)}`.
3. Lower bound for `S` **without Mertens' theorem** (Mathlib lacks Mertens): the elementary
   expansion `g(l) = ∏_{p∣l} (ν(p)/(1-ν(p)))` gives `S ≥ Σ_{n ≤ √y, n odd} 2^{ω(n)}/n ≥ c (log y)^2`,
   using only harmonic-sum bounds (`Mathlib/NumberTheory/Harmonic/Bounds.lean`).
4. Error bound: `Σ_{d ≤ y} 6^{ω(d)} ≤ y (1 + log y)^5` via `Σ_{d ≤ y} τ_k(d) ≤ y (1 + log y)^{k-1}`
   (elementary induction on `k`), or the cruder `|λ_d| ≤ 1` route.
5. Conclude `pi_2(x) ≤ C x / (log x)^2` for `x ≥ 2` with an explicit `C`, then Brun's theorem:
   `Summable (fun p : twinPrimes => 1/p)` by dyadic decomposition.

Milestone: **Brun's theorem, machine-checked in Lean 4**.

## Phase 2.5. Lower bounds by Legendre's sieve — DONE (2026-09-04)

`twinRough_infinite`: infinitely many `n` with all prime factors of `n(n+2)` above `log n/(2 log 3)`.

## Phase 3. The lower-bound side (research)

The formal library will make the obstruction precise rather than hide it.

1. State the "parity phenomenon" as a theorem about bounding sieves (Selberg's example) —
   DONE (2026-09-05), `Parity.lean`: for every lower-bound sieve `μ⁻` and `z² > x`, the sieve
   expression for the twin sequence is `≤ ∑_{d ∣ P(z)} |μ⁻(d)| |Λ_d|`, `Λ_d` a Liouville sum
   (`parity_obstruction`); unconditional. The discrepancy estimate needs explicit uniformity,
   rates, multiplicities, and summation losses. A fixed-modulus theorem does not supply
   these. Bounding this discrepancy does not reverse the inequality into a twin-prime lower
   bound; the current program isolates a separate signed bilinear estimate.
2. Numerically explore (GPU) the Maynard–Tao functional `M_k` and the GPY sieve for the tuple
   `(0, 2)`: confirm that the optimum for `k = 2` cannot exceed the threshold even under the
   strongest distribution hypotheses, documenting exactly why bounded gaps `≤ 246` / `≤ 6` do not
   reach `2`.
3. Brun's pure sieve (Bonferroni truncation) — DONE (2026-09-05): `brun_almostPrime_infinite`,
   infinitely many `n` with `Ω(n) + Ω(n+2) ≤ 6000 log log n`.
4. Brun–Hooley combinatorial sieve — DONE (2026-09-05): `brun_bounded_infinite`, infinitely many
   `n` with `Ω(n) + Ω(n+2) ≤ 4001`.  Beyond this: Chen's theorem (`p + 2 = P₂`) needs
   Bombieri–Vinogradov and the switching principle — a different scale of project.
5. Investigate what *additional* input (Type II / bilinear information) would suffice, and
   formalise conditional theorems `H → TwinPrimeConjecture` with `H` as weak as we can make it.

## Phase 4. Computation

* Exact `pi_2(x)` to `1e13` (CPU); compare with `2 C_2 ∫_2^x dt/(log t)^2`; Brun constant.
* GPU: sieve-weight optimisations (Selberg / Maynard quadratic forms), and brute-force checks of
  candidate inequalities on finite ranges that feed back into Phase 2/3 constants.

## Ground rules

* No `theorem` may contain `sorry`. Open statements are `def ... : Prop`.
* Every computational claim recorded in the log is reproducible by a command in `scripts/`.
* Commit at every milestone; the log entry cites the commit.
