# twinprime

Lean 4 formalizations and computational tools for research on the twin prime
conjecture.

**This repository does not prove the twin prime conjecture.** The target is
infinitude of the set

```lean
{p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}
```

It is recorded as the proposition `TwinPrime.TwinPrimeConjecture` in
[Basic.lean](TwinPrime/Basic.lean). The remaining signed fixed-shift estimate
is explicitly identified in the [proof-obligation ledger](docs/PROOF_OBLIGATIONS.md).

## Mathematical scope

- **Unconditional formal results:** Brun's theorem, sieve bounds, finite
  correlation and prime-power identities, and a classical analytic chain proving
  centered Siegel–Walfisz, maximal Bombieri–Vinogradov, and quantitative Mertens
  estimates. See the [classical proof map](docs/CLASSICAL_DISTRIBUTION_THEOREM.md).
- **Partial signed-sum results:** exact factor partitions, negligible-error
  range removals and cutoff changes, and an eventual upper bound of `0.263 C X`
  for one complete negative middle-prime class, where `C = 2 C₂`. This class
  bound does not give a positive margin for the full sum. See the
  [complete signed budget](docs/SIGNED_TOTAL_BUDGET.md).
- **Conditional twin-prime theorems:**
  [ConditionalSignedBilinear.lean](TwinPrime/ConditionalSignedBilinear.lean)
  supplies the classical inputs but assumes the open cofinal signed estimate
  `(B*)`. [ConditionalClassicalCenter.lean](TwinPrime/ConditionalClassicalCenter.lean)
  gives an alternative implication from a cofinal logarithmic gain above the
  exact finite center; that gain is also unproved.
- **Computational work:** exact finite algebra checks, twin-prime counts, and
  signed-coefficient diagnostics. Finite experiments do not establish bounds
  at infinity; displayed floating-point values are not rigorous certificates.

The conjecture's proof still requires new arithmetic controlling the surviving
signed contribution at shift `2`. A successful build of a conditional theorem
does not supply its missing hypothesis.

## Build and verification

Run commands from the repository root. Install Lean through `elan`; the
[toolchain file](lean-toolchain) selects Lean `4.32.0`.
[lakefile.toml](lakefile.toml) pins Mathlib to `v4.32.0`, with dependency revisions
recorded in [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The first command downloads Mathlib's compiled cache. The audit reports axiom
dependencies for selected declarations and prints the types of key conditional
endpoints. Inspect the hypotheses as well as the axiom lists: using only
standard Lean axioms does not make a conditional result unconditional.

Run the portable source check for proof holes and disallowed trust shortcuts:

```sh
python scripts/check_proof_hygiene.py
```

CI runs the build, validates the selected axiom reports against the audit
script and standard-axiom allowlist, and runs the bounded Python and Rust
checks below. The source checker is an additional guard, not a Lean parser.

Detailed verification records and mathematical reviews are maintained in the
[ledger](docs/PROOF_OBLIGATIONS.md#verification-and-provenance) and
[analytic review](docs/ANALYTIC_REVIEW.md).

## Computational checks

The following Python checks use Python 3.10 or later and its standard library:

```sh
python -m unittest discover -s compute -p "test_*.py" -v
python compute/type_i_switch_check.py
python compute/smoothing_check.py
```

For the Rust tools, install a Rust toolchain with Cargo:

```sh
cargo test --locked --manifest-path compute/twinsieve/Cargo.toml
cargo test --locked --manifest-path compute/parity/Cargo.toml
cargo run --release --locked --manifest-path compute/twinsieve/Cargo.toml -- 100000 1000 10000 100000
```

The last command is a small sieve example. See
[compute/CORRELATION.md](compute/CORRELATION.md) for diagnostic output formats,
exact coefficient checks, and reproducibility conventions. Optional GPU
experiments are separate from the Lean build and these tests.

## Repository guide

| Path | Contents |
|---|---|
| [TwinPrime.lean](TwinPrime.lean) | Root module importing the formal library |
| [TwinPrime/](TwinPrime/) | Lean definitions, proofs, and conditional endpoints |
| [compute/](compute/) | Rust sieves and Python diagnostics |
| [data/](data/) | Computational tables |
| [scripts/](scripts/) | Proof-source check and selected-declaration audit |
| [PLAN.md](PLAN.md) | Research program and acceptance criteria |
| [docs/PROOF_OBLIGATIONS.md](docs/PROOF_OBLIGATIONS.md) | Proven results, assumptions, and current milestones |
| [docs/SIGNED_TOTAL_BUDGET.md](docs/SIGNED_TOTAL_BUDGET.md) | Exact remaining inequality and every residual term |
| [docs/RESEARCH_LOG.md](docs/RESEARCH_LOG.md) | Research history and unsuccessful approaches |

## Research provenance

This is an **AI-assisted research project**. AI systems have been used
extensively to draft Lean proofs, computational code, literature assessments,
and research notes. Formal results should be evaluated by their exact checked
statements and assumptions. Paper arguments, source interpretations, and
numerical observations remain distinct from kernel-checked proofs and warrant
independent review. The technical notes preserve both successful reductions
and failed approaches; they do not constitute a claimed proof of twin-prime
infinitude.

The [provenance notes](docs/PROVENANCE.md) explain the consolidated Git history
and historical experiment hashes. [Data notes](data/README.md) describe the
limits of the saved numerical tables.

## License and attribution

Licensed under [Apache-2.0](LICENSE). The Selberg sieve port retains attribution
to Arend Mellendijk; see [NOTICE](NOTICE). Dependencies retain their own licenses.
