# Computation tools

These programs provide finite diagnostics and numerical experiments. They do
not prove an asymptotic estimate or the Twin Primes Conjecture. The exact
integer-coefficient checks are separate from floating-point displays.

Run the following small checks from the repository root. The ordinary Python
diagnostics use only the standard library; the Rust crates have no external
dependencies. This checkpoint was tested with Python 3.12.10 and Rust 1.96.0.

```sh
python -B -m unittest discover -s compute -p "test_*.py" -v
python -B compute/type_i_switch_check.py
python -B compute/smoothing_check.py
cargo test --offline --manifest-path compute/parity/Cargo.toml
cargo test --offline --manifest-path compute/twinsieve/Cargo.toml
```

| Tool | Purpose |
|---|---|
| `correlation.py` | Exact finite Vaughan decomposition and factor-box checks; see [CORRELATION.md](CORRELATION.md). |
| `sign_diagnostics.py` | Exact signs of selected logarithmic coefficients. |
| `type_i_switch_check.py`, `smoothing_check.py` | Finite witnesses for the documented limitations of switching and smoothing. |
| `twinsieve` | Segmented CPU twin counts, with floating-point Brun sums and Hardy–Littlewood comparisons. |
| `parity` | Sifted product-Omega statistics, including explicit zero-denominator output. |
| `parity`'s `liouville_disc` binary | Legacy experimental Liouville discrepancy table on `0 <= n <= N`, matching the Lean interval convention. Use small positive integer arguments; its legacy scientific-notation parser uses floating point. |

Small Rust command-line examples:

```sh
cargo run --offline --manifest-path compute/twinsieve/Cargo.toml -- 1000 100 1000
cargo run --offline --manifest-path compute/parity/Cargo.toml --bin parity -- 1000 3 10
cargo run --offline --manifest-path compute/parity/Cargo.toml --bin liouville_disc -- 1000 30
```

The two `gpu/` scripts additionally require PyTorch; `twinsieve_torch.py` also
requires NumPy. They support CPU fallback. Their default experiments can use
substantial memory and time and are not part of the ordinary test suite. A
legacy floating-point parser remains in the GPU sieve; use small integer
endpoints for checks rather than relying on it above binary64's exact range.
The functional script has a small, explicitly CPU-only check:

```sh
python -B -c "import torch; from compute.gpu.maynard_mk import mk_lower_bound; print(mk_lower_bound(2, 8, iters=80, dev=torch.device('cpu')))"
```

The functional values and Richardson extrapolations are uncertified numerical
estimates. In exact arithmetic the Galerkin Rayleigh quotient is a variational
lower bound, but this implementation does not certify floating-point rounding.

Keep source files, tests, Cargo manifests and lockfiles, and the selected
`correlation_results/2026-09-04/{summary.json,boxes.csv}` record. That historical
record includes a provenance note explaining path sanitization; its numeric
payload and original source/interpreter hashes are unchanged. Give each new
experiment a new output directory; do not replace historical results.

Cargo `target/` directories, Python `__pycache__/` and `.pyc` files, virtual
environments, and temporary experiment outputs are local artifacts, not source.
The existing repository ignore rules cover the Cargo and Python caches. Review
new result files before choosing to preserve them, including command-line paths
and other machine-specific metadata. No large experiment is required to run the
bounded checks above.
