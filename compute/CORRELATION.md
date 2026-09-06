# Finite correlation diagnostics

`correlation.py` measures exactly the quantities in Sections 4 and 6 of the root
`PLAN.md`, with `X < n <= 2X`, shift 2, and integer cutoffs. Its default cutoffs
are `U = V = floor(X^(1/5))`, computed without floating-point rounding.

Run from the repository root:

```powershell
python -m unittest discover -s compute -p "test_*.py" -v
python compute/correlation.py --X 1000 10000 100000 --output-dir compute/correlation_results/new-run
```

Choose a new output directory for each later run. The program refuses to replace
existing `summary.json` or `boxes.csv` files.

The summary records `A_U`, `H_U`, `I_UV`, `B_UV`, `K_UV = H_U - I_UV`, `W_2`,
the proper-prime-power contribution `E_pp`, and the direct number of twin pairs.
Every identity is tested as equality of integer coefficients of the formal
products `log(p)log(q)`. Zero residual here means an exact finite algebra check;
no conjecture, asymptotic formula, or lower-bound assumption is used. The script
also checks 8,000 instances of Vaughan's identity in the linear `log(p)` basis.

The two enumerations are deliberately different: direct sums over `n` and its
divisors are checked against the Type I progression sum and the bilinear sum
over `(d,r)`. `beta_V(r)` is computed both from divisors greater than `V` and
from `log(r)` minus the complementary divisor sum. The coefficient bounds are
checked coefficient by coefficient. These finite checks do not replace general
proofs in Lean.

Each CSV row describes one disjoint box `M < d <= 2M`, `N < r <= 2N`, retaining
`d > U`, `r > V`, and `X < dr <= 2X`. Zero terms are included in the factor-pair
count so the coverage check tests the complete range. The file records positive,
negative, signed, and absolute contributions, plus the signed and absolute
contributions for which **the shifted value `dr+2` is a proper prime power**.
That last statistic belongs to `B_UV`; it is different from `E_pp`, which belongs
to `W_2` and includes either nonprime member. Non-squarefree `r` occurrences are
reported separately. Nonzero terms automatically have squarefree `d`, since
their coefficient contains `mu(d)`.

The JSON stores the source commit, dirty-tree status, source and interpreter
SHA-256 hashes, interpreter/platform details, arguments, UTC timestamp, exact
coefficient hashes, and arithmetic precision. CSV rows repeat the core source
and binary provenance. The script path is repository-relative and the interpreter
path contains only its basename. When Git metadata is unavailable (for example,
in a source archive), the commit and dirty-tree fields are null and explicitly
marked unavailable; source/interpreter hashes are still recorded. Command-line
arguments are retained as supplied, so use relative output paths for portable
records. The saved 2026-09-04 summary includes a note documenting the removal of
its two original machine-specific paths; its numerical results and historical
hashes are unchanged. Coefficients use arbitrary-precision integers; displayed
real values use binary64 logarithms and `math.fsum`, without rigorous rounding
intervals. The constant used only for numerical normalization is the displayed
approximation to `2 C_2`.

No bound at infinity is inferred from these outputs. In particular, negative
box measurements and absolute-value totals do not prove or disprove the
cofinal signed bound (B*). The CSV's `applicable_proved_lower_bound` fields remain
empty because no new uniform box estimate has been established.

The focused `python compute/smoothing_check.py` checks logarithmic cutoff
averaging with exact integer log-prime coefficients, including its lower
window endpoint and prime-only beta convolution. It also verifies the
negative-change witness 381=3*127 with shifted prime 383 and the compensating
finite A+H-I term, and a second witness 1011=3*337 with shifted prime1013
at the exact primary/quarter cutoffs X=1000,R=3,W=5. Its 4,800 averaging
and 9,600 convolution identities are
finite checks, not a formal proof or a statement about the asymptotic center.
See the [smoothing review](../docs/SMOOTHED_SIGNED_GAIN_REVIEW.md).
The same checker also verifies a power-window witness at X=100000,
S=3,R=10,W=17: n=100055=5*20011 has prime shift100057 and window
coefficient strictly between zero and one. Its positive part therefore
exceeds its square. This is an exact finite obstruction to a proposed
majorant, not an estimate at infinity.
