# Source and experiment provenance

This repository is an AI-assisted research project, not a proof of the twin
prime conjecture. The [README](../README.md) describes the current scope, and
the [proof-obligation ledger](PROOF_OBLIGATIONS.md) distinguishes established
formal results from the remaining hypotheses.

## Consolidated source history

The initial publication snapshot consolidates the local development history
into one commit. Earlier research decisions and failed approaches remain in
the [research log](RESEARCH_LOG.md) and route reviews. An archival copy of the
original history and source files is retained locally by the maintainer.

Commit identifiers recorded in older research notes and experiment metadata
refer to that original development history. They are preserved as historical
provenance and may not resolve in the consolidated repository. They should not
be read as identifiers for the current source snapshot. New runs record their
own revision when Git metadata is available.

Personal workspace paths and account or orchestration details were removed
from the documentation. Local source links were made repository-relative;
Mathlib source links use the revision pinned by the dependency manifest.
These editorial changes do not alter the mathematical statements.

## Historical numerical records

The selected correlation record in
[`compute/correlation_results/2026-09-04/`](../compute/correlation_results/2026-09-04/)
retains its original numerical payload, CSV, source commit, script hash, and
interpreter hash. Two machine-specific path fields were shortened, and a
`provenance_note` records this change. Those hashes describe the original run,
not the subsequently edited scripts. Reproducing a result means rerunning the
documented computation and comparing the numerical output; it need not produce
the same interpreter hash on another platform.

The current correlation tool records its repository-relative source path and
the interpreter's basename. Source archives without Git metadata report that
limitation explicitly. New experiment output belongs in a new directory, so
the selected historical results remain intact. The [computation guide](../compute/README.md)
and [data notes](../data/README.md) describe validation and numerical limits.

## Formal verification and review

The toolchain and dependency lockfile identify the Lean and Mathlib versions.
`lake build` checks the imported formal library. `scripts/Axioms.lean` prints
axiom dependencies for selected declarations and types of key endpoints.
The portable source and audit-log checker is an additional guard; it is not
a replacement for Lean's kernel or a proof that every paper argument is valid.

A theorem depending only on standard Lean axioms can still have an unproved
mathematical hypothesis. In particular, the signed-bilinear and logarithmic-gain
twin-prime implications remain conditional. Computational checks are finite,
and prose reviews are separate from kernel-checked statements.

Upstream source attribution and modification notices appear in
[NOTICE](../NOTICE) and the ported source files.
