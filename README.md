# Levi-Civita smoothness preparation

This repository isolates the smooth Levi-Civita construction from the library and prepares a bridge to
Mathlib's existing `CovariantDerivative.leviCivitaConnection`. It is a local preparation package,
not an upstream contribution already accepted or submitted.

The extracted source is pinned to the library commit
`recorded-source-baseline`. The 19 files (5,037 lines) are byte-for-byte
verified against that Git object; their hashes are in
[`evidence/construction/source-manifest.json`](evidence/construction/source-manifest.json).

The package uses Lean **4.34.1** and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Current upstream was separately inspected at
`e293c42021c641734f10655c39b8023fa88ff6ee`, using Lean **4.36.0-rc2**. The source snapshots
under `evidence/upstream` are evidence, excluded from the Lean library roots. Their attribution
headers are preserved.

Mathlib already proves existence and uniqueness of Levi-Civita connections. The contribution
opportunity is regularity of its chosen connection, with explicit attention to local section
inputs and loss of derivatives. the library's result only constructs an operator on global smooth
sections. These statements must be bridged; they are not interchangeable.

See [`docs/api-comparison.md`](docs/api-comparison.md) for the exact interfaces and limitations,
and [`evidence/upstream/pr-status.json`](evidence/upstream/pr-status.json) for overlapping
upstream work. No public PR, issue, or comment has been created from this package.

## Validation status

The extraction and source hashes have been verified. Lean compilation is pending the shared
serial build lane. Source inspection alone is not reported as kernel validation.
