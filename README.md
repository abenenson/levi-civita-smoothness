# Levi-Civita smoothness preparation

This repository isolates the smooth Levi-Civita construction from the library and prepares a bridge to
Mathlib's existing `CovariantDerivative.leviCivitaConnection`. It is a local preparation package,
not an upstream contribution already accepted or submitted.

The extracted source is pinned to the library commit
`recorded-source-baseline`. The 19 files (5,037 lines) are byte-for-byte
verified against that Git object; their hashes are in
[`evidence/construction/source-manifest.json`](evidence/construction/source-manifest.json).
The copied file headers retain their historical project descriptions; the current-upstream
comparison below supersedes any novelty claims in that prose.

The package uses Lean **4.34.1** and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Current upstream was separately inspected at
`e293c42021c641734f10655c39b8023fa88ff6ee`, using Lean **4.36.0-rc2**. The source snapshots
under `evidence/upstream` are evidence, excluded from the Lean library roots. Their attribution
headers are preserved.

Mathlib already proves existence and uniqueness of Levi-Civita connections. The contribution
opportunity is regularity of its chosen connection, with explicit attention to local section
inputs and loss of derivatives. the library's result only constructs an operator on global smooth
sections. These statements must be bridged; they are not interchangeable.

The new bridge now proves, on the pinned Mathlib version, that its chosen Levi-Civita derivative
agrees with the library's smooth output on global smooth input pairs. It transfers `ContMDiff ... ∞`
regularity to that evaluation. The canonical application installs the Riemannian structure
from the supplied metric, so no independent metric agreement assumption is required:

* [`KoszulTransfer.lean`](LeviCivitaSmoothness/KoszulTransfer.lean): pointwise uniqueness and
  transfer of smoothness from the Koszul identities.
* [`MathlibBridge.lean`](LeviCivitaSmoothness/MathlibBridge.lean): identification with
  `CovariantDerivative.leviCivitaConnection` and smoothness on global smooth pairs.
* [`MetricApplication.lean`](LeviCivitaSmoothness/MetricApplication.lean):
  `contMDiff_leviCivitaConnection_fromMetric`, using precisely the metric supplied as data.

See [`docs/api-comparison.md`](docs/api-comparison.md) for the exact interfaces and limitations,
and [`evidence/upstream/pr-status.json`](evidence/upstream/pr-status.json) for overlapping
upstream work. No public PR, issue, or comment has been created from this package.

## Validation status

The 19-file extracted source cone passed `lake --rehash --wfail build` on qualified Lean
4.34.1 with the pinned Mathlib dependency. No extracted file was changed. The source hashes and
upstream Git blob hashes also pass `python3 scripts/verify_evidence.py`.

The new bridge, canonical metric application, both library roots, and
[`AxiomAudit.lean`](LeviCivitaSmoothness/AxiomAudit.lean) passed a separate strict build.
The audited source existence and bridge theorems depend only on `propext`, `Classical.choice`,
and `Quot.sound`; no new axioms or placeholders are introduced.

See [`evidence/validation.json`](evidence/validation.json) for exact scope, proof hashes, and
successful build receipts. Reproduce the checks with:

```sh
python3 scripts/verify_evidence.py
lake --rehash --wfail build +MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentExistenceTheorem:olean
lake --rehash --wfail build +LeviCivitaSmoothness.AxiomAudit:olean +LeviCivitaSmoothness:olean +MathlibExtensions:olean
```

Full Hom-valued connection regularity, finite derivative loss, arbitrary-set local input
regularity, and a current-master port remain separate work. This package does not claim those
theorems or an accepted upstream contribution.
