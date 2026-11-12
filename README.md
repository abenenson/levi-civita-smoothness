# Levi-Civita smoothness preparation

[![Lean verification](https://github.com/abenenson/levi-civita-smoothness/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/abenenson/levi-civita-smoothness/actions/workflows/lean.yml)

This repository proves global smoothness of Mathlib's `CovariantDerivative.leviCivitaConnection`
from a smooth metric. A direct Koszul construction is identified with Mathlib's chosen derivative
to transfer smoothness. It is a local preparation package, not an upstream contribution already accepted
or submitted.

The 19 core construction files (5,037 lines) have their source identities recorded in
[`evidence/source-manifest.json`](evidence/source-manifest.json).
The current Mathlib interface comparison below describes their relationship to upstream.

The package uses Lean **4.34.1** and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Upstream was separately inspected at
`e293c42021c641734f10655c39b8023fa88ff6ee`, using Lean **4.36.0-rc2**. The source snapshots
under `evidence/upstream` are evidence, excluded from the Lean library roots. Their attribution
headers are preserved.

Mathlib already proves existence and uniqueness of Levi-Civita connections. The contribution
opportunity is regularity of its chosen connection, with explicit attention to local section
inputs and loss of derivatives. The direct construction acts on global smooth sections. These statements must be bridged;
they are not interchangeable.

The new bridge now proves, on the pinned Mathlib version, that its chosen Levi-Civita derivative
agrees with the local construction's smooth output on global smooth input pairs. It transfers `ContMDiff ... ∞`
regularity to that evaluation. The canonical application installs the Riemannian structure
from the supplied metric, so no independent metric agreement assumption is required:

* [`KoszulTransfer.lean`](LeviCivitaSmoothness/KoszulTransfer.lean): pointwise uniqueness and
  transfer of smoothness from the Koszul identities.
* [`MathlibBridge.lean`](LeviCivitaSmoothness/MathlibBridge.lean): identification with
  `CovariantDerivative.leviCivitaConnection` and smoothness on global smooth pairs.
* [`MetricApplication.lean`](LeviCivitaSmoothness/MetricApplication.lean):
  `contMDiff_leviCivitaConnection_fromMetric`, using precisely the metric supplied as data.

Import `LeviCivitaSmoothness.HomRecovery` for the full global regularity result:

```lean
CovariantDerivative.ContMDiffCovariantDerivative
  (CovariantDerivative.leviCivitaConnection I M) ∞
```

[`HomRecovery.lean`](LeviCivitaSmoothness/HomRecovery.lean) recovers smoothness of the full
Hom-valued derivative from its evaluations on global smooth sections. The theorem
`contMDiffCovariantDerivative_leviCivitaConnection_fromMetric` installs the supplied metric and
proves this class under the preserved smooth-manifold, finite-dimensional, Hausdorff, and
complete-space hypotheses. An explicit metric-agreement version is also provided.

See [`docs/api-comparison.md`](docs/api-comparison.md) for the exact interfaces and limitations,
and [`evidence/upstream/pr-status.json`](evidence/upstream/pr-status.json) for overlapping
upstream work. No public PR, issue, or comment has been created from this package.

## Validation status

The 19-file source cone passed `lake --rehash --wfail build` on qualified Lean
4.34.1 with the pinned Mathlib dependency. A later comment-only scope wording update in
`TangentVectorFieldDerivation.lean` refreshed its public source inventory digest without
changing Lean code tokens. Historical build and lint receipts retain their original scope;
Lean was not rerun for this comment update. The current source inventory and upstream Git blob
hashes pass `python3 scripts/verify_evidence.py`.

The new bridge, canonical metric application, both library roots, and
[`AxiomAudit.lean`](LeviCivitaSmoothness/AxiomAudit.lean) passed a separate strict build.
The audited source existence and bridge theorems depend only on `propext`, `Classical.choice`,
and `Quot.sound`; no new axioms or placeholders are introduced.

The original [`evidence/validation.json`](evidence/validation.json) records the earlier
checkpoint that established smooth-pair evaluation. The additional
[`evidence/hom-validation.json`](evidence/hom-validation.json) records the successful full
global `C^∞` connection-class proof and its three axiom probes, again using only the same three
standard axioms. The later [documentation and lint checkpoint](docs/lint-checkpoint.md) adds
headers and the missing theorem documentation while preserving all mathematical proof code.
At that checkpoint, strict checks and full-source lint covered the recorded file hashes. Reproduce the
strict proof checks with:

```sh
python3 scripts/verify_evidence.py
python3 -m unittest discover -s scripts -p 'test_*.py'
lake --rehash --wfail build +MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentExistenceTheorem:olean
lake --rehash --wfail build +LeviCivitaSmoothness.AxiomAudit:olean +LeviCivitaSmoothness:olean +MathlibExtensions:olean
lake --rehash --wfail build +LeviCivitaSmoothness.HomRecovery:olean +LeviCivitaSmoothness.HomAxiomAudit:olean
```

The offline evidence checker requires all three validation receipts and checks their source,
build-log, and lint-probe hashes. The regression checks exercise missing receipts and source
changes in isolated copies without invoking Lean or accessing the network.

GitHub Actions repeats the offline checks, strict builds of **all 27 authored modules**
(the 19 construction files and eight new files), and the eight full-source lint probes on
the existing Lean 4.34.1 / Mathlib pin. It also checks all five original and three Hom-recovery
axiom reports against the three standard axioms above. To repeat these live checks locally:

```sh
python3 scripts/verify_live.py --cache
python3 scripts/verify_live.py
```

The cache step fetches only the transitive Mathlib imports needed by the authored sources
and lint probes, to limit hosted runner disk use. The live lint checks reconstruct the same
source wrappers as the archived probes, require clean JSON diagnostics and all 16 linters,
and re-elaborate each complete source under its original module identity. CI uses at most two
Lean threads per process. Live logs are retained as the `lean-verification-evidence` Actions
artifact for 14 days, separately from the historical receipts under `evidence/`; those receipts
remain records of their original verification runs.

Finite derivative loss, arbitrary-set local input regularity, and a current-master port remain
separate work. This package does not claim those theorems or an accepted upstream contribution.

All eight new proof, entry, and audit files also passed full-source
`#lint+ docBlame docBlameThm`, with all 16 selected environment linters and zero errors per file.
The mechanical syntax/style checks using the recorded `verify-mathlib-bar.sh` passed separately.
These checks do not assert that Mathlib's entire optional standard syntax-linter set was enabled.
Exact probes, per-file logs, hashes, and guarded receipts are in
[`evidence/lint-validation.json`](evidence/lint-validation.json). The original 19-file source
cone has a separate historical strict-build and hash certificate; it is outside this eight-file
lint scope. The later comment-only inventory update is described above.
