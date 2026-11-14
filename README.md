# Levi-Civita smoothness

[![Lean verification](https://github.com/abenenson/levi-civita-smoothness/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/abenenson/levi-civita-smoothness/actions/workflows/lean.yml)

This package proves global `C^∞` smoothness of Mathlib's chosen
`CovariantDerivative.leviCivitaConnection` from a supplied smooth Riemannian metric.
It uses Lean **4.35.0** and Mathlib
[`56a005855ea17e0b0958f73ec801ae140b0a1679`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
(the `v4.35.0` release).

```lean
import LeviCivitaSmoothness

#check LeviCivitaSmoothness.contMDiffCovariantDerivative_leviCivitaConnection_fromMetric
```

The conclusion is Mathlib's full Hom-valued connection regularity class:

```lean
CovariantDerivative.ContMDiffCovariantDerivative
  (CovariantDerivative.leviCivitaConnection I M) ∞
```

For every globally smooth tangent section `Y`, this class gives smoothness of the
Hom-valued section `x ↦ leviCivitaConnection I M Y x`, before choosing a direction
field. The theorem preserves the finite-dimensional real model, Hausdorff manifold,
complete model space, and smooth-manifold hypotheses of the construction. Its
`_fromMetric` form installs precisely the supplied genuine smooth metric; the
explicit-instance form requires agreement between that metric and the Riemannian
bundle's inner products.

[`Examples/MetricConsumer.lean`](LeviCivitaSmoothness/Examples/MetricConsumer.lean)
shows how to use the smooth-pair theorem, extract Hom-valued smoothness for an
unbundled globally smooth input, and obtain a global smooth section with a prescribed
tangent value. Examples are opt-in and are excluded from the library roots.

Mathlib already supplies Levi-Civita existence and uniqueness. The package identifies
a direct smooth Koszul construction with Mathlib's chosen derivative on globally
smooth sections, then recovers the full Hom-valued result. All 19 maintained support
files are retained: 17 lie in the Hom-recovery import cone, and the separate
`MathlibExtensions` root also preserves the existence and uniqueness API. Live
verification covers all support files, the bridge, entry points, audits, and example.

The result concerns global smooth inputs and the regularity class on `univ`.
Arbitrary-set local-input regularity, finite derivative loss, and compilation on
Mathlib master remain separate work. Values on nonsmooth input sections are outside
the theorem's scope. This package does not claim an accepted or submitted upstream
contribution. General Hom-bundle recovery is also being developed in upstream
[PR #43042](https://github.com/leanprover-community/mathlib4/pull/43042).
See [the interface comparison](docs/api-comparison.md) and
[the Hom recovery proof guide](docs/hom-recovery.md).

## Verification

The public workflow uses standard `ubuntu-latest` runners. It checks the pinned
sources and dependency metadata, strict builds of every authored module, full-source
probes with all 16 selected environment linters, and public-declaration axiom reports
against `propext`, `Classical.choice`, and `Quot.sound`. The live module inventory
includes the opt-in example; the library roots do not import it.

```sh
python3 scripts/verify_evidence.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify_live.py --cache
python3 scripts/verify_live.py
```

The focused cache command fetches the Mathlib import closure needed by these checks.
Live logs are retained as the `lean-verification-evidence` Actions artifact for
14 days. These logs qualify the exact workflow revision.

The earlier Lean 4.34.1 build, Hom recovery, and eight-file lint receipts under
[`evidence/`](evidence/) retain their original source hashes and verification scope.
They document historical checkpoints; fresh 4.35.0 verification is supplied by the
live checks. Upstream source snapshots under `evidence/upstream` are historical
evidence outside the Lean library roots, with their attribution headers preserved.
