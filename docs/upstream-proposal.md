# Concrete upstream preparation

## First deliverable: smooth global inputs

The candidate bridge has two layers:

1. `LeviCivitaSmoothness/KoszulTransfer.lean` proves that the smooth Koszul identities determine
   the output pointwise, and transfers the existing smooth-output proof to any representative
   satisfying those identities.
2. `LeviCivitaSmoothness/MathlibBridge.lean` compares Mathlib's existing Koszul formula with the
   local formula, then transfers smoothness to
   `x ↦ leviCivitaConnection I M Y x (X x)` for globally smooth `X,Y`.

The bridge uses an explicit equality between the supplied metric's bilinear forms and the
inner products of the scoped `RiemannianBundle` instance. This prevents a hidden mismatch of
metrics. `MetricApplication.lean` installs the bundle from the supplied metric and discharges
that premise by reflexivity; this application has passed the strict build and axiom audit.

The supported package uses Lean and Mathlib v4.35.0, with exact dependency pins
recorded in the package configuration. It is not a current-master patch or the
finite-regularity smoothness theorem. The earlier Lean 4.34.1 strict-build and
three-standard-axiom receipts remain historical checkpoints; current verification
uses the public live verifier described in the README.

## Proved next step: global smooth connection class

For the global `ContMDiffCovariantDerivative ... ∞` instance, input sections are globally
smooth: `ContMDiffOn ... (∞ + 1) ... univ` reduces to ordinary global smoothness. Thus there
is no additional arbitrary-set input localization obligation at this stage. The Hom-bundle
regularity of `x ↦ leviCivitaConnection I M Y x` is now proved in `HomRecovery.lean`.

This package supplies global smooth extensions of chart-constant test sections near any point. The new
proof combines these with `contMDiffAt_hom_bundle`, a source chart, and the existing
finite-dimensional criterion `contDiffWithinAt_clm_apply`. It proves Mathlib's full global
`ContMDiffCovariantDerivative ... ∞` class, with explicit metric agreement and canonical
metric-installation versions. No common neighborhood for every test vector is assumed.
The more general Hom-bundle API in open upstream PR #43042 remains overlapping work to
coordinate with before an eventual public proposal. This local preparation does not replace
that general theorem or its planned finite-regularity extensions.

## Eventual finite-regularity theorem

The upstream file advertises:

```
C^(n+2) manifold + C^(n+1) metric -> C^n Levi-Civita connection
```

An appropriate final result is an instance or theorem of the form
`CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaConnection I M) n`, using the
current finite-regularity metric and manifold classes. The exact Lean index inequalities and
auxiliary bundle regularity premises must be checked on the target Mathlib revision; the
displayed arrow above records the upstream mathematical goal, not a fabricated Lean theorem.

The finite-matrix argument is reusable as proof strategy, but all input regularities and
derivative losses must be re-established. A finite-regularity port must account for:

* the derivative of metric pairings;
* regularity and derivative loss of the Lie bracket;
* the atlas regularity needed for the tangent and Hom bundles;
* smooth inversion of the local Gram matrix on its nonzero-determinant neighborhood;
* section regularity on sets when proving the local `...On` statement;
* connection locality when replacing local sections by suitable extensions.

The 19 maintained support files preserve a reusable public API. The full construction is too large and
project-specific to propose wholesale as an upstream PR. Replace its auxiliary local-frame,
tensoriality, derivation, and metric APIs with upstream APIs before proposing a small patch.

## Public contribution gate

No upstream issue, PR, or maintainer message has been created from this package. A reviewable upstream patch
would need a separately pinned current-master checkout, clean kernel checks, an explicit
review of overlap with the active Riemannian geometry project, and a description limited to
the theorem actually proved. The present package supplies the source evidence and the
mathematical/API comparison for that work.
