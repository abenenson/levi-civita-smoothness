# Bounded global smoothness step

The branch `hom-bundle-recovery` starts at the validated commit `d9da9f6`. It leaves the
existing proof sources and their validation hashes unchanged.

The new target is Mathlib's existing class, not a new connection interface:

```lean
CovariantDerivative.ContMDiffCovariantDerivative
  (CovariantDerivative.leviCivitaConnection I M) ∞
```

The metric-agreement version retains the smooth-pair theorem's assumptions: finite-dimensional
real model space, complete model space, Hausdorff manifold, the explicit manifold regularity
instances already used by the the library construction, a smooth metric `g`, a Riemannian bundle with
its `C¹` metric class, and `inner ℝ u v = g.inner x u v`. The canonical version installs the
Riemannian structure from `g` and discharges metric agreement by reflexivity.

The proof is bounded by APIs already present in pinned Mathlib v4.34.1:

1. `contMDiffAt_hom_bundle` reduces a Hom-valued section to its coordinate operator.
2. `contMDiffAt_iff_source` moves operator regularity into a source chart.
3. `contDiffWithinAt_clm_apply` recovers regularity of a finite-dimensional family of linear
   operators from regularity of every fixed-vector evaluation.
4. the library's `SmoothTangentSection.exists_eq_localConst_nhds` extends each chart-constant vector
   to a global smooth section agreeing with it near the point. The checked smooth-pair theorem
   gives smooth evaluation on that section. `Bundle.contMDiffAt_section` then yields the
   needed smooth coordinate evaluation.
5. In the global regularity class the input assumption is `C^(∞+1)` on `univ`, which reduces
   to global `C^∞`. Bundle that input as a smooth tangent section and apply the recovered Hom
   regularity.

Each fixed vector may have a different neighborhood of agreement. The operator criterion
requires regularity of each evaluation at the point; no quantifier exchange to a single
neighborhood for every vector is used. The existing finite-dimensional criterion internally
reduces to finitely many coordinate tests.

`LeviCivitaSmoothness/HomRecovery.lean` contains the proof and
`LeviCivitaSmoothness/HomAxiomAudit.lean` contains its transitive axiom probes. Both passed the
strict `lake --rehash --wfail build` gate in the qualified serial compiler lane. All three new
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
`evidence/hom-validation.json` records the successful build receipt and exact source hashes.
The only new Mathlib cache target was `Mathlib.Analysis.Calculus.ContDiff.FiniteDimension`.

Finite regularity, section inputs regular only on arbitrary subsets, and compilation on current
Mathlib master remain outside this step. Existing upstream PR #43042 develops a more general
Hom-bundle criterion, so this specialized global-smooth route must still be coordinated with
that project before any public proposal.
