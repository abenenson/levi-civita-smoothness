# Exact comparison and contribution boundary

## Pinned sources

* Current Mathlib package base: `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).
* Historical package base: `d13f23b723b8a846827a245b89c10fc7d3f11612` (v4.34.1).
* Mathlib master observation: `e293c42021c641734f10655c39b8023fa88ff6ee` (2026-11-06).

The pinned v4.35.0 `LeviCivita.lean` supplies existence, uniqueness, and the Koszul
formula; its header still leaves connection regularity to future work. Its `Hom.lean`
supplies `contMDiffAt_hom_bundle` and forward `clm_bundle_apply`, while the reverse
`clm_bundle_of_apply` criterion is absent. Upstream PR #43042 remained open when
checked on 2026-11-14. The older master observation and archived source snapshots
remain historical evidence; the package does not claim a current-master port.

## Types and premises

| Aspect | local construction | Mathlib v4.35.0 |
| --- | --- | --- |
| Connection type | `SmoothTangentConnection` | `CovariantDerivative I E (TangentSpace I)` |
| Underlying operation | `Γ∞ → Γ∞ → Γ∞` | `(Π x, TM x) → Π x, TM x →L[ℝ] TM x` |
| Argument order | `conn.covDeriv X Y x` | `cov Y x (X x)` |
| Section regularity | Global smoothness stored in inputs and output | Arbitrary total sections; identities assume differentiability at the evaluation point |
| Direction dependence | Smooth-function linearity; pointwise tensoriality proved separately | Continuous linearity in a tangent vector built into the type |
| Metric | Explicit `g : Bundle.ContMDiffRiemannianMetric I ∞ E TM` | Scoped `RiemannianBundle TM` and `IsContMDiffRiemannianBundle I 1 E TM` |
| Existence premises | `IsManifold I 1 M`, `IsManifold I ∞ M`, `IsManifold I (minSmoothness ℝ 2) M`, `CompleteSpace E`, `FiniteDimensional ℝ E`, `T2Space M` | `IsManifold I 2 M`, `FiniteDimensional ℝ E`, metric class of regularity 1 |
| Output | Global smooth section for every pair of global smooth inputs | Chosen covariant derivative; no regularity instance in inspected file |
| Uniqueness | Equality of smooth output sections | Equality at `x` on sections differentiable at `x`; arbitrary tangent direction |

`∞` denotes smoothness, whereas `ω = ⊤` denotes analyticity in the `ℕ∞ω` index. The local
notation `n∞` is `(∞ : WithTop ℕ∞)`, not the top element.

The construction's strongest existence statement in the cone is
`SmoothTangentSection.exists_leviCivitaTangentConnectionFromMetric`. Its output is a
`SmoothTangentConnection` satisfying `IsTorsionFree` and
`IsMetricCompatibleFromMetric`. Smoothness comes from the codomain `Γ∞` of `covDeriv`, not
from an instance of Mathlib's connection regularity class.

Mathlib's `CovariantDerivative.ContMDiffCovariantDerivative cov n` requires that **every**
section that is `C^(n+1)` on `univ` maps to a `C^n` section of the Hom bundle. Its local form,
`ContMDiffCovariantDerivativeOn`, quantifies over sections that are regular **on the given
set**. The conclusion concerns the full Hom-valued section `x ↦ cov Y x`, not just evaluation
against a fixed global smooth vector field.

## Formula agreement

The local construction writes twice the inner product as

```
X⟪Y,Z⟫ + Y⟪Z,X⟫ - Z⟪X,Y⟫
  + ⟪[X,Y],Z⟫ - ⟪[X,Z],Y⟫ - ⟪[Y,Z],X⟫.
```

Mathlib writes the inner product as half of

```
X⟪Y,Z⟫ + Y⟪Z,X⟫ - Z⟪X,Y⟫
  - ⟪Y,[X,Z]⟫ - ⟪Z,[Y,X]⟫ + ⟪X,[Z,Y]⟫.
```

These agree using symmetry of the metric and antisymmetry of the Lie bracket. The derivative
terms agree via `TangentSection.toDerivation_apply`, whose right-hand side is
`mfderiv I 𝓘(ℝ, ℝ) f x (X x)`. The same explicit metric must define the fiberwise inner
products used by Mathlib; a second unrelated `RiemannianBundle` instance would invalidate the
comparison.

The compile-checked smooth bridge equation is

```
CovariantDerivative.leviCivitaConnection I M (fun x => Y x) x (X x)
  = SmoothTangentSection.covDerivFromMetric g X Y x
```

for bundled global smooth `X,Y`, with Mathlib's Riemannian bundle instantiated from `g`.
It is proved in `LeviCivitaSmoothness/MathlibBridge.lean`; the canonical metric application is
checked in `LeviCivitaSmoothness/MetricApplication.lean`. Both use the pinned v4.35.0 package.
Pairing against global smooth test sections determines a tangent vector: the local construction's
`SmoothTangentSection.exists_eq_at` supplies a test section with any prescribed value, without
requiring `SigmaCompactSpace M`. This avoids assuming that global differentiable and smooth
sections are the same test class.

## Proof architecture

1. Package the Koszul expression as a smooth scalar function and prove smooth-function
   linearity in the test section.
2. Represent its pointwise value as a linear functional on a tangent fiber and use a metric
   linear equivalence to obtain the pointwise candidate vector.
3. Construct a finite smooth frame near each point. Invert its Gram matrix using a nonzero
   determinant and smoothly solve the Koszul system locally.
4. Identify the pointwise candidate with the smooth local solution by pairing against that
   frame, then use locality of `ContMDiff` to get global smoothness.
5. Package the output as a smooth-section connection and verify torsion and compatibility.

The local representation theorem has quantifiers `∃ W, ∀ Z, ∀ᶠ x in 𝓝 x₀, ...`. It does
not itself provide one neighborhood valid for all test sections simultaneously. The global
smoothness proof only needs finitely many frame sections and takes the finite intersection
of their neighborhoods; an upstream port must preserve that distinction.

This is a different smoothness route from upstream's pointwise tensoriality/musical-isomorphism
construction. The checked bridge identifies the two outputs and transfers the local construction's smoothness
of evaluation on global smooth pairs. The subsequent checked `HomRecovery.lean` module recovers
the full Hom-valued regularity class at index `∞`, under the same smooth-metric hypotheses.

## Remaining work for an upstream regularity theorem

* The global `∞` case of Hom-bundle recovery is now proved in this package using the existing
  finite-dimensional operator criterion and global smooth extensions of chart-constant test
  sections. Open PR [#43042](https://github.com/leanprover-community/mathlib4/pull/43042)
  develops the more general `ContMDiff.clm_bundle_of_apply` criterion; coordinate further
  generalizations with that work.
* Localize the inputs. The local solver consumes globally smooth sections. A pointwise smoothness
  argument must extend sections agreeing on a neighborhood, rather than assert that every
  locally smooth section is globally smooth. Existing bump-function tools can support this,
  but the corresponding connection-germ bridge must be stated and checked. This is needed
  for the stronger arbitrary-set/local-input theorem. The proved global `C^∞` regularity class
  uses global smooth test sections obtained from local chart constants.
* Track finite derivative loss. The advertised upstream goal is a `C^(n+2)` manifold and
  `C^(n+1)` metric yielding a `C^n` connection. Replacing every `∞` in the construction by `n` is invalid:
  differentiating metric pairings and taking Lie brackets each costs derivatives, and the
  tangent bundle itself costs one derivative of the manifold atlas.
* Prove the correct local-set formulation. Smoothness at a point with index `∞` does not in
  general imply one neighborhood on which the function is smooth. PR #43042 explicitly uses
  `∀ᶠ b in 𝓝 x, ContMDiffAt ... b` for this reason.
* Port and check on the current toolchain in an isolated Mathlib checkout before offering any
  candidate as a current-master patch. The supported toolchain is Lean 4.35.0 with the stable Mathlib pin above.

## Existing upstream activity

Observed 2026-11-06 through the GitHub connector:

* [#45737](https://github.com/leanprover-community/mathlib4/pull/45737), open, updated that day:
  arithmetic for derivative counts; its description explicitly identifies the Levi-Civita
  smoothness project.
* [#43042](https://github.com/leanprover-community/mathlib4/pull/43042), open:
  regularity of a Hom-bundle section from regularity of applications. It promises future
  versions with derivative loss.
* [#44711](https://github.com/leanprover-community/mathlib4/pull/44711), closed with title
  `[Merged by Bors]`: regularity of `mvfderiv`, with the body explicitly mentioning an
  alternative proof of Levi-Civita smoothness. GitHub's `merged` field is false on this
  Bors-managed PR, so the title and pinned master source are the evidence for landing rather
  than that field.
* [#26221](https://github.com/leanprover-community/mathlib4/pull/26221), open umbrella branch:
  covariant derivative and Levi-Civita development.

No dedicated open smoothness theorem was found by the bounded searches used here. This does
not establish that no unpublished branch exists. The active project's authors should be
coordinated with before any eventual public contribution; no contact has been made here.
