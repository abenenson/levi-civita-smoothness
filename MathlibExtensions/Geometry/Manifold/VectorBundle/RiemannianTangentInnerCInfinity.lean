/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

public import MathlibExtensions.Geometry.Manifold.VectorBundle.Connection
public import MathlibExtensions.Geometry.Manifold.VectorBundle.RiemannianTangentBundle

@[expose] public section

/-!
# Smooth inner product on tangent-bundle sections (from metric data)

For the tangent bundle, `TangentSpace I x` is definitionally the model space `E`. For a smoothly
varying Riemannian metric on `TM`, one typically wants to use the fiberwise bilinear forms
`g.inner x : E →L[ℝ] E →L[ℝ] ℝ` without introducing fiberwise `InnerProductSpace` instances as
typeclasses (which can lead to definitional-equality diamonds).

This module defines the pointwise inner product of two smooth tangent-bundle sections as a smooth
real-valued function, directly from the metric data
`Bundle.ContMDiffRiemannianMetric I n∞ E (fun x ↦ TangentSpace I x)`.

Implementation note: smoothness is proved using `ContMDiff.clm_bundle_apply₂`, mirroring the core
argument in `Mathlib.Geometry.Manifold.VectorBundle.Riemannian` but avoiding reliance on
`IsContMDiffRiemannianBundle` typeclass parameters.
-/

open scoped Bundle Manifold ContDiff

namespace MathlibExtensions.Geometry.Manifold.VectorBundle

open Bundle

local notation "n∞" => (∞ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

/-- The pointwise inner product of two smooth tangent-bundle sections, as a smooth real-valued
function, constructed directly from a smooth Riemannian metric `g` on `TM`. -/
noncomputable def smoothTangentSectionInnerFromMetric
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t : Γ∞) : C∞ := by
  refine ⟨fun x => (g.inner x (s x)) (t x), ?_⟩
  -- Prove smoothness of the scalar function by first working in the total space of the trivial
  -- ℝ-bundle over `M`, then extracting the fiber coordinate.
  have h_total :
      ContMDiff I (I.prod 𝓘(ℝ, ℝ)) n∞
        (fun x : M =>
          Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x ((g.inner x (s x)) (t x))) := by
    -- The evaluation map `(ψ, v, w) ↦ ψ(v)(w)` is smooth in bundle coordinates.
    simpa using
      (ContMDiff.clm_bundle_apply₂ (𝕜 := ℝ)
        (B := M) (M := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (E₁ := TM) (E₂ := TM) (E₃ := Bundle.Trivial M ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => g.inner x)
        (v := fun x : M => s x)
        (w := fun x : M => t x)
        g.contMDiff s.contMDiff t.contMDiff)
  -- `ContMDiff` is pointwise, so reduce to `ContMDiffAt` and use the total-space characterization.
  intro x
  have hx := h_total x
  have hx' :=
    (Bundle.contMDiffAt_totalSpace (n := n∞) (IB := I) (IM := I)
      (F := ℝ) (E := Bundle.Trivial M ℝ)
      (f := fun x : M =>
        Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x ((g.inner x (s x)) (t x)))
      (x₀ := x)).1 hx
  simpa using hx'.2

/-- Evaluating the smooth section inner product gives the metric's fiberwise bilinear form. -/
@[simp]
theorem smoothTangentSectionInnerFromMetric_apply
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t : Γ∞) (x : M) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t x = (g.inner x (s x)) (t x) :=
  rfl

/-- Interchanging the two sections leaves their smooth inner product unchanged. -/
theorem smoothTangentSectionInnerFromMetric_symm
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t =
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g t s := by
  ext x
  change (g.inner x (s x)) (t x) = (g.inner x (t x)) (s x)
  exact g.symm x (s x) (t x)

/-- The smooth section inner product distributes over addition in its first section. -/
@[simp]
theorem smoothTangentSectionInnerFromMetric_add_left
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s₁ s₂ t : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g (s₁ + s₂) t =
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g s₁ t +
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g s₂ t := by
  ext x
  change (g.inner x (s₁ x + s₂ x)) (t x) =
    (g.inner x (s₁ x)) (t x) + (g.inner x (s₂ x)) (t x)
  exact congrArg (fun form : TangentSpace I x →L[ℝ] ℝ ↦ form (t x))
    (map_add (g.inner x) (s₁ x) (s₂ x))

/-- The smooth section inner product distributes over addition in its second section. -/
@[simp]
theorem smoothTangentSectionInnerFromMetric_add_right
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t₁ t₂ : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g s (t₁ + t₂) =
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t₁ +
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t₂ := by
  ext x
  change (g.inner x (s x)) (t₁ x + t₂ x) =
    (g.inner x (s x)) (t₁ x) + (g.inner x (s x)) (t₂ x)
  exact map_add (g.inner x (s x)) (t₁ x) (t₂ x)

/-- A smooth scalar multiplying the first section factors out of its smooth inner product. -/
@[simp]
theorem smoothTangentSectionInnerFromMetric_smul_left
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (f : C∞) (s t : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g (f • s) t =
      f • smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t := by
  ext x
  -- Scalar action on `C∞` is pointwise multiplication.
  change (g.inner x (f x • s x)) (t x) = f x • ((g.inner x (s x)) (t x))
  exact congrArg (fun form : TangentSpace I x →L[ℝ] ℝ ↦ form (t x))
    (map_smul (g.inner x) (f x) (s x))

/-- A smooth scalar multiplying the second section factors out of its smooth inner product. -/
@[simp]
theorem smoothTangentSectionInnerFromMetric_smul_right
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (f : C∞) (s t : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g s (f • t) =
      f • smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t := by
  ext x
  change (g.inner x (s x)) (f x • t x) = f x • ((g.inner x (s x)) (t x))
  exact map_smul (g.inner x (s x)) (f x) (t x)

namespace SmoothRiemannianTangentBundle

variable [IsManifold I n∞ M] [h : SmoothRiemannianTangentBundle (I := I) (M := M)]

/-- The pointwise inner product of two smooth tangent-bundle sections, as a smooth real-valued
function, constructed from the `SmoothRiemannianTangentBundle` data. -/
noncomputable def smoothTangentSectionInner (s t : Γ∞) : C∞ :=
  smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := h.g) s t

end SmoothRiemannianTangentBundle

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
