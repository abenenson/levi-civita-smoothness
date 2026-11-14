/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Smooth Riemannian structure on the tangent bundle (typeclass wrapper)

Mathlib provides:

- `Bundle.ContMDiffRiemannianMetric` (data) and
- `Bundle.RiemannianBundle` / `IsContMDiffRiemannianBundle` (typeclasses)

but the smooth metric data is not itself a typeclass. In this project we often want to assume
“`TM` carries a smooth Riemannian metric” and have the corresponding bundle instances derived
coherently (avoiding definitional-equality diamonds).

This file introduces a small wrapper typeclass around the data
`Bundle.ContMDiffRiemannianMetric I ∞ E (fun x ↦ TangentSpace I x)` and provides the standard
instances derived from it.
-/

open scoped Bundle Manifold ContDiff

namespace MathlibExtensions.Geometry.Manifold.VectorBundle

local notation "n∞" => (∞ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I n∞ M]

/-- Typeclass wrapper for a smooth Riemannian metric on the tangent bundle. -/
class SmoothRiemannianTangentBundle (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I n∞ M] : Type _ where
  /-- The smooth Riemannian metric data on `TM`. -/
  g : Bundle.ContMDiffRiemannianMetric I n∞ E (fun x : M => TangentSpace I x)

namespace SmoothRiemannianTangentBundle

variable [h : SmoothRiemannianTangentBundle (I := I) (M := M)]

local notation "TM" => (fun x : M => TangentSpace I x)

-- These instances are intentionally local to the `Bundle` scope, per mathlib conventions.
/-- The supplied smooth metric determines the tangent-fiber Riemannian metric. -/
instance : Bundle.RiemannianBundle TM :=
  ⟨h.g.toRiemannianMetric⟩

/-- The supplied smooth metric yields continuity for the same tangent-fiber inner products. -/
instance :
    letI : Bundle.RiemannianBundle TM := ⟨h.g.toRiemannianMetric⟩
    letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
     Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
       (B := M) (E := TM) x
    letI : (x : M) → InnerProductSpace ℝ (TangentSpace I x) :=
      fun _ => by
        infer_instance
    IsContinuousRiemannianBundle E TM := by
  classical
  -- Use the `ContMDiff` metric data to build a continuous Riemannian metric and reuse the
  -- `ContinuousRiemannianMetric` → `IsContinuousRiemannianBundle` instance.
  let : Bundle.RiemannianBundle TM := ⟨h.g.toRiemannianMetric⟩
  let : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (B := M) (E := TM) x
  let : (x : M) → InnerProductSpace ℝ (TangentSpace I x) :=
    fun _ => by
      infer_instance
  let gcont : Bundle.ContinuousRiemannianMetric E TM := h.g.toContinuousRiemannianMetric
  let : Bundle.RiemannianBundle TM := ⟨gcont.toRiemannianMetric⟩
  exact ⟨⟨gcont.inner, gcont.continuous, fun _ _ _ => rfl⟩⟩

/-- The supplied smooth metric yields smoothness for the same tangent-fiber inner products. -/
instance :
    letI : Bundle.RiemannianBundle TM := ⟨h.g.toRiemannianMetric⟩
    letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
     Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
       (B := M) (E := TM) x
    letI : (x : M) → InnerProductSpace ℝ (TangentSpace I x) :=
      fun x => by
        infer_instance
    IsContMDiffRiemannianBundle I n∞ E TM :=
  -- This matches the instance in `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`.
  letI : Bundle.RiemannianBundle TM := ⟨h.g.toRiemannianMetric⟩
  letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (B := M) (E := TM) x
  letI : (x : M) → InnerProductSpace ℝ (TangentSpace I x) :=
    fun _ => by
      infer_instance
  ⟨h.g.inner, h.g.contMDiff, fun _ _ _ => rfl⟩

end SmoothRiemannianTangentBundle

end

end MathlibExtensions.Geometry.Manifold.VectorBundle

namespace Bundle

/-- Compatibility spelling for the norm factory whose generated name changed in Mathlib 4.34.
This abbreviation uses the existing Riemannian metric and the same fiber topology. It adds no
instance: the current scoped factory remains the sole typeclass registration. -/
noncomputable abbrev instNormedAddCommGroupOfRiemannianBundle
    {B : Type*} {E : B → Type*}
    [(b : B) → TopologicalSpace (E b)]
    [(b : B) → AddCommGroup (E b)] [(b : B) → Module ℝ (E b)]
    [h : RiemannianBundle E] [∀ (b : B), IsTopologicalAddGroup (E b)]
    [∀ (b : B), ContinuousConstSMul ℝ (E b)] (b : B) :
    NormedAddCommGroup (E b) :=
  instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (B := B) (E := E) b

end Bundle
