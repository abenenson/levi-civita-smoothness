/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public import MathlibExtensions.Geometry.Manifold.VectorBundle.RiemannianTangentInnerCInfinity
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentLieBracket
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionLieBracket
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionCInfinityLinearAtPoint
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionDerivation
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSpaceFiniteDimensional

@[expose] public section

/-!
# Levi–Civita existence (workbench)

This module collects preparatory lemmas for the Koszul-based construction of the Levi–Civita
connection on the tangent bundle.

## Main Results

- `SmoothTangentSection.koszulRHS`: the Koszul right-hand side, as a smooth real-valued function.
- `SmoothTangentSection.koszulRHS_smul_right`: `C^∞`-linearity of the Koszul RHS in the third slot.
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
  [IsManifold I 1 M] [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

section KoszulRHS

/-- The (scalar) right-hand side of the Koszul formula, packaged as a smooth function. -/
noncomputable def koszulRHS
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z : Γ∞) : C∞ :=
  (TangentSection.toDerivation (I := I) (M := M) X)
        (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) +
      (TangentSection.toDerivation (I := I) (M := M) Y)
        (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X) -
    (TangentSection.toDerivation (I := I) (M := M) Z)
        (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) +
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
        (SmoothTangentSection.mlieBracket (I := I) X Y) Z -
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) X Z) Y -
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) Y Z) X

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
private theorem inner_smul_right
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t : Γ∞) (f : C∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g s (f • t) =
      f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t := by
  ext x
  -- linearity in the second argument of `g.inner x s` (as a `ContinuousLinearMap`)
  simp [smoothTangentSectionInnerFromMetric_apply, smul_eq_mul]

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
private theorem inner_smul_left
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t : Γ∞) (f : C∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g (f • s) t =
      f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t := by
  ext x
  -- linearity in the first argument of `g.inner x` (as a `LinearMap` into linear maps)
  simp [smoothTangentSectionInnerFromMetric_apply, smul_eq_mul]

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
private theorem inner_add_right
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s t₁ t₂ : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g s (t₁ + t₂) =
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t₁ +
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t₂ := by
  ext x
  simp [smoothTangentSectionInnerFromMetric_apply]

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
private theorem inner_add_left
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (s₁ s₂ t : Γ∞) :
    smoothTangentSectionInnerFromMetric (I := I) (M := M) g (s₁ + s₂) t =
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g s₁ t +
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g s₂ t := by
  ext x
  simp [smoothTangentSectionInnerFromMetric_apply]

/-- `C^∞`-linearity of the Koszul RHS in the third slot. -/
theorem koszulRHS_smul_right
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z : Γ∞) (f : C∞) :
    koszulRHS (I := I) (M := M) (E := E) g X Y (f • Z) =
      f * koszulRHS (I := I) (M := M) (E := E) g X Y Z := by
  -- Work pointwise, but use algebraic Leibniz for the derivations.
  ext x
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M)
      (hmn := (le_minSmoothness (𝕜 := ℝ) (n := (2 : WithTop ℕ∞))))
  have hYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y (f • Z) =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z :=
    inner_smul_right (I := I) (M := M) (E := E) (g := g) Y Z f
  have hZX :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g (f • Z) X =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X :=
    inner_smul_left (I := I) (M := M) (E := E) (g := g) Z X f
  have hXY :
      (TangentSection.toDerivation (I := I) (M := M) (f • Z))
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) x =
        (f x) *
        (TangentSection.toDerivation (I := I) (M := M) Z)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) x := by
    -- `toDerivation` scales as a `C^∞`-module morphism.
    simp [TangentSection.toDerivation_smul (I := I) (M := M), smul_eq_mul]
  have hbrX :=
    SmoothTangentSection.mlieBracket_smul_right (I := I) (X := X) (Y := Z) (f := f) (x := x)
  have hbrY :=
    SmoothTangentSection.mlieBracket_smul_right (I := I) (X := Y) (Y := Z) (f := f) (x := x)
  have hinner_brX :
      ((g.inner x) (VectorField.mlieBracket I (fun z => X z) (fun z => f z • Z z) x)) (Y x) =
        (TangentSection.toDerivation (I := I) (M := M) X f) x * ((g.inner x) (Z x)) (Y x) +
          f x * ((g.inner x) (VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) := by
    -- rewrite the bracket using the Leibniz rule, then use linearity of `g.inner x`
    -- in the first argument
    -- (viewed as a `ContinuousLinearMap` into `TangentSpace I x →L[ℝ] ℝ`).
    have hdfX :
        (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x) =
          (TangentSection.toDerivation (I := I) (M := M) X f) x := by
      simp [TangentSection.toDerivation_apply]
    have hbrX' :
        VectorField.mlieBracket I (fun z => X z) (fun z => f z • Z z) x =
          (TangentSection.toDerivation (I := I) (M := M) X f) x • Z x +
            f x • VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x := by
      simpa only [hdfX] using! hbrX
    rw [hbrX']
    -- split the first-argument sum
    have hadd :
        ((g.inner x)
              ((TangentSection.toDerivation (I := I) (M := M) X f) x • Z x +
                f x • VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) =
          ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) X f) x • Z x)) (Y x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) := by
      -- `g.inner x` is linear in its first argument.
      simp [map_add]
    -- scale the two summands
    have hsmul₁ :
        ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) X f) x • Z x)) (Y x) =
          (TangentSection.toDerivation (I := I) (M := M) X f) x * ((g.inner x) (Z x)) (Y x) := by
      simpa only [_root_.smul_apply, smul_eq_mul] using
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Y x))
          ((g.inner x).map_smul (((TangentSection.toDerivation (I := I) (M := M) X f) x)) (Z x))
    have hsmul₂ :
        ((g.inner x) (f x • VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) =
          f x * ((g.inner x) (VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) := by
      simp [smul_eq_mul]
    -- finish
    calc
      ((g.inner x)
            ((TangentSection.toDerivation (I := I) (M := M) X f) x • Z x +
              f x • VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x)
          =
          ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) X f) x • Z x)) (Y x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) := hadd
      _ =
          (TangentSection.toDerivation (I := I) (M := M) X f) x * ((g.inner x) (Z x)) (Y x) +
            f x * ((g.inner x) (VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x)) (Y x) := by
          rw [hsmul₁, hsmul₂]
  have hinner_brY :
      ((g.inner x) (VectorField.mlieBracket I (fun z => Y z) (fun z => f z • Z z) x)) (X x) =
        (TangentSection.toDerivation (I := I) (M := M) Y f) x * ((g.inner x) (Z x)) (X x) +
          f x * ((g.inner x) (VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) := by
    have hdfY :
        (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (Y x) =
          (TangentSection.toDerivation (I := I) (M := M) Y f) x := by
      simp [TangentSection.toDerivation_apply]
    have hbrY' :
        VectorField.mlieBracket I (fun z => Y z) (fun z => f z • Z z) x =
          (TangentSection.toDerivation (I := I) (M := M) Y f) x • Z x +
            f x • VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x := by
      simpa only [hdfY] using! hbrY
    rw [hbrY']
    have hadd :
        ((g.inner x)
              ((TangentSection.toDerivation (I := I) (M := M) Y f) x • Z x +
                f x • VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) =
          ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) Y f) x • Z x)) (X x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) := by
      simp [map_add]
    have hsmul₁ :
        ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) Y f) x • Z x)) (X x) =
          (TangentSection.toDerivation (I := I) (M := M) Y f) x * ((g.inner x) (Z x)) (X x) := by
      simpa only [_root_.smul_apply, smul_eq_mul] using
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x))
          ((g.inner x).map_smul (((TangentSection.toDerivation (I := I) (M := M) Y f) x)) (Z x))
    have hsmul₂ :
        ((g.inner x) (f x • VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) =
          f x * ((g.inner x) (VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) := by
      simp [smul_eq_mul]
    calc
      ((g.inner x)
            ((TangentSection.toDerivation (I := I) (M := M) Y f) x • Z x +
              f x • VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x)
          =
          ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) Y f) x • Z x)) (X x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) := hadd
      _ =
          (TangentSection.toDerivation (I := I) (M := M) Y f) x * ((g.inner x) (Z x)) (X x) +
            f x * ((g.inner x) (VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)) (X x) := by
          rw [hsmul₁, hsmul₂]
  have hsymmYZ : ((g.inner x) (Y x)) (Z x) = ((g.inner x) (Z x)) (Y x) := by
    simpa using (g.symm x (Y x) (Z x))
  -- Expand the derivation/product terms, rewrite the two bracket-inner terms via the Leibniz rules,
  -- then finish by commutative-ring algebra (the remaining cancellations use `g.symm` once).
  -- Expand via Leibniz, rewrite the two bracket-inner terms, then finish
  -- by commutative-ring algebra.
  -- Avoid rewriting `TangentSection.toDerivation_apply`
  -- (it introduces tangent-space scalars in `ℝ`).
  simp [-TangentSection.toDerivation_apply, koszulRHS, hYZ, hZX, hXY, Derivation.leibniz,
    sub_eq_add_neg, hinner_brX, hinner_brY, hsymmYZ, smoothTangentSectionInnerFromMetric_apply]
  ring_nf

/-- Additivity of the Koszul RHS in the third slot. -/
theorem koszulRHS_add_right
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z₁ Z₂ : Γ∞) :
    koszulRHS (I := I) (M := M) (E := E) g X Y (Z₁ + Z₂) =
      koszulRHS (I := I) (M := M) (E := E) g X Y Z₁ +
        koszulRHS (I := I) (M := M) (E := E) g X Y Z₂ := by
  ext x
  have hYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y (Z₁ + Z₂) =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z₁ +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z₂ :=
    inner_add_right (I := I) (M := M) (E := E) (g := g) Y Z₁ Z₂
  have hZX :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g (Z₁ + Z₂) X =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z₁ X +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z₂ X :=
    inner_add_left (I := I) (M := M) (E := E) (g := g) Z₁ Z₂ X
  have hDX :
      (TangentSection.toDerivation (I := I) (M := M) X)
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y (Z₁ + Z₂)) x =
        (TangentSection.toDerivation (I := I) (M := M) X)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z₁) x +
          (TangentSection.toDerivation (I := I) (M := M) X)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z₂) x := by
    -- rewrite by additivity of the inner product, then use linearity of the derivation
    simp [hYZ, map_add]
  have hDY :
      (TangentSection.toDerivation (I := I) (M := M) Y)
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g (Z₁ + Z₂) X) x =
        (TangentSection.toDerivation (I := I) (M := M) Y)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z₁ X) x +
          (TangentSection.toDerivation (I := I) (M := M) Y)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z₂ X) x := by
    simp [hZX, map_add]
  have hDZ :
      (TangentSection.toDerivation (I := I) (M := M) (Z₁ + Z₂))
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) x =
        (TangentSection.toDerivation (I := I) (M := M) Z₁)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) x +
          (TangentSection.toDerivation (I := I) (M := M) Z₂)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) x := by
    -- `toDerivation` is additive in the vector field argument.
    simp [TangentSection.toDerivation_add (I := I) (M := M)]
  have hZ₁ : MDifferentiableAt I I.tangent (fun z : M ↦ (Z₁ z : TangentBundle I M)) x := by
    simpa using (Z₁.contMDiff.mdifferentiableAt (x := x) (by simp))
  have hZ₂ : MDifferentiableAt I I.tangent (fun z : M ↦ (Z₂ z : TangentBundle I M)) x := by
    simpa using (Z₂.contMDiff.mdifferentiableAt (x := x) (by simp))
  have hbrXZ :
      VectorField.mlieBracket I (fun z : M => X z) (fun z : M => (Z₁ + Z₂) z) x =
        VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z₁ z) x +
          VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z₂ z) x := by
    simpa [Pi.add_apply] using!
      (VectorField.mlieBracket_add_right (I := I) (V := fun z : M => X z)
        (W := fun z : M => Z₁ z) (W₁ := fun z : M => Z₂ z) (x := x) hZ₁ hZ₂)
  have hbrYZ :
      VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => (Z₁ + Z₂) z) x =
        VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z₁ z) x +
          VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z₂ z) x := by
    simpa [Pi.add_apply] using!
      (VectorField.mlieBracket_add_right (I := I) (V := fun z : M => Y z)
        (W := fun z : M => Z₁ z) (W₁ := fun z : M => Z₂ z) (x := x) hZ₁ hZ₂)
  have hInnerXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) X Y) (Z₁ + Z₂) x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X Y) Z₁ x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X Y) Z₂ x := by
    -- linearity in the second argument
    simp
  have hInnerXZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) X (Z₁ + Z₂)) Y x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X Z₁) Y x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X Z₂) Y x := by
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
  have hInnerYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) Y (Z₁ + Z₂)) X x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) Y Z₁) X x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) Y Z₂) X x := by
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
  -- Expand `koszulRHS` on both sides and finish in the additive commutative group `ℝ`.
  simp only [koszulRHS, ContMDiffMap.coe_add, ContMDiffMap.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  rw [hDX, hDY, hDZ, hInnerXY, hInnerXZ, hInnerYZ]
  abel

/-- Additivity of the Koszul RHS in the second slot. -/
theorem koszulRHS_add_middle
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y₁ Y₂ Z : Γ∞) :
    koszulRHS (I := I) (M := M) (E := E) g X (Y₁ + Y₂) Z =
      koszulRHS (I := I) (M := M) (E := E) g X Y₁ Z +
        koszulRHS (I := I) (M := M) (E := E) g X Y₂ Z := by
  ext x
  have hYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g (Y₁ + Y₂) Z =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y₁ Z +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y₂ Z :=
    inner_add_left (I := I) (M := M) (E := E) (g := g) Y₁ Y₂ Z
  have hXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g X (Y₁ + Y₂) =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y₁ +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y₂ :=
    inner_add_right (I := I) (M := M) (E := E) (g := g) X Y₁ Y₂
  have hDX :
      (TangentSection.toDerivation (I := I) (M := M) X)
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g (Y₁ + Y₂) Z) x =
        (TangentSection.toDerivation (I := I) (M := M) X)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y₁ Z) x +
          (TangentSection.toDerivation (I := I) (M := M) X)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y₂ Z) x := by
    simp [hYZ, map_add]
  have hDY :
      (TangentSection.toDerivation (I := I) (M := M) (Y₁ + Y₂))
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X) x =
        (TangentSection.toDerivation (I := I) (M := M) Y₁)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X) x +
          (TangentSection.toDerivation (I := I) (M := M) Y₂)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X) x := by
    simp [TangentSection.toDerivation_add (I := I) (M := M)]
  have hDZ :
      (TangentSection.toDerivation (I := I) (M := M) Z)
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X (Y₁ + Y₂)) x =
        (TangentSection.toDerivation (I := I) (M := M) Z)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y₁) x +
          (TangentSection.toDerivation (I := I) (M := M) Z)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y₂) x := by
    simp [hXY, map_add]
  have hY₁ : MDifferentiableAt I I.tangent (fun z : M ↦ (Y₁ z : TangentBundle I M)) x := by
    simpa using (Y₁.contMDiff.mdifferentiableAt (x := x) (by simp))
  have hY₂ : MDifferentiableAt I I.tangent (fun z : M ↦ (Y₂ z : TangentBundle I M)) x := by
    simpa using (Y₂.contMDiff.mdifferentiableAt (x := x) (by simp))
  have hbrXY :
      VectorField.mlieBracket I (fun z : M => X z) (fun z : M => (Y₁ + Y₂) z) x =
        VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y₁ z) x +
          VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y₂ z) x := by
    simpa [Pi.add_apply] using!
      (VectorField.mlieBracket_add_right (I := I) (V := fun z : M => X z)
        (W := fun z : M => Y₁ z) (W₁ := fun z : M => Y₂ z) (x := x) hY₁ hY₂)
  have hbrYZ :
      VectorField.mlieBracket I (fun z : M => (Y₁ + Y₂) z) (fun z : M => Z z) x =
        VectorField.mlieBracket I (fun z : M => Y₁ z) (fun z : M => Z z) x +
          VectorField.mlieBracket I (fun z : M => Y₂ z) (fun z : M => Z z) x := by
    simpa [Pi.add_apply] using!
      (VectorField.mlieBracket_add_left (I := I) (V := fun z : M => Y₁ z)
        (V₁ := fun z : M => Y₂ z) (W := fun z : M => Z z) (x := x) hY₁ hY₂)
  have hInnerXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) X (Y₁ + Y₂)) Z x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X Y₁) Z x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X Y₂) Z x := by
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
  have hInnerXZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) X Z) (Y₁ + Y₂) x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X Z) Y₁ x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X Z) Y₂ x := by
    exact
      congrArg (fun f : C∞ => f x)
        (inner_add_right (I := I) (M := M) (E := E) (g := g)
          (SmoothTangentSection.mlieBracket (I := I) X Z) Y₁ Y₂)
  have hInnerYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) (Y₁ + Y₂) Z) X x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) Y₁ Z) X x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) Y₂ Z) X x := by
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
  simp only [koszulRHS, ContMDiffMap.coe_add, ContMDiffMap.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  rw [hDX, hDY, hDZ, hInnerXY, hInnerXZ, hInnerYZ]
  abel

/-- Additivity of the Koszul RHS in the first slot. -/
theorem koszulRHS_add_left
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X₁ X₂ Y Z : Γ∞) :
    koszulRHS (I := I) (M := M) (E := E) g (X₁ + X₂) Y Z =
      koszulRHS (I := I) (M := M) (E := E) g X₁ Y Z +
        koszulRHS (I := I) (M := M) (E := E) g X₂ Y Z := by
  ext x
  have hZX :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z (X₁ + X₂) =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X₁ +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X₂ :=
    inner_add_right (I := I) (M := M) (E := E) (g := g) Z X₁ X₂
  have hXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g (X₁ + X₂) Y =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g X₁ Y +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g X₂ Y :=
    inner_add_left (I := I) (M := M) (E := E) (g := g) X₁ X₂ Y
  have hDX :
      (TangentSection.toDerivation (I := I) (M := M) (X₁ + X₂))
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) x =
        (TangentSection.toDerivation (I := I) (M := M) X₁)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) x +
          (TangentSection.toDerivation (I := I) (M := M) X₂)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) x := by
    simp [TangentSection.toDerivation_add (I := I) (M := M)]
  have hDY :
      (TangentSection.toDerivation (I := I) (M := M) Y)
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z (X₁ + X₂)) x =
        (TangentSection.toDerivation (I := I) (M := M) Y)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X₁) x +
          (TangentSection.toDerivation (I := I) (M := M) Y)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X₂) x := by
    simp [hZX, map_add]
  have hDZ :
      (TangentSection.toDerivation (I := I) (M := M) Z)
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g (X₁ + X₂) Y) x =
        (TangentSection.toDerivation (I := I) (M := M) Z)
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X₁ Y) x +
          (TangentSection.toDerivation (I := I) (M := M) Z)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X₂ Y) x := by
    simp [hXY, map_add]
  have hX₁ : MDifferentiableAt I I.tangent (fun z : M ↦ (X₁ z : TangentBundle I M)) x := by
    simpa using (X₁.contMDiff.mdifferentiableAt (x := x) (by simp))
  have hX₂ : MDifferentiableAt I I.tangent (fun z : M ↦ (X₂ z : TangentBundle I M)) x := by
    simpa using (X₂.contMDiff.mdifferentiableAt (x := x) (by simp))
  have hbrXY :
      VectorField.mlieBracket I (fun z : M => (X₁ + X₂) z) (fun z : M => Y z) x =
        VectorField.mlieBracket I (fun z : M => X₁ z) (fun z : M => Y z) x +
          VectorField.mlieBracket I (fun z : M => X₂ z) (fun z : M => Y z) x := by
    simpa [Pi.add_apply] using!
      (VectorField.mlieBracket_add_left (I := I) (V := fun z : M => X₁ z)
        (V₁ := fun z : M => X₂ z) (W := fun z : M => Y z) (x := x) hX₁ hX₂)
  have hbrXZ :
      VectorField.mlieBracket I (fun z : M => (X₁ + X₂) z) (fun z : M => Z z) x =
        VectorField.mlieBracket I (fun z : M => X₁ z) (fun z : M => Z z) x +
          VectorField.mlieBracket I (fun z : M => X₂ z) (fun z : M => Z z) x := by
    simpa [Pi.add_apply] using!
      (VectorField.mlieBracket_add_left (I := I) (V := fun z : M => X₁ z)
        (V₁ := fun z : M => X₂ z) (W := fun z : M => Z z) (x := x) hX₁ hX₂)
  have hInnerXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) (X₁ + X₂) Y) Z x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X₁ Y) Z x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X₂ Y) Z x := by
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
  have hInnerXZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) (X₁ + X₂) Z) Y x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X₁ Z) Y x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X₂ Z) Y x := by
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
  have hInnerYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) Y Z) (X₁ + X₂) x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) Y Z) X₁ x +
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) Y Z) X₂ x := by
    exact
      congrArg (fun f : C∞ => f x)
        (inner_add_right (I := I) (M := M) (E := E) (g := g)
          (SmoothTangentSection.mlieBracket (I := I) Y Z) X₁ X₂)
  simp only [koszulRHS, ContMDiffMap.coe_add, ContMDiffMap.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  rw [hDX, hDY, hDZ, hInnerXY, hInnerXZ, hInnerYZ]
  abel

/-- Leibniz rule for the Koszul RHS in the second slot: `Y ↦ f • Y`. -/
theorem koszulRHS_smul_middle
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z : Γ∞) (f : C∞) :
    koszulRHS (I := I) (M := M) (E := E) g X (f • Y) Z =
      (2 : ℝ) •
          ((TangentSection.toDerivation (I := I) (M := M) X f) *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) +
        f * koszulRHS (I := I) (M := M) (E := E) g X Y Z := by
  ext x
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M)
      (hmn := (le_minSmoothness (𝕜 := ℝ) (n := (2 : WithTop ℕ∞))))
  have hYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g (f • Y) Z =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z :=
    inner_smul_left (I := I) (M := M) (E := E) (g := g) Y Z f
  have hXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g X (f • Y) =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y :=
    inner_smul_right (I := I) (M := M) (E := E) (g := g) X Y f
  have hDY :
      (TangentSection.toDerivation (I := I) (M := M) (f • Y))
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X) x =
        (f x) *
          (TangentSection.toDerivation (I := I) (M := M) Y)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X) x := by
    -- `toDerivation` scales as a `C^∞`-module morphism.
    simp [TangentSection.toDerivation_smul (I := I) (M := M), smul_eq_mul]
  have hdfX :
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x) =
        (TangentSection.toDerivation (I := I) (M := M) X f) x := by
    simp [TangentSection.toDerivation_apply]
  have hdfZ :
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (Z x) =
        (TangentSection.toDerivation (I := I) (M := M) Z f) x := by
    simp [TangentSection.toDerivation_apply]
  have hbrXY :=
    SmoothTangentSection.mlieBracket_smul_right (I := I) (X := X) (Y := Y) (f := f) (x := x)
  have hbrYZ :=
    SmoothTangentSection.mlieBracket_smul_left (I := I) (X := Y) (Y := Z) (f := f) (x := x)
  have hinner_brXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) X (f • Y)) Z x =
        (TangentSection.toDerivation (I := I) (M := M) X f) x *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z x +
          f x *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) g
                (SmoothTangentSection.mlieBracket (I := I) X Y) Z x := by
    -- Rewrite the bracket via Leibniz, then expand using linearity of `g.inner x`
    -- in the first slot.
    simp [smoothTangentSectionInnerFromMetric_apply, SmoothTangentSection.mlieBracket_apply]
    have hbrXY' :
        VectorField.mlieBracket I (fun z : M => X z) (fun z : M => f z • Y z) x =
          (TangentSection.toDerivation (I := I) (M := M) X f) x • Y x +
            f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x := by
      simpa only [hdfX] using! hbrXY
    rw [hbrXY']
    -- `g.inner x` is linear in the first slot.
    have hadd :=
      congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Z x))
        ((g.inner x).map_add
          ((TangentSection.toDerivation (I := I) (M := M) X f) x • Y x)
          (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x))
    have hsmul₁ :
        ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) X f) x • Y x)) (Z x) =
          (TangentSection.toDerivation (I := I) (M := M) X f) x * ((g.inner x) (Y x)) (Z x) := by
      simpa only [_root_.smul_apply, smul_eq_mul] using
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Z x))
          ((g.inner x).map_smul (((TangentSection.toDerivation (I := I) (M := M) X f) x)) (Y x))
    have hsmul₂ :
        ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) =
          f x *
            ((g.inner x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) := by
      simp [smul_eq_mul]
    -- Finish.
    calc
      ((g.inner x)
            ((TangentSection.toDerivation (I := I) (M := M) X f) x • Y x +
              f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x)
          =
          ((g.inner x) ((TangentSection.toDerivation (I := I) (M := M) X f) x • Y x)) (Z x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) := by
            exact hadd
      _ =
          (TangentSection.toDerivation (I := I) (M := M) X f) x * ((g.inner x) (Y x)) (Z x) +
            f x *
              ((g.inner x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) := by
            rw [hsmul₁, hsmul₂]
  have hinner_brYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) (f • Y) Z) X x =
        -((TangentSection.toDerivation (I := I) (M := M) Z f) x) *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y X x +
          f x *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) g
                (SmoothTangentSection.mlieBracket (I := I) Y Z) X x := by
    simp [-TangentSection.toDerivation_apply, smoothTangentSectionInnerFromMetric_apply,
      SmoothTangentSection.mlieBracket_apply]
    have hbrYZ' :
        VectorField.mlieBracket I (fun z : M => f z • Y z) (fun z : M => Z z) x =
          -((TangentSection.toDerivation (I := I) (M := M) Z f) x) • Y x +
            f x • VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x := by
      simpa only [hdfZ] using! hbrYZ
    rw [hbrYZ']
    have hadd :=
      congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x))
        ((g.inner x).map_add
          (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • Y x)
          (f x • VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x))
    have hsmul₁ :
        ((g.inner x) (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • Y x)) (X x) =
          -(((TangentSection.toDerivation (I := I) (M := M) Z f) x) * ((g.inner x) (Y x)) (X x)) := by
      simpa only [_root_.smul_apply, smul_eq_mul, neg_mul] using
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x))
          ((g.inner x).map_smul (-(((TangentSection.toDerivation (I := I) (M := M) Z f) x))) (Y x))
    have hsmul₂ :
        ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x)) (X x) =
          f x *
            ((g.inner x) (VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x)) (X x) := by
      simp [smul_eq_mul]
    calc
      ((g.inner x)
            (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • Y x +
              f x • VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x)) (X x)
          =
          ((g.inner x) (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • Y x)) (X x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x)) (X x) := by
            exact hadd
      _ =
          -(((TangentSection.toDerivation (I := I) (M := M) Z f) x) * ((g.inner x) (Y x)) (X x)) +
            f x *
              ((g.inner x) (VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x)) (X x) := by
            rw [hsmul₁, hsmul₂]
  have hsymmXY : smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y X x =
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y x := by
    simp [smoothTangentSectionInnerFromMetric_apply]
    exact g.symm x (Y x) (X x)
  -- Expand all terms and finish by commutative-ring algebra (the `Z(f)` terms cancel by symmetry).
  simp [-TangentSection.toDerivation_apply, koszulRHS, hYZ, hXY, hDY,
    Derivation.leibniz, hinner_brXY,
    hinner_brYZ, hsymmXY, smoothTangentSectionInnerFromMetric_apply, sub_eq_add_neg, smul_eq_mul]
  ring_nf

/-- `C^∞`-linearity of the Koszul RHS in the first slot. -/
theorem koszulRHS_smul_left
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z : Γ∞) (f : C∞) :
    koszulRHS (I := I) (M := M) (E := E) g (f • X) Y Z =
      f * koszulRHS (I := I) (M := M) (E := E) g X Y Z := by
  ext x
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M)
      (hmn := (le_minSmoothness (𝕜 := ℝ) (n := (2 : WithTop ℕ∞))))
  have hDX :
      (TangentSection.toDerivation (I := I) (M := M) (f • X))
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) x =
        (f x) *
          (TangentSection.toDerivation (I := I) (M := M) X)
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z) x := by
    simp [TangentSection.toDerivation_smul (I := I) (M := M), smul_eq_mul]
  have hZX :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z (f • X) =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X :=
    inner_smul_right (I := I) (M := M) (E := E) (g := g) Z X f
  have hXY :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g (f • X) Y =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y :=
    inner_smul_left (I := I) (M := M) (E := E) (g := g) X Y f
  have hInnerYZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) Y Z) (f • X) =
        f * smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) Y Z) X :=
    inner_smul_right (I := I) (M := M) (E := E) (g := g)
      (SmoothTangentSection.mlieBracket (I := I) Y Z) X f
  have hdfY :
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (Y x) =
        (TangentSection.toDerivation (I := I) (M := M) Y f) x := by
    simp [TangentSection.toDerivation_apply]
  have hdfZ :
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (Z x) =
        (TangentSection.toDerivation (I := I) (M := M) Z f) x := by
    simp [TangentSection.toDerivation_apply]
  have hbrXY :=
    SmoothTangentSection.mlieBracket_smul_left (I := I) (X := X) (Y := Y) (f := f) (x := x)
  have hbrXZ :=
    SmoothTangentSection.mlieBracket_smul_left (I := I) (X := X) (Y := Z) (f := f) (x := x)
  have hinner_brXY :
      (smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) (f • X) Y) Z) x =
        -(((TangentSection.toDerivation (I := I) (M := M) Y f) x) *
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Z) x) +
          (f x) *
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g
                (SmoothTangentSection.mlieBracket (I := I) X Y) Z) x := by
    simp [-TangentSection.toDerivation_apply, smoothTangentSectionInnerFromMetric_apply,
      SmoothTangentSection.mlieBracket_apply]
    have hbrXY' :
        VectorField.mlieBracket I (fun z : M => f z • X z) (fun z : M => Y z) x =
          -((TangentSection.toDerivation (I := I) (M := M) Y f) x) • X x +
            f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x := by
      simpa only [hdfY] using! hbrXY
    rw [hbrXY']
    have hadd :=
      congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Z x))
        ((g.inner x).map_add
          (-((TangentSection.toDerivation (I := I) (M := M) Y f) x) • X x)
          (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x))
    have hsmul₁ :
        ((g.inner x) (-((TangentSection.toDerivation (I := I) (M := M) Y f) x) • X x)) (Z x) =
          -(((TangentSection.toDerivation (I := I) (M := M) Y f) x) * ((g.inner x) (X x)) (Z x)) := by
      simpa only [_root_.smul_apply, smul_eq_mul, neg_mul] using
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Z x))
          ((g.inner x).map_smul (-(((TangentSection.toDerivation (I := I) (M := M) Y f) x))) (X x))
    have hsmul₂ :
        ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) =
          (f x) * ((g.inner x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) := by
      simp [smul_eq_mul]
    calc
      ((g.inner x)
            (-((TangentSection.toDerivation (I := I) (M := M) Y f) x) • X x +
              f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x)
          =
          ((g.inner x) (-((TangentSection.toDerivation (I := I) (M := M) Y f) x) • X x)) (Z x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) := by
            exact hadd
      _ =
          -(((TangentSection.toDerivation (I := I) (M := M) Y f) x) * ((g.inner x) (X x)) (Z x)) +
            (f x) * ((g.inner x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x)) (Z x) := by
            rw [hsmul₁, hsmul₂]
  have hinner_brXZ :
      (smoothTangentSectionInnerFromMetric (I := I) (M := M) g
          (SmoothTangentSection.mlieBracket (I := I) (f • X) Z) Y) x =
        -(((TangentSection.toDerivation (I := I) (M := M) Z f) x) *
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y) x) +
          (f x) *
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g
                (SmoothTangentSection.mlieBracket (I := I) X Z) Y) x := by
    simp [-TangentSection.toDerivation_apply, smoothTangentSectionInnerFromMetric_apply,
      SmoothTangentSection.mlieBracket_apply]
    have hbrXZ' :
        VectorField.mlieBracket I (fun z : M => f z • X z) (fun z : M => Z z) x =
          -((TangentSection.toDerivation (I := I) (M := M) Z f) x) • X x +
            f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x := by
      simpa only [hdfZ] using! hbrXZ
    rw [hbrXZ']
    have hadd :=
      congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Y x))
        ((g.inner x).map_add
          (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • X x)
          (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x))
    have hsmul₁ :
        ((g.inner x) (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • X x)) (Y x) =
          -(((TangentSection.toDerivation (I := I) (M := M) Z f) x) * ((g.inner x) (X x)) (Y x)) := by
      simpa only [_root_.smul_apply, smul_eq_mul, neg_mul] using
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (Y x))
          ((g.inner x).map_smul (-(((TangentSection.toDerivation (I := I) (M := M) Z f) x))) (X x))
    have hsmul₂ :
        ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x)) (Y x) =
          (f x) * ((g.inner x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x)) (Y x) := by
      simp [smul_eq_mul]
    calc
      ((g.inner x)
            (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • X x +
              f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x)) (Y x)
          =
          ((g.inner x) (-((TangentSection.toDerivation (I := I) (M := M) Z f) x) • X x)) (Y x) +
            ((g.inner x) (f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x)) (Y x) := by
            exact hadd
      _ =
          -(((TangentSection.toDerivation (I := I) (M := M) Z f) x) * ((g.inner x) (X x)) (Y x)) +
            (f x) * ((g.inner x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x)) (Y x) := by
            rw [hsmul₁, hsmul₂]
  have hsymmXZ :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X x =
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Z x := by
    simpa [smoothTangentSectionInnerFromMetric_apply] using (g.symm x (Z x) (X x))
  -- Expand all terms and finish by commutative-ring algebra (the `Y(f)` and `Z(f)` terms cancel).
  simp [-TangentSection.toDerivation_apply, koszulRHS, hDX, hZX, hXY, hInnerYZ, Derivation.leibniz,
    hinner_brXY, hinner_brXZ, hsymmXZ, smoothTangentSectionInnerFromMetric_apply, sub_eq_add_neg]
  ring_nf

/-- `C^∞`-linearity of the Koszul RHS in the third slot, packaged as a `C^∞`-linear map. -/
noncomputable def koszulRHSLinear
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) :
    Γ∞ →ₗ[C∞] C∞ where
  toFun Z := koszulRHS (I := I) (M := M) (E := E) g X Y Z
  map_add' Z₁ Z₂ := koszulRHS_add_right (I := I) (M := M) (E := E) (g := g) X Y Z₁ Z₂
  map_smul' f Z := by
    -- `C∞` acts on itself by multiplication.
    simpa [smul_eq_mul] using
      (koszulRHS_smul_right (I := I) (M := M) (E := E) (g := g) X Y Z f)

end KoszulRHS

section KoszulAtPoint

variable [FiniteDimensional ℝ E] [T2Space M]

/-- The Koszul RHS, evaluated at a point, factors through the tangent fiber at that point. -/
theorem exists_koszulRHSLinearAt
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) (x₀ : M) :
    ∃ ℓ : TangentSpace I x₀ →ₗ[ℝ] ℝ,
      ∀ Z : Γ∞, (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x₀ = ℓ (Z x₀) := by
  simpa [koszulRHSLinear] using
    (SmoothTangentSection.exists_eval_eq_linear_apply (I := I) (M := M) (E := E) x₀
      (koszulRHSLinear (I := I) (M := M) (E := E) g X Y))

/-! ### Riesz representation at a point -/

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] [T2Space M] in
/-- In a Riemannian tangent fiber, every linear functional is represented by `g.inner x₀ w` for
some `w`. This is the pointwise Riesz representation theorem, phrased in terms of the metric data
`g.inner`. -/
theorem exists_inner_eq_linear_apply
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M) (ℓ : TangentSpace I x₀ →ₗ[ℝ] ℝ) :
    ∃ w : TangentSpace I x₀, ∀ v : TangentSpace I x₀, ℓ v = (g.inner x₀ w) v := by
  classical
  -- Interpret `g.inner x₀` as a nondegenerate bilinear form on the tangent fiber.
  let B : LinearMap.BilinForm ℝ (TangentSpace I x₀) :=
    (ContinuousLinearMap.coeLM (S := ℝ) (R := ℝ) (M := TangentSpace I x₀) (N₃ := ℝ)) ∘ₗ
      (g.inner x₀ : TangentSpace I x₀ →ₗ[ℝ] TangentSpace I x₀ →L[ℝ] ℝ)
  have hB_apply (u v : TangentSpace I x₀) : B u v = (g.inner x₀ u) v := by
    simp [B]
  have hB : B.Nondegenerate := by
    constructor
    · intro v hv
      by_contra hv0
      have hpos : 0 < (g.inner x₀ v) v := g.pos x₀ v hv0
      have : (g.inner x₀ v) v = 0 := by
        simpa [hB_apply] using (hv v)
      exact (ne_of_gt hpos) this
    · intro v hv
      by_contra hv0
      have hpos : 0 < (g.inner x₀ v) v := g.pos x₀ v hv0
      have : (g.inner x₀ v) v = 0 := by
        simpa [hB_apply] using (hv v)
      exact (ne_of_gt hpos) this
  refine ⟨(B.toDual hB).symm ℓ, ?_⟩
  intro v
  have h := (LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB) ℓ v)
  calc
    ℓ v = B ((B.toDual hB).symm ℓ) v := by
          exact h.symm
    _ = (g.inner x₀ ((B.toDual hB).symm ℓ)) v := by simp [hB_apply]

/-- The bilinear form on a tangent fiber induced by a Riemannian metric. -/
noncomputable def metricBilinForm (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x₀) :=
  (ContinuousLinearMap.coeLM (S := ℝ) (R := ℝ) (M := TangentSpace I x₀) (N₃ := ℝ)) ∘ₗ
    (g.inner x₀ : TangentSpace I x₀ →ₗ[ℝ] TangentSpace I x₀ →L[ℝ] ℝ)

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]
    [FiniteDimensional ℝ E] [T2Space M] in
/-- The metric bilinear form evaluates to the supplied Riemannian inner product. -/
@[simp]
theorem metricBilinForm_apply (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M)
    (u v : TangentSpace I x₀) :
    metricBilinForm (I := I) (M := M) (E := E) g x₀ u v = (g.inner x₀ u) v := by
  simp [metricBilinForm]

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]
    [FiniteDimensional ℝ E] [T2Space M] in
/-- The bilinear form induced by the Riemannian metric is nondegenerate. -/
theorem metricBilinForm_nondegenerate (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M) :
    (metricBilinForm (I := I) (M := M) (E := E) g x₀).Nondegenerate := by
  constructor
  · intro v hv
    by_contra hv0
    have hpos : 0 < (g.inner x₀ v) v := g.pos x₀ v hv0
    have : (g.inner x₀ v) v = 0 := by
      simpa [metricBilinForm_apply] using (hv v)
    exact (ne_of_gt hpos) this
  · intro v hv
    by_contra hv0
    have hpos : 0 < (g.inner x₀ v) v := g.pos x₀ v hv0
    have : (g.inner x₀ v) v = 0 := by
      simpa [metricBilinForm_apply] using (hv v)
    exact (ne_of_gt hpos) this

/-- The linear equivalence `TM x₀ ≃ₗ (TM x₀)ᵗ` induced by the Riemannian metric at `x₀`. -/
noncomputable def metricToDual (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M) :
    TangentSpace I x₀ ≃ₗ[ℝ] (TangentSpace I x₀ →ₗ[ℝ] ℝ) := by
  classical
  exact
    (metricBilinForm (I := I) (M := M) (E := E) g x₀).toDual
      (metricBilinForm_nondegenerate (I := I) (M := M) (E := E) (g := g) x₀)

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] [T2Space M] in
/-- Evaluating the metric bilinear form on the inverse metric-to-dual image recovers the
original linear functional at the given tangent vector. -/
theorem metricBilinForm_metricToDual_symm_apply (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M)
    (ℓ : TangentSpace I x₀ →ₗ[ℝ] ℝ) (v : TangentSpace I x₀) :
    metricBilinForm (I := I) (M := M) (E := E) g x₀
        ((metricToDual (I := I) (M := M) (E := E) g x₀).symm ℓ) v = ℓ v := by
  classical
  simp [metricToDual]

/-- The Koszul RHS, evaluated at a point, is represented by an inner product against some vector in
the tangent fiber. -/
theorem exists_koszulRHSInnerAt
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) (x₀ : M) :
    ∃ w : TangentSpace I x₀,
      ∀ Z : Γ∞, (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x₀ = (g.inner x₀ w) (Z x₀) := by
  rcases
      exists_koszulRHSLinearAt (I := I) (M := M) (E := E) (g := g) (X := X) (Y := Y) x₀ with
    ⟨ℓ, hℓ⟩
  rcases exists_inner_eq_linear_apply (I := I) (M := M) (E := E) (g := g) x₀ ℓ with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  intro Z
  calc
    (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x₀ = ℓ (Z x₀) := hℓ Z
    _ = (g.inner x₀ w) (Z x₀) := hw (Z x₀)

end KoszulAtPoint

end SmoothTangentSection

end
