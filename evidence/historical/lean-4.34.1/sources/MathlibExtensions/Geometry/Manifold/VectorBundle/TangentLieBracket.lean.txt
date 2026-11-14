/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

import MathlibExtensions.Geometry.Manifold.VectorField.LieBracket
import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionDerivation
import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionLieBracket

/-!
# Lie bracket Leibniz rules for smooth tangent sections

This module provides convenient wrappers around
`VectorField.mlieBracket_smul_fun_right` / `VectorField.mlieBracket_smul_fun_left` specialized to
smooth tangent sections (`Γ∞`) and smooth scalar functions (`C∞`).
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
  [IsManifold I 2 M] [CompleteSpace E]

local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, fun x : M => TangentSpace I x⟯

namespace SmoothTangentSection

/-- Leibniz rule for the manifold Lie bracket: `[X, f • Y]`. -/
theorem mlieBracket_smul_right (X Y : Γ∞) (f : C∞) (x : M) :
    VectorField.mlieBracket I (fun z : M => X z) (fun z : M => f z • Y z) x =
      ((NormedSpace.fromTangentSpace (f x))
        ((mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x))) • Y x +
        f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x := by
  have hY : MDifferentiableAt I I.tangent (fun z : M ↦ (Y z : TangentBundle I M)) x := by
    simpa using (Y.contMDiff.mdifferentiableAt (x := x) (by simp))
  exact
    (VectorField.mlieBracket_smul_fun_right (I := I) (V := fun z : M => X z) (W := fun z : M => Y z)
      (c := (f : M → ℝ)) (x := x) (hc := f.mdifferentiableAt (x := x))
      (hW := hY))

/-- Leibniz rule for the manifold Lie bracket: `[f • X, Y]`. -/
theorem mlieBracket_smul_left (X Y : Γ∞) (f : C∞) (x : M) :
    VectorField.mlieBracket I (fun z : M => f z • X z) (fun z : M => Y z) x =
      -((NormedSpace.fromTangentSpace (f x))
        ((mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (Y x))) • X x +
        f x • VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x := by
  have hX : MDifferentiableAt I I.tangent (fun z : M ↦ (X z : TangentBundle I M)) x := by
    simpa using (X.contMDiff.mdifferentiableAt (x := x) (by simp))
  exact
    (VectorField.mlieBracket_smul_fun_left (I := I) (V := fun z : M => X z) (W := fun z : M => Y z)
      (c := (f : M → ℝ)) (x := x) (hc := f.mdifferentiableAt (x := x))
      (hV := hX))

/-!
The bundled Lie bracket `SmoothTangentSection.mlieBracket` is only available under the smoothness
assumptions required to build it (`IsManifold I n∞ M` and `IsManifold I (minSmoothness ℝ 2) M`).
-/

section

variable [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M]

/-- Leibniz rule for the smooth tangent-section Lie bracket: `[X, f • Y]`. -/
theorem mlieBracket_smul_right_section (X Y : Γ∞) (f : C∞) :
    SmoothTangentSection.mlieBracket (I := I) X (f • Y) =
      (TangentSection.toDerivation (I := I) (M := M) X f) • Y +
        f • SmoothTangentSection.mlieBracket (I := I) X Y := by
  ext x
  simpa [TangentSection.toDerivation_apply, SmoothTangentSection.mlieBracket_apply,
    smul_apply] using!
    (mlieBracket_smul_right (I := I) (X := X) (Y := Y) (f := f) (x := x))

/-- Leibniz rule for the smooth tangent-section Lie bracket: `[f • X, Y]`. -/
theorem mlieBracket_smul_left_section (X Y : Γ∞) (f : C∞) :
    SmoothTangentSection.mlieBracket (I := I) (f • X) Y =
      - (TangentSection.toDerivation (I := I) (M := M) Y f) • X +
        f • SmoothTangentSection.mlieBracket (I := I) X Y := by
  ext x
  simpa [TangentSection.toDerivation_apply, SmoothTangentSection.mlieBracket_apply,
    smul_apply] using!
    (mlieBracket_smul_left (I := I) (X := X) (Y := Y) (f := f) (x := x))

end

end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
