/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

public import MathlibExtensions.Geometry.Manifold.VectorBundle.Connection
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentVectorFieldDerivation

@[expose] public section

/-!
# Tangent sections as derivations of `C^∞(M)`

This module packages the common coercion used throughout the curvature/connection stack:

*a smooth section of the tangent bundle induces a derivation of smooth scalar functions*.

Concretely, we:
- reinterpret a smooth tangent-bundle section as a bundled `SmoothTangentVectorField`, then
- use `SmoothTangentVectorField.toDerivation`.
-/

open scoped Bundle Manifold ContDiff

namespace MathlibExtensions.Geometry.Manifold.VectorBundle

open Bundle

-- `ContMDiff` uses `n : WithTop ℕ∞`; `∞` is the standard “smooth” index (as opposed to `ω = ⊤`).
local notation "n∞" => (∞ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, fun x : M => TangentSpace I x⟯

namespace TangentSection

/-- Interpret a smooth tangent-bundle section as a bundled smooth tangent vector field. -/
noncomputable def toSmoothTangentVectorField (X : Γ∞) :
    SmoothTangentVectorField (I := I) (M := M) :=
  ⟨fun x => X x, by
    -- `Γ∞TM` already stores smoothness of the map into `TM`.
    simpa using X.contMDiff⟩

/-- A smooth tangent-bundle section acts on smooth scalar functions as a derivation. -/
noncomputable def toDerivation (X : Γ∞) :
    Derivation ℝ C∞ C∞ :=
  (toSmoothTangentVectorField (I := I) (M := M) X).toDerivation

/-- The induced derivation evaluates as the manifold derivative in the section direction. -/
@[simp]
theorem toDerivation_apply (X : Γ∞) (f : C∞) (x : M) :
    (toDerivation (I := I) (M := M) X f) x =
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x) :=
  rfl

/-- The derivation induced by the sum of two sections is the sum of their derivations. -/
theorem toDerivation_add (X Y : Γ∞) :
    toDerivation (I := I) (M := M) (X + Y) =
      toDerivation (I := I) (M := M) X + toDerivation (I := I) (M := M) Y := by
  ext f x
  change (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x + Y x) =
    (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x) +
      (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (Y x)
  exact map_add (mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x) (Y x)

/-- Scaling a section by a smooth function scales its induced derivation by that function. -/
theorem toDerivation_smul (f : C∞) (X : Γ∞) :
    toDerivation (I := I) (M := M) (f • X) =
      f • toDerivation (I := I) (M := M) X := by
  ext g x
  -- Both sides are derivations; evaluate pointwise.
  -- The directional derivative is linear in the direction, hence scales by `f x`.
  change (mfderiv I 𝓘(ℝ, ℝ) (g : M → ℝ) x) (f x • X x) =
    f x • (mfderiv I 𝓘(ℝ, ℝ) (g : M → ℝ) x) (X x)
  exact map_smul (mfderiv I 𝓘(ℝ, ℝ) (g : M → ℝ) x) (f x) (X x)

/-- Pointwise Leibniz rule for the derivation induced by a smooth tangent section. -/
theorem toDerivation_mul_apply (X : Γ∞) (f g : C∞) (x : M) :
    (toDerivation (I := I) (M := M) X (f * g)) x =
      (toDerivation (I := I) (M := M) X f) x * g x +
        f x * (toDerivation (I := I) (M := M) X g) x := by
  have h := congrArg (fun h : C∞ => h x)
    ((toDerivation (I := I) (M := M) X).leibniz f g)
  change (toDerivation (I := I) (M := M) X (f * g)) x =
    f x * (toDerivation (I := I) (M := M) X g) x +
      g x * (toDerivation (I := I) (M := M) X f) x at h
  calc
    (toDerivation (I := I) (M := M) X (f * g)) x =
        f x * (toDerivation (I := I) (M := M) X g) x +
          g x * (toDerivation (I := I) (M := M) X f) x := h
    _ = (toDerivation (I := I) (M := M) X f) x * g x +
        f x * (toDerivation (I := I) (M := M) X g) x := by ring

end TangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
