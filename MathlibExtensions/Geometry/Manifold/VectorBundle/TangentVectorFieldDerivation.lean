/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.RingTheory.Derivation.Lie

@[expose] public section

/-!
# `MathlibExtensions.Geometry.Manifold.VectorBundle.TangentVectorFieldDerivation`

Mathlib provides two complementary “vector field” viewpoints:

1. **Geometric:** a vector field is a section of the tangent bundle `TM`, encoded as a map
   `x ↦ ⟨x, v x⟩ : TM` together with a manifold-smoothness proof.
2. **Algebraic:** a vector field acts on smooth scalar functions as a **derivation**
   `C^∞(M;𝕜) → C^∞(M;𝕜)`.

For our retained chart localization curvature/connection work we use the algebraic (derivation) viewpoint because:
- derivations form a Lie algebra (commutator bracket) without any additional setup, and
- it gives an upstreamable interface boundary for connections/curvature.

This module implements the forward bridge:

*a smooth geometric tangent vector field induces a derivation on `C^∞(M;𝕜)` via directional
derivative.*

We do **not** attempt the inverse direction (derivation ⇒ geometric vector field); that requires
additional locality/smoothness structure on algebraic derivations. The inverse direction is
outside this package's scope.
-/

open scoped Manifold ContDiff

namespace MathlibExtensions
namespace Geometry
namespace Manifold
namespace VectorBundle

section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

local notation "C∞" => C^∞⟮I, M; 𝕜⟯
local notation "I𝕜" => 𝓘(𝕜, 𝕜)

/-- A `C^∞` geometric tangent vector field, encoded as a smooth section `x ↦ ⟨x, v x⟩ : TM`.

This is a minimal bundled type sufficient to build a derivation on `C^∞(M;𝕜)`. -/
structure SmoothTangentVectorField where
  /-- The underlying pointwise tangent vector. -/
  toFun : ∀ x : M, TangentSpace I x
  /-- Smoothness of the induced map into the tangent bundle. -/
  contMDiff_toBundle : ContMDiff I I.tangent (∞ : WithTop ℕ∞)
    (fun x : M => (⟨x, toFun x⟩ : TangentBundle I M))

namespace SmoothTangentVectorField

instance : CoeFun (SmoothTangentVectorField (I := I) (M := M)) (fun _ => ∀ x : M, TangentSpace I x) :=
  ⟨SmoothTangentVectorField.toFun⟩

/-- Directional derivative of a smooth function along a smooth geometric vector field. -/
noncomputable def deriv (X : SmoothTangentVectorField (I := I) (M := M))
    (f : C∞) : C∞ := by
    classical
    -- Build as a `C^∞` map via `tangentMap` composed with the section `x ↦ ⟨x, X x⟩`,
    -- then project to the tangent component.
    refine ⟨fun x => (mfderiv I I𝕜 (f : M → 𝕜) x) (X x), ?_⟩
    have h_tangentMap :
        ContMDiff I.tangent ((I𝕜).tangent) (∞ : WithTop ℕ∞) (tangentMap I I𝕜 (f : M → 𝕜)) := by
      -- `∞ + 1 = ∞` in `WithTop ℕ∞`, so `m+1 ≤ n` is `le_rfl`.
      exact
        f.contMDiff.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
          (by simp : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞))
    have h_comp :
        ContMDiff I ((I𝕜).tangent) (∞ : WithTop ℕ∞)
          (fun x : M => tangentMap I I𝕜 (f : M → 𝕜) (⟨x, X x⟩ : TangentBundle I M)) :=
      h_tangentMap.comp X.contMDiff_toBundle
    have h_snd :
        ContMDiff ((I𝕜).tangent) I𝕜 (∞ : WithTop ℕ∞)
          (fun (p : TangentBundle I𝕜 𝕜) => p.2) := by
      -- The base is the model space `𝕜`, so we can use the model-space lemma.
      simpa using (contMDiff_snd_tangentBundle_modelSpace (H := 𝕜) (I := I𝕜) (n := (∞ : WithTop ℕ∞)))
    -- Compose to get smoothness of the directional derivative as a scalar function.
    have : ContMDiff I I𝕜 (∞ : WithTop ℕ∞)
        (fun x : M => (tangentMap I I𝕜 (f : M → 𝕜) (⟨x, X x⟩ : TangentBundle I M)).2) :=
      h_snd.comp h_comp
    -- The displayed function is definitional equal to `x ↦ mfderiv f x (X x)`.
    simpa [tangentMap] using this

/-- Evaluating the directional derivative applies the manifold derivative to the vector field. -/
@[simp]
theorem deriv_apply (X : SmoothTangentVectorField (I := I) (M := M)) (f : C∞) (x : M) :
    X.deriv f x = (mfderiv I I𝕜 (f : M → 𝕜) x) (X x) :=
  rfl

section Derivation

/-- A smooth geometric tangent vector field induces a derivation on `C^∞(M;𝕜)`. -/
noncomputable def toDerivation (X : SmoothTangentVectorField (I := I) (M := M)) :
    Derivation 𝕜 C∞ C∞ where
  toLinearMap :=
    { toFun := fun f => X.deriv f
      map_add' := by
        intro f g
        ext x
        have h :
            (by
                exact
                  mfderiv I I𝕜 (fun y => f y + g y) x : TangentSpace I x →L[𝕜] 𝕜) =
              (by exact mfderiv I I𝕜 (f : M → 𝕜) x : TangentSpace I x →L[𝕜] 𝕜) +
                (by exact mfderiv I I𝕜 (g : M → 𝕜) x : TangentSpace I x →L[𝕜] 𝕜) := by
          simpa using!
            (mfderiv_add (I := I) (z := x) (f := (f : M → 𝕜)) (g := (g : M → 𝕜))
              (hf := (f.mdifferentiableAt (x := x))) (hg := (g.mdifferentiableAt (x := x))))
        have h_apply := congrArg (fun L => L (X x)) h
        simpa [SmoothTangentVectorField.deriv_apply, _root_.add_apply] using! h_apply
      map_smul' := by
        intro a f
        ext x
        have h :
            (by
                exact
                  mfderiv I I𝕜 (fun y => a • f y) x : TangentSpace I x →L[𝕜] 𝕜) =
              a • (by exact mfderiv I I𝕜 (f : M → 𝕜) x : TangentSpace I x →L[𝕜] 𝕜) := by
          simpa using!
            (const_smul_mfderiv (I := I) (z := x) (f := (f : M → 𝕜))
              (hf := (f.mdifferentiableAt (x := x))) a)
        have h_apply := congrArg (fun L => L (X x)) h
        simpa [SmoothTangentVectorField.deriv_apply, _root_.smul_apply, smul_eq_mul] using! h_apply
    }
  map_one_eq_zero' := by
    ext x
    -- `mfderiv` of a constant is zero, hence the directional derivative of `1` is zero.
    change (mfderiv I I𝕜 (fun _ : M => (1 : 𝕜)) x) (X x) = 0
    simp
  leibniz' := by
    intro f g
    ext x
    -- Use the manifold product rule for `mfderiv` and evaluate on the tangent vector `X x`.
    have hf : HasMFDerivAt I I𝕜 (f : M → 𝕜) x (by exact mfderiv I I𝕜 (f : M → 𝕜) x :
        TangentSpace I x →L[𝕜] 𝕜) :=
      (f.mdifferentiableAt (x := x)).hasMFDerivAt
    have hg : HasMFDerivAt I I𝕜 (g : M → 𝕜) x (by exact mfderiv I I𝕜 (g : M → 𝕜) x :
        TangentSpace I x →L[𝕜] 𝕜) :=
      (g.mdifferentiableAt (x := x)).hasMFDerivAt
    have hmul :
        (mfderiv I I𝕜 (fun y => f y * g y) x : TangentSpace I x →L[𝕜] 𝕜) =
          (f x • (by exact mfderiv I I𝕜 (g : M → 𝕜) x : TangentSpace I x →L[𝕜] 𝕜) +
            g x • (by exact mfderiv I I𝕜 (f : M → 𝕜) x : TangentSpace I x →L[𝕜] 𝕜)) := by
      -- Derivative of multiplication in the target normed commutative ring.
      simpa using! (HasMFDerivAt.mul (I := I) (z := x) (F' := 𝕜) hf hg).mfderiv
    -- Apply both sides to `X x`.
    have hmul_apply := congrArg (fun L => L (X x)) hmul
    -- unfold `deriv` and evaluate linear-map operations
    simpa [SmoothTangentVectorField.deriv_apply, hmul_apply, _root_.add_apply,
      _root_.smul_apply, smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The induced derivation evaluates by applying the manifold derivative to the vector field. -/
@[simp]
theorem toDerivation_apply (X : SmoothTangentVectorField (I := I) (M := M)) (f : C∞) (x : M) :
    X.toDerivation f x = (mfderiv I I𝕜 (f : M → 𝕜) x) (X x) :=
  rfl

end Derivation

end SmoothTangentVectorField

end

end VectorBundle
end Manifold
end Geometry
end MathlibExtensions
