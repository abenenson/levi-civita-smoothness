/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Geometry.Manifold.DerivationBundle
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.RingTheory.Derivation.Lie

@[expose] public section

/-!
# `MathlibExtensions.Geometry.Manifold.VectorBundle.Connection`

Mathlib provides the `CovariantDerivative` interface for connections on vector bundles.
This module retains the smooth-section and derivation interface used by the direct smooth
Koszul construction. The `LeviCivitaSmoothness` bridge identifies that construction with
Mathlib's chosen Levi-Civita covariant derivative on global smooth inputs.

The retained interface is phrased in terms of derivations of the commutative ring `C^∞(M; 𝕜)`:

- we first equip smooth sections with a natural scalar action by smooth functions, and
- then define a connection as an operator `∇ₓ s` satisfying `C^∞`-linearity in `x` and the
  Leibniz rule in `s`.

The operator satisfies the usual connection axioms. This support module itself does not
construct a metric connection or prove curvature identities.

## Main definitions

- `MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothVectorField`:
  derivations of smooth functions, `Derivation 𝕜 C^∞ C^∞` (alias).
- `MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothConnection`:
  a smooth vector bundle connection `∇`.

## Notes

The local notations `Γ∞` and `C∞` abbreviate smooth sections and smooth scalar functions;
they do not introduce additional exported declarations.

For finite-dimensional smooth real manifolds, derivations of `C^∞(M)` coincide with classical
smooth vector fields. We keep this file purely algebraic (derivation-based); any equivalence layer
belongs in a subsequent module.
-/

open scoped Bundle Manifold ContDiff

namespace MathlibExtensions
namespace Geometry
namespace Manifold
namespace VectorBundle

open Bundle

-- `ContMDiff` uses `n : WithTop ℕ∞`; `∞` is the standard “smooth” index (as opposed to `ω = ⊤`).
local notation "n∞" => (∞ : WithTop ℕ∞)

section SmulBySmoothFunctions

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [TopologicalSpace (Bundle.TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

local notation "C∞" => C^n∞⟮I, M; 𝕜⟯
local notation "Γ∞" => Cₛ^n∞⟮I; F, V⟯

noncomputable instance instSMulSmoothFunctionSmoothSection : SMul C∞ Γ∞ :=
  ⟨fun f s =>
    ⟨fun x => f x • s x,
      (f.contMDiff.smul_section s.contMDiff)⟩⟩

/-- The smooth-function scalar action on smooth sections evaluates pointwise. -/
@[simp]
theorem smul_apply (f : C∞) (s : Γ∞) (x : M) : (f • s) x = f x • s x :=
  rfl

noncomputable instance instModuleSmoothFunctionSmoothSection : Module C∞ Γ∞ where
  smul := (· • ·)
  smul_add := by
    intro f s t
    ext x
    simp [smul_apply, smul_add]
  add_smul := by
    intro f g s
    ext x
    simp [smul_apply, add_smul]
  mul_smul := by
    intro f g s
    ext x
    simp [smul_apply, mul_smul]
  one_smul := by
    intro s
    ext x
    simp [smul_apply]
  zero_smul := by
    intro s
    ext x
    simp [smul_apply]
  smul_zero := by
    intro f
    ext x
    simp [smul_apply]

end SmulBySmoothFunctions

section Connection

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [TopologicalSpace (Bundle.TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

local notation "C∞" => C^n∞⟮I, M; 𝕜⟯
local notation "Γ∞" => Cₛ^n∞⟮I; F, V⟯

/-- A (derivation-based) smooth vector field: an `𝕜`-derivation of `C^∞(M;𝕜)` to itself. -/
abbrev SmoothVectorField : Type _ := Derivation 𝕜 C∞ C∞

/-- A smooth connection on a vector bundle, phrased via derivations on `C^∞(M;𝕜)`.

This is the standard `C^∞`-linear / Leibniz interface:

- `∇_{f • X} s = f • ∇_X s` (linearity in the vector field over smooth functions),
- `∇_X (f • s) = X(f) • s + f • ∇_X s` (Leibniz rule in the section variable).
-/
structure SmoothConnection where
  /-- Covariant derivative of a smooth section along a smooth vector field. -/
  covDeriv : SmoothVectorField (I := I) (M := M) (𝕜 := 𝕜) → Γ∞ → Γ∞
  /-- Additivity in the section argument. -/
  covDeriv_add : ∀ X s t, covDeriv X (s + t) = covDeriv X s + covDeriv X t
  /-- `𝕜`-linearity in the section argument. -/
  covDeriv_smul : ∀ X (a : 𝕜) s, covDeriv X (a • s) = a • covDeriv X s
  /-- Additivity in the vector field argument. -/
  covDeriv_add_vec : ∀ X Y s, covDeriv (X + Y) s = covDeriv X s + covDeriv Y s
  /-- `C^∞`-linearity in the vector field argument. -/
  covDeriv_smul_vec :
    ∀ (f : C∞) X s, covDeriv (f • X) s = f • covDeriv X s
  /-- Leibniz rule for smooth-function scalar multiplication on sections. -/
  leibniz :
    ∀ (X) (f : C∞) s,
      covDeriv X (f • s) = (X f) • s + f • covDeriv X s

namespace SmoothConnection

/-- For a fixed vector field `X`, `∇_X` is a `𝕜`-linear endomorphism of smooth sections. -/
noncomputable def covDerivLin (conn : SmoothConnection (I := I) (F := F) (V := V))
    (X : SmoothVectorField (I := I) (M := M) (𝕜 := 𝕜)) : Γ∞ →ₗ[𝕜] Γ∞ :=
  { toFun := fun s => conn.covDeriv X s
    map_add' := by intro s t; simpa using conn.covDeriv_add X s t
    map_smul' := by intro a s; simpa using conn.covDeriv_smul X a s }

/-- The linear covariant-derivative map evaluates to the supplied connection derivative. -/
@[simp]
theorem covDerivLin_apply (conn : SmoothConnection (I := I) (F := F) (V := V))
    (X : SmoothVectorField (I := I) (M := M) (𝕜 := 𝕜)) (s : Γ∞) :
    covDerivLin (I := I) (M := M) (F := F) (V := V) (𝕜 := 𝕜) conn X s =
      conn.covDeriv X s :=
  rfl

end SmoothConnection

end Connection

end VectorBundle
end Manifold
end Geometry
end MathlibExtensions
