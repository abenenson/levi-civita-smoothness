import Mathlib.Geometry.Manifold.VectorBundle.Tangent

import MathlibExtensions.Geometry.Manifold.VectorBundle.Connection
import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionDerivation

/-!
# Tangent-bundle connections (vector-field input)

`MathlibExtensions.Geometry.Manifold.VectorBundle.Connection` defines a derivation-based
`SmoothConnection` interface:

`covDeriv : Derivation ℝ C^∞ C^∞ → Γ∞ → Γ∞`.

For Levi–Civita, it is often more natural to view the first argument as a *smooth tangent section*
(`Γ∞TM`), acting on functions via `TangentSection.toDerivation`.

This module introduces a small tangent-bundle-specific interface `SmoothTangentConnection`, and
shows that any derivation-based `SmoothConnection` restricts to it.
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

local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, fun x : M => TangentSpace I x⟯

/-- A smooth connection on the tangent bundle, with vector-field input encoded as a smooth tangent
section `Γ∞` (rather than an arbitrary derivation). -/
structure SmoothTangentConnection where
  /-- Covariant derivative of a tangent section along a tangent section. -/
  covDeriv : Γ∞ → Γ∞ → Γ∞
  /-- Additivity in the section argument. -/
  covDeriv_add : ∀ X s t, covDeriv X (s + t) = covDeriv X s + covDeriv X t
  /-- `ℝ`-linearity in the section argument. -/
  covDeriv_smul : ∀ X (a : ℝ) s, covDeriv X (a • s) = a • covDeriv X s
  /-- Additivity in the vector field argument. -/
  covDeriv_add_vec : ∀ X Y s, covDeriv (X + Y) s = covDeriv X s + covDeriv Y s
  /-- `C^∞`-linearity in the vector field argument. -/
  covDeriv_smul_vec : ∀ (f : C∞) X s, covDeriv (f • X) s = f • covDeriv X s
  /-- Leibniz rule for smooth-function scalar multiplication on sections. -/
  leibniz :
    ∀ (X) (f : C∞) s,
      covDeriv X (f • s) =
        (TangentSection.toDerivation (I := I) (M := M) X f) • s + f • covDeriv X s

namespace SmoothTangentConnection

variable (conn : SmoothTangentConnection (I := I) (M := M) (E := E))

/-- For a fixed vector field `X`, `∇_X` is a linear endomorphism of smooth tangent sections. -/
noncomputable def covDerivLin (X : Γ∞) : Γ∞ →ₗ[ℝ] Γ∞ :=
  { toFun := fun s => conn.covDeriv X s
    map_add' := by intro s t; simpa using conn.covDeriv_add X s t
    map_smul' := by intro a s; simpa using conn.covDeriv_smul X a s }

@[simp]
theorem covDerivLin_apply (X s : Γ∞) : conn.covDerivLin (I := I) (M := M) X s = conn.covDeriv X s :=
  rfl

end SmoothTangentConnection

namespace SmoothConnection

variable
  (conn :
    SmoothConnection (I := I) (F := E) (V := fun x : M => TangentSpace I x) (𝕜 := ℝ) (M := M))

/-- Restrict a derivation-based connection on `TM` to a tangent-section input connection, by
precomposing with `TangentSection.toDerivation`. -/
noncomputable def restrictToTangent : SmoothTangentConnection (I := I) (M := M) (E := E) where
  covDeriv X Y := conn.covDeriv (TangentSection.toDerivation (I := I) (M := M) X) Y
  covDeriv_add X s t := by
    simpa using conn.covDeriv_add (TangentSection.toDerivation (I := I) (M := M) X) s t
  covDeriv_smul X a s := by
    simpa using conn.covDeriv_smul (TangentSection.toDerivation (I := I) (M := M) X) a s
  covDeriv_add_vec X Y s := by
    -- rewrite `(X+Y)` at the derivation level
    simpa [TangentSection.toDerivation_add (I := I) (M := M)] using
      (conn.covDeriv_add_vec (TangentSection.toDerivation (I := I) (M := M) X)
        (TangentSection.toDerivation (I := I) (M := M) Y) s)
  covDeriv_smul_vec f X s := by
    simpa [TangentSection.toDerivation_smul (I := I) (M := M)] using
      (conn.covDeriv_smul_vec (f := f) (TangentSection.toDerivation (I := I) (M := M) X) s)
  leibniz X f s := by
    -- This is exactly the Leibniz axiom of `SmoothConnection`.
    simpa using conn.leibniz (TangentSection.toDerivation (I := I) (M := M) X) f s

end SmoothConnection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle

