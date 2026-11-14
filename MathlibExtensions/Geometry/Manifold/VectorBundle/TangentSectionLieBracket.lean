/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Lie bracket of smooth tangent sections

This module bundles the manifold Lie bracket of smooth vector fields (`VectorField.mlieBracket`)
as a smooth tangent section (`Γ∞`).

## Main results

- `SmoothTangentSection.mlieBracket`
- `SmoothTangentSection.mlieBracket_swap`
- `SmoothTangentSection.mlieBracket_self`
- `SmoothTangentSection.mlieBracket_neg_left`
- `SmoothTangentSection.mlieBracket_neg_right`
- `SmoothTangentSection.mlieBracket_jacobi`
- `SmoothTangentSection.mlieBracket_jacobi_left_nested`
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
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

/-- The manifold Lie bracket of smooth tangent sections, bundled as a smooth tangent section. -/
noncomputable def mlieBracket (X Y : Γ∞) : Γ∞ :=
  ⟨fun x => VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x, by
    -- Smoothness of `mlieBracket` follows from the corresponding lemma for smooth vector fields.
    have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
      IsManifold.of_le (I := I) (M := M) (by simp : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞))
    have hX : ContMDiff I I.tangent n∞ (fun x : M ↦ (⟨x, X x⟩ : TangentBundle I M)) := by
      exact X.contMDiff
    have hY : ContMDiff I I.tangent n∞ (fun x : M ↦ (⟨x, Y x⟩ : TangentBundle I M)) := by
      exact Y.contMDiff
    -- `ContDiff.mlieBracket_vectorField` expects indices in `ℕ∞`; use `m = n = ⊤`.
    simpa using
      (ContDiff.mlieBracket_vectorField (I := I) (U := fun x : M => X x) (V := fun x : M => Y x)
        (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hX hY (by simp))
  ⟩

/-- The bundled smooth tangent bracket evaluates to the original manifold vector-field
bracket. -/
@[simp]
theorem mlieBracket_apply (X Y : Γ∞) (x : M) :
    SmoothTangentSection.mlieBracket (I := I) X Y x =
      VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x :=
  rfl

/-- The smooth tangent-section Lie bracket is antisymmetric. -/
theorem mlieBracket_swap (X Y : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) X Y =
      -SmoothTangentSection.mlieBracket (I := I) Y X := by
  ext x
  simpa [SmoothTangentSection.mlieBracket_apply] using
    (VectorField.mlieBracket_swap_apply (I := I) (V := fun z : M => X z)
      (W := fun z : M => Y z) (x := x))

/-- The smooth tangent-section Lie bracket of a section with itself is zero. -/
@[simp]
theorem mlieBracket_self (X : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) X X = 0 := by
  ext x
  simp [SmoothTangentSection.mlieBracket_apply]

/-- Negation in the left input of the smooth tangent-section Lie bracket factors out. -/
@[simp]
theorem mlieBracket_neg_left (X Y : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) (-X) Y =
      -SmoothTangentSection.mlieBracket (I := I) X Y := by
  ext x
  have hX :
      MDifferentiableAt I I.tangent (fun z : M ↦ (⟨z, X z⟩ : TangentBundle I M)) x :=
    X.contMDiff.mdifferentiableAt (by simp)
  have hNeg : (-(fun z : M => X z)) = (fun z : M => -X z) := by
    funext z
    rfl
  simpa [SmoothTangentSection.mlieBracket_apply, Pi.neg_apply, hNeg] using
    (VectorField.mlieBracket_const_smul_left (I := I) (V := fun z : M => X z)
      (W := fun z : M => Y z) (c := (-1 : ℝ)) (x := x) hX)

/-- Negation in the right input of the smooth tangent-section Lie bracket factors out. -/
@[simp]
theorem mlieBracket_neg_right (X Y : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) X (-Y) =
      -SmoothTangentSection.mlieBracket (I := I) X Y := by
  ext x
  have hY :
      MDifferentiableAt I I.tangent (fun z : M ↦ (⟨z, Y z⟩ : TangentBundle I M)) x :=
    Y.contMDiff.mdifferentiableAt (by simp)
  have hNeg : (-(fun z : M => Y z)) = (fun z : M => -Y z) := by
    funext z
    rfl
  simpa [SmoothTangentSection.mlieBracket_apply, Pi.neg_apply, hNeg] using
    (VectorField.mlieBracket_const_smul_right (I := I) (V := fun z : M => X z)
      (W := fun z : M => Y z) (c := (-1 : ℝ)) (x := x) hY)

/-- The smooth tangent-section Lie bracket distributes over addition in its left input. -/
@[simp]
theorem mlieBracket_add_left (X X' Y : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) (X + X') Y =
      SmoothTangentSection.mlieBracket (I := I) X Y +
        SmoothTangentSection.mlieBracket (I := I) X' Y := by
  ext x
  have hX :
      MDifferentiableAt I I.tangent (fun z : M ↦ (⟨z, X z⟩ : TangentBundle I M)) x :=
    X.contMDiff.mdifferentiableAt (by simp)
  have hX' :
      MDifferentiableAt I I.tangent (fun z : M ↦ (⟨z, X' z⟩ : TangentBundle I M)) x :=
    X'.contMDiff.mdifferentiableAt (by simp)
  have hAdd : ((fun z : M => X z) + (fun z : M => X' z)) =
      (fun z : M => X z + X' z) := by
    funext z
    rfl
  simpa [SmoothTangentSection.mlieBracket_apply, hAdd] using
    (VectorField.mlieBracket_add_left (I := I) (V := fun z : M => X z) (V₁ := fun z : M => X' z)
      (W := fun z : M => Y z) (x := x) hX hX')

/-- The smooth tangent-section Lie bracket distributes over addition in its right input. -/
@[simp]
theorem mlieBracket_add_right (X Y Y' : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) X (Y + Y') =
      SmoothTangentSection.mlieBracket (I := I) X Y +
        SmoothTangentSection.mlieBracket (I := I) X Y' := by
  ext x
  have hY :
      MDifferentiableAt I I.tangent (fun z : M ↦ (⟨z, Y z⟩ : TangentBundle I M)) x :=
    Y.contMDiff.mdifferentiableAt (by simp)
  have hY' :
      MDifferentiableAt I I.tangent (fun z : M ↦ (⟨z, Y' z⟩ : TangentBundle I M)) x :=
    Y'.contMDiff.mdifferentiableAt (by simp)
  have hAdd : ((fun z : M => Y z) + (fun z : M => Y' z)) =
      (fun z : M => Y z + Y' z) := by
    funext z
    rfl
  simpa [SmoothTangentSection.mlieBracket_apply, hAdd] using
    (VectorField.mlieBracket_add_right (I := I) (V := fun z : M => X z) (W := fun z : M => Y z)
      (W₁ := fun z : M => Y' z) (x := x) hY hY')

/-- Jacobi identity for the smooth tangent-section Lie bracket. -/
theorem mlieBracket_jacobi (X Y Z : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) X
          (SmoothTangentSection.mlieBracket (I := I) Y Z) +
        SmoothTangentSection.mlieBracket (I := I) Y
          (SmoothTangentSection.mlieBracket (I := I) Z X) +
          SmoothTangentSection.mlieBracket (I := I) Z
            (SmoothTangentSection.mlieBracket (I := I) X Y) = 0 := by
  classical
  -- Use the vector-field Leibniz identity plus skew-symmetry to derive cyclic Jacobi.
  have : IsManifold I (minSmoothness ℝ 3) M :=
    IsManifold.of_le (I := I) (M := M) (m := (minSmoothness ℝ 3)) (n := (∞ : WithTop ℕ∞))
      (by simp)
  let U : ∀ x : M, TangentSpace I x := fun x => X x
  let V : ∀ x : M, TangentSpace I x := fun x => Y x
  let W : ∀ x : M, TangentSpace I x := fun x => Z x
  have h_le2 : (minSmoothness ℝ 2) ≤ (∞ : WithTop ℕ∞) := by
    simp
  have hU :
      ContMDiff I I.tangent (minSmoothness ℝ 2) (fun x ↦ (U x : TangentBundle I M)) := by
    simpa [U] using X.contMDiff.of_le h_le2
  have hV :
      ContMDiff I I.tangent (minSmoothness ℝ 2) (fun x ↦ (V x : TangentBundle I M)) := by
    simpa [V] using Y.contMDiff.of_le h_le2
  have hW :
      ContMDiff I I.tangent (minSmoothness ℝ 2) (fun x ↦ (W x : TangentBundle I M)) := by
    simpa [W] using Z.contMDiff.of_le h_le2
  have hLeibniz :
      VectorField.mlieBracket I U (VectorField.mlieBracket I V W) =
        VectorField.mlieBracket I (VectorField.mlieBracket I U V) W +
          VectorField.mlieBracket I V (VectorField.mlieBracket I U W) :=
    VectorField.leibniz_identity_mlieBracket (I := I) hU hV hW
  ext x
  have hLeibniz_x := congrArg (fun f => f x) hLeibniz
  have hdiffXZ :
      VectorField.mlieBracket I V (VectorField.mlieBracket I W U) x =
        -VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x := by
    have hmdiff :
        MDifferentiableAt I I.tangent
          (fun x ↦ (VectorField.mlieBracket I U W x : TangentBundle I M)) x := by
      simpa [SmoothTangentSection.mlieBracket_apply, U, W] using
        (SmoothTangentSection.mlieBracket (I := I) X Z).contMDiff.mdifferentiableAt
    have hsmul :
        VectorField.mlieBracket I V ((-1 : ℝ) • VectorField.mlieBracket I U W) x =
          (-1 : ℝ) • VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x := by
      exact
        VectorField.mlieBracket_const_smul_right (I := I) (V := V)
          (W := VectorField.mlieBracket I U W) (c := (-1 : ℝ)) (x := x) hmdiff
    calc
      VectorField.mlieBracket I V (VectorField.mlieBracket I W U) x =
          VectorField.mlieBracket I V (-VectorField.mlieBracket I U W) x := by
            simp [VectorField.mlieBracket_swap (I := I) (V := W) (W := U)]
      _ = VectorField.mlieBracket I V ((-1 : ℝ) • VectorField.mlieBracket I U W) x := by
            simp
      _ = (-1 : ℝ) • VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x := hsmul
      _ = -VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x := by
            simp
  have hswap_outer :
      VectorField.mlieBracket I W (VectorField.mlieBracket I U V) x =
        -VectorField.mlieBracket I (VectorField.mlieBracket I U V) W x := by
    simpa using
      (VectorField.mlieBracket_swap_apply (I := I) (V := W)
        (W := VectorField.mlieBracket I U V) (x := x))
  have :
      VectorField.mlieBracket I U (VectorField.mlieBracket I V W) x +
          VectorField.mlieBracket I V (VectorField.mlieBracket I W U) x +
            VectorField.mlieBracket I W (VectorField.mlieBracket I U V) x = 0 := by
    have h1 :
        VectorField.mlieBracket I U (VectorField.mlieBracket I V W) x =
          VectorField.mlieBracket I (VectorField.mlieBracket I U V) W x +
            VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x := by
      simpa using hLeibniz_x
    calc
      VectorField.mlieBracket I U (VectorField.mlieBracket I V W) x +
            VectorField.mlieBracket I V (VectorField.mlieBracket I W U) x +
              VectorField.mlieBracket I W (VectorField.mlieBracket I U V) x =
          (VectorField.mlieBracket I (VectorField.mlieBracket I U V) W x +
              VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x) +
            (-VectorField.mlieBracket I V (VectorField.mlieBracket I U W) x) +
              (-VectorField.mlieBracket I (VectorField.mlieBracket I U V) W x) := by
            simp [h1, hdiffXZ, hswap_outer, add_comm, add_left_comm]
      _ = 0 := by
            abel
  simpa [SmoothTangentSection.mlieBracket_apply, U, V, W] using this

/-- Left-nested cyclic Jacobi identity for the smooth tangent-section Lie bracket. -/
theorem mlieBracket_jacobi_left_nested (X Y Z : Γ∞) :
    SmoothTangentSection.mlieBracket (I := I) (SmoothTangentSection.mlieBracket (I := I) X Y) Z +
        SmoothTangentSection.mlieBracket (I := I)
          (SmoothTangentSection.mlieBracket (I := I) Y Z) X +
          SmoothTangentSection.mlieBracket (I := I)
            (SmoothTangentSection.mlieBracket (I := I) Z X) Y = 0 := by
  have h := SmoothTangentSection.mlieBracket_jacobi (I := I) (X := X) (Y := Y) (Z := Z)
  have hneg :
      -(SmoothTangentSection.mlieBracket (I := I) X
            (SmoothTangentSection.mlieBracket (I := I) Y Z) +
          SmoothTangentSection.mlieBracket (I := I) Y
            (SmoothTangentSection.mlieBracket (I := I) Z X) +
            SmoothTangentSection.mlieBracket (I := I) Z
              (SmoothTangentSection.mlieBracket (I := I) X Y)) = 0 := by
    rw [h]
    simp
  have h1 :
      SmoothTangentSection.mlieBracket (I := I) (SmoothTangentSection.mlieBracket (I := I) X Y) Z =
        -SmoothTangentSection.mlieBracket (I := I) Z
          (SmoothTangentSection.mlieBracket (I := I) X Y) :=
    SmoothTangentSection.mlieBracket_swap (I := I)
      (SmoothTangentSection.mlieBracket (I := I) X Y) Z
  have h2 :
      SmoothTangentSection.mlieBracket (I := I) (SmoothTangentSection.mlieBracket (I := I) Y Z) X =
        -SmoothTangentSection.mlieBracket (I := I) X
          (SmoothTangentSection.mlieBracket (I := I) Y Z) :=
    SmoothTangentSection.mlieBracket_swap (I := I)
      (SmoothTangentSection.mlieBracket (I := I) Y Z) X
  have h3 :
      SmoothTangentSection.mlieBracket (I := I) (SmoothTangentSection.mlieBracket (I := I) Z X) Y =
        -SmoothTangentSection.mlieBracket (I := I) Y
          (SmoothTangentSection.mlieBracket (I := I) Z X) :=
    SmoothTangentSection.mlieBracket_swap (I := I)
      (SmoothTangentSection.mlieBracket (I := I) Z X) Y
  rw [h1, h2, h3]
  simpa [add_assoc, add_comm, add_left_comm] using hneg

end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
