import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

import MathlibExtensions.Geometry.Manifold.VectorBundle.RiemannianTangentInnerCInfinity
import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentConnection

/-!
# Levi–Civita uniqueness for `SmoothTangentConnection` (Koszul)

This file ports the Koszul/uniqueness argument to the tangent-section input connection interface
`SmoothTangentConnection` (see `TangentConnection.lean`).

The main result is: torsion-free + metric-compatibility uniquely determine the covariant
derivative.
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

namespace SmoothTangentConnection

section Koszul

variable
  (g : Bundle.ContMDiffRiemannianMetric I n∞ E (fun x : M => TangentSpace I x))
  (conn : SmoothTangentConnection (I := I) (M := M) (E := E))

local notation "⟪" s ", " t "⟫" =>
  smoothTangentSectionInnerFromMetric (I := I) (M := M) g s t

/-- Metric compatibility for a `SmoothTangentConnection` on `TM`, phrased using the metric data `g`
directly (avoiding fiberwise `InnerProductSpace` typeclass diamonds). -/
def IsMetricCompatibleFromMetric : Prop :=
  ∀ (X Y Z : Γ∞),
    (TangentSection.toDerivation (I := I) (M := M) X) ⟪Y, Z⟫ =
      ⟪conn.covDeriv X Y, Z⟫ + ⟪Y, conn.covDeriv X Z⟫

/-- Torsion-free predicate for a tangent-bundle connection, expressed pointwise using the manifold
Lie bracket of smooth vector fields. -/
def IsTorsionFree : Prop :=
  ∀ (X Y : Γ∞) (x : M),
    conn.covDeriv X Y x - conn.covDeriv Y X x =
      VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x

private theorem covDeriv_swap_of_isTorsionFree
    (hT : conn.IsTorsionFree (I := I) (M := M)) (X Y : Γ∞) (x : M) :
    conn.covDeriv Y X x =
      conn.covDeriv X Y x -
        VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x := by
  have h := hT X Y x
  -- `h : A - B = C` with `A := ∇_X Y` and `B := ∇_Y X`. Rearrange to `B = A - C`.
  have h' :
      conn.covDeriv X Y x =
        VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x + conn.covDeriv Y X x :=
    (sub_eq_iff_eq_add).1 h
  refine (eq_sub_iff_add_eq).2 ?_
  simpa [add_assoc, add_comm, add_left_comm] using h'.symm

/-- Koszul formula (pointwise), for a torsion-free, metric-compatible tangent connection. -/
theorem koszul_formula_pointwise
    (hT : conn.IsTorsionFree (I := I) (M := M))
    (hM : IsMetricCompatibleFromMetric (I := I) (M := M) g conn)
    (X Y Z : Γ∞) (x : M) :
    2 * (g.inner x (conn.covDeriv X Y x) (Z x)) =
      (TangentSection.toDerivation (I := I) (M := M) X) ⟪Y, Z⟫ x +
          (TangentSection.toDerivation (I := I) (M := M) Y) ⟪Z, X⟫ x -
        (TangentSection.toDerivation (I := I) (M := M) Z) ⟪X, Y⟫ x +
        g.inner x (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x) (Z x) -
          g.inner x (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Z z) x) (Y x) -
          g.inner x (VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x) (X x) := by
  have hXYZ :
      (TangentSection.toDerivation (I := I) (M := M) X) ⟪Y, Z⟫ x =
        g.inner x (conn.covDeriv X Y x) (Z x) + g.inner x (Y x) (conn.covDeriv X Z x) := by
    simpa [IsMetricCompatibleFromMetric, smoothTangentSectionInnerFromMetric_apply] using
      congrArg (fun f : C∞ => f x) (hM X Y Z)
  have hYZX :
      (TangentSection.toDerivation (I := I) (M := M) Y) ⟪Z, X⟫ x =
        g.inner x (conn.covDeriv Y Z x) (X x) + g.inner x (Z x) (conn.covDeriv Y X x) := by
    simpa [IsMetricCompatibleFromMetric, smoothTangentSectionInnerFromMetric_apply] using
      congrArg (fun f : C∞ => f x) (hM Y Z X)
  have hZXY :
      (TangentSection.toDerivation (I := I) (M := M) Z) ⟪X, Y⟫ x =
        g.inner x (conn.covDeriv Z X x) (Y x) + g.inner x (X x) (conn.covDeriv Z Y x) := by
    simpa [IsMetricCompatibleFromMetric, smoothTangentSectionInnerFromMetric_apply] using
      congrArg (fun f : C∞ => f x) (hM Z X Y)

  have hswapXY := covDeriv_swap_of_isTorsionFree (I := I) (M := M) (conn := conn) hT X Y x
  have hswapXZ := covDeriv_swap_of_isTorsionFree (I := I) (M := M) (conn := conn) hT X Z x
  have hswapYZ := covDeriv_swap_of_isTorsionFree (I := I) (M := M) (conn := conn) hT Y Z x

  symm
  have hsymmYXZ : g.inner x (Y x) (conn.covDeriv X Z x) = g.inner x (conn.covDeriv X Z x) (Y x) := by
    simpa using (g.symm x (Y x) (conn.covDeriv X Z x))
  have hsymmYZX : g.inner x (conn.covDeriv Y Z x) (X x) = g.inner x (X x) (conn.covDeriv Y Z x) := by
    simpa using (g.symm x (conn.covDeriv Y Z x) (X x))
  have hsymmZXY : g.inner x (conn.covDeriv Z X x) (Y x) = g.inner x (Y x) (conn.covDeriv Z X x) := by
    simpa using (g.symm x (conn.covDeriv Z X x) (Y x))
  have hsymmZXY' : g.inner x (Z x) (conn.covDeriv X Y x) = g.inner x (conn.covDeriv X Y x) (Z x) := by
    simpa using (g.symm x (Z x) (conn.covDeriv X Y x))
  have hsymmZXbrXY :
      g.inner x (Z x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x) =
        g.inner x (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x) (Z x) := by
    simpa using (g.symm x (Z x) (VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x))
  have hsymmXbrYZ :
      g.inner x (X x) (VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x) =
        g.inner x (VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x) (X x) := by
    simpa using (g.symm x (X x) (VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x))

  simp [hXYZ, hYZX, hZXY, sub_eq_add_neg, hsymmYXZ, hsymmYZX, hsymmZXY',
    hswapXY, hswapXZ, hswapYZ, hsymmZXbrXY, hsymmXbrYZ]
  ring_nf

/-- Uniqueness: torsion-free and metric-compatible tangent connections agree. -/
theorem covDeriv_eq_of_isTorsionFree_of_isMetricCompatibleFromMetric
    (conn₁ conn₂ : SmoothTangentConnection (I := I) (M := M) (E := E))
    (hT₁ : IsTorsionFree (I := I) (M := M) (conn := conn₁))
    (hM₁ : IsMetricCompatibleFromMetric (I := I) (M := M) (g := g) (conn := conn₁))
    (hT₂ : IsTorsionFree (I := I) (M := M) (conn := conn₂))
    (hM₂ : IsMetricCompatibleFromMetric (I := I) (M := M) (g := g) (conn := conn₂))
    (X Y : Γ∞) :
    conn₁.covDeriv X Y = conn₂.covDeriv X Y := by
  ext x
  let U : Γ∞ := conn₁.covDeriv X Y
  let V : Γ∞ := conn₂.covDeriv X Y
  let W : Γ∞ := U - V
  have h1 :=
    koszul_formula_pointwise (I := I) (M := M) (g := g) (conn := conn₁) hT₁ hM₁ X Y W x
  have h2 :=
    koszul_formula_pointwise (I := I) (M := M) (g := g) (conn := conn₂) hT₂ hM₂ X Y W x
  have hEq2 :
      (2 : ℝ) * g.inner x (U x) (W x) = (2 : ℝ) * g.inner x (V x) (W x) := by
    exact h1.trans h2.symm
  have hEq : g.inner x (U x) (W x) = g.inner x (V x) (W x) :=
    mul_left_cancel₀ (a := (2 : ℝ)) (b := g.inner x (U x) (W x)) (c := g.inner x (V x) (W x))
      two_ne_zero hEq2

  have hEq' : g.inner x (W x) (U x) = g.inner x (W x) (V x) := by
    simpa [g.symm x (U x) (W x), g.symm x (V x) (W x)] using hEq

  have hWW : g.inner x (W x) (W x) = 0 := by
    have hsub :
        g.inner x (W x) (U x - V x) = g.inner x (W x) (U x) - g.inner x (W x) (V x) :=
      (g.inner x (W x)).map_sub (U x) (V x)
    have hRHS0 : g.inner x (W x) (U x) - g.inner x (W x) (V x) = 0 := sub_eq_zero.2 hEq'
    have hLHS0 : g.inner x (W x) (U x - V x) = 0 := by
      calc
        g.inner x (W x) (U x - V x) = g.inner x (W x) (U x) - g.inner x (W x) (V x) := hsub
        _ = 0 := hRHS0
    simpa [W, U, V] using hLHS0

  have hW : W x = 0 := by
    by_contra hne
    have hpos := g.pos x (W x) hne
    have hne0 : g.inner x (W x) (W x) ≠ 0 := ne_of_gt hpos
    exact hne0 hWW

  have hUV : U x - V x = 0 := by simpa [W] using hW
  exact sub_eq_zero.1 hUV

end Koszul

end SmoothTangentConnection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
