/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentConnectionFromMetric
public import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentUniqueness

@[expose] public section

/-!
# Levi–Civita existence theorem (tangent-connection interface)

This file proves that the connection constructed via the Koszul formula in
`LeviCivitaTangentConnectionFromMetric` is torsion-free and metric-compatible, and packages it as
an existence result.

## Main results

- `SmoothTangentSection.tangentConnectionFromMetric_isTorsionFree`
- `SmoothTangentSection.tangentConnectionFromMetric_isMetricCompatibleFromMetric`
- `SmoothTangentSection.exists_leviCivitaTangentConnectionFromMetric`
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
  [IsManifold I 1 M] [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M]
  [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]

local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "TM" => (fun x : M => TangentSpace I x)
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

omit [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
private theorem exists_smoothTangentSection_eq_at (x₀ : M) (v₀ : TM x₀) : ∃ s : Γ∞, s x₀ = v₀ := by
  classical
  let e := trivializationAt E TM x₀
  let w : E := (e (⟨x₀, v₀⟩ : TangentBundle I M)).2
  rcases exists_eq_localConst_nhds (I := I) (M := M) (E := E) (x₀ := x₀) (w := w) with ⟨s, hs⟩
  have hs0 :
      s x₀ = localConst (I := I) (M := M) (E := E) x₀ w x₀ :=
    (Filter.EventuallyEq.eq_of_nhds (f := fun x => s x)
      (g := fun x => localConst (I := I) (M := M) (E := E) x₀ w x) (by
        simpa using! hs))
  refine ⟨s, ?_⟩
  simpa [w, hs0] using (localConst_apply_self (I := I) (M := M) (E := E) (x₀ := x₀) v₀)
/-- The Koszul-constructed tangent connection is torsion-free. -/
theorem tangentConnectionFromMetric_isTorsionFree
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) :
    (tangentConnectionFromMetric (I := I) (M := M) (E := E) g).IsTorsionFree (I := I) (M := M) := by
  classical
  intro X Y x
  -- We prove equality of vectors by testing against the metric with a section `W` realizing the
  -- difference at `x`.
  let conn := tangentConnectionFromMetric (I := I) (M := M) (E := E) g
  let lhs : TM x := conn.covDeriv X Y x - conn.covDeriv Y X x
  let rhs : TM x := VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x
  set w : TM x := lhs - rhs with hw
  rcases exists_smoothTangentSection_eq_at (I := I) (M := M) (E := E) (x₀ := x) w with ⟨W, hW⟩
  have hkoszulXY :
      (koszulRHS (I := I) (M := M) (E := E) g X Y W) x =
        (2 : ℝ) * g.inner x (conn.covDeriv X Y x) (W x) := by
    simpa [conn, tangentConnectionFromMetric, covDerivFromMetric, covDerivFromMetricFun] using
      koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
        (Y := Y) (Z := W) x
  have hkoszulYX :
      (koszulRHS (I := I) (M := M) (E := E) g Y X W) x =
        (2 : ℝ) * g.inner x (conn.covDeriv Y X x) (W x) := by
    simpa [conn, tangentConnectionFromMetric, covDerivFromMetric, covDerivFromMetricFun] using
      koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := Y)
        (Y := X) (Z := W) x
  have hkoszul_diff :
      (koszulRHS (I := I) (M := M) (E := E) g X Y W) x -
          (koszulRHS (I := I) (M := M) (E := E) g Y X W) x =
        (2 : ℝ) * g.inner x rhs (W x) := by
    -- All derivation and “mixed bracket” terms cancel under swapping `X`/`Y`.
    -- The remaining bracket term doubles by skew-symmetry of the Lie bracket.
    have hsymmWX :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g W X =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g X W := by
      simpa using (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) g W X)
    have hsymmWY :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g W Y =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y W := by
      simpa using (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) g W Y)
    have hsymmXY :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y X := by
      simpa using (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) g X Y)
    -- Rewrite all symmetric inner-product terms, then simplify.
    have hbr_swap :
        VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => X z) x =
          - VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) x := by
      simpa using
        (VectorField.mlieBracket_swap_apply (I := I) (V := fun z : M => Y z) (W := fun z : M => X z)
          (x := x))
    have hred :
        (koszulRHS (I := I) (M := M) (E := E) g X Y W) x -
            (koszulRHS (I := I) (M := M) (E := E) g Y X W) x =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) X Y) W x -
            smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) Y X) W x := by
      -- After rewriting symmetric inner-product terms, the derivation and mixed-bracket terms
      -- cancel by commutativity in `ℝ`.
      simp [-TangentSection.toDerivation_apply, koszulRHS, hsymmWX, hsymmWY, hsymmXY]
      ring
    -- Reduce to the bracket swap term.
    -- Use pointwise skew-symmetry of `VectorField.mlieBracket`.
    have :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) X Y) W x -
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) Y X) W x =
          (2 : ℝ) * g.inner x rhs (W x) := by
      -- Expand the inner products at `x` and use `hbr_swap`.
      simp [SmoothTangentSection.mlieBracket_apply, smoothTangentSectionInnerFromMetric_apply,
        rhs, hbr_swap]
      ring
    exact (by simpa [hred] using this)
  have hinner2 :
      (2 : ℝ) * g.inner x lhs (W x) =
        (2 : ℝ) * g.inner x rhs (W x) := by
    -- Convert the Koszul identities into an equality for `2 * ⟪lhs, W x⟫`.
    calc
      (2 : ℝ) * g.inner x lhs (W x) =
          (2 : ℝ) * (g.inner x (conn.covDeriv X Y x) (W x) -
            g.inner x (conn.covDeriv Y X x) (W x)) := by
            simp [lhs, map_sub, mul_sub]
      _ =
          (koszulRHS (I := I) (M := M) (E := E) g X Y W) x -
            (koszulRHS (I := I) (M := M) (E := E) g Y X W) x := by
            simp [hkoszulXY, hkoszulYX, mul_sub]
      _ = (2 : ℝ) * g.inner x rhs (W x) := hkoszul_diff
  have hinner :
      g.inner x lhs (W x) = g.inner x rhs (W x) :=
    mul_left_cancel₀ (a := (2 : ℝ))
      (b := g.inner x lhs (W x))
      (c := g.inner x rhs (W x))
      two_ne_zero hinner2
  have hww : g.inner x w w = 0 := by
    have hWw : W x = w := hW
    have hsub :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x)) ((g.inner x).map_sub lhs rhs)
    have : g.inner x w (W x) = 0 := by
      have hsub' : g.inner x w (W x) = g.inner x lhs (W x) - g.inner x rhs (W x) := by
        rw [hw]
        exact hsub
      rw [hsub', hinner, sub_self]
    simp [hWw] at this
    exact this
  have hw0 : w = 0 := by
    by_contra hw0
    have hpos : 0 < (g.inner x w) w := g.pos x w hw0
    exact (ne_of_gt hpos) hww
  -- Conclude `lhs = rhs`.
  have : lhs = rhs := by
    have : lhs - rhs = 0 := by simpa [w] using hw0
    exact sub_eq_zero.mp this
  simpa [conn, lhs, rhs, SmoothTangentConnection.IsTorsionFree] using this
/-- The Koszul-constructed tangent connection preserves the supplied smooth metric. -/
theorem tangentConnectionFromMetric_isMetricCompatibleFromMetric
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) :
    SmoothTangentConnection.IsMetricCompatibleFromMetric (I := I) (M := M) g
      (tangentConnectionFromMetric (I := I) (M := M) (E := E) g) := by
  classical
  intro X Y Z
  ext x
  let conn := tangentConnectionFromMetric (I := I) (M := M) (E := E) g
  -- Two Koszul identities.
  have hkoszulXY :
      (koszulRHS (I := I) (M := M) (E := E) g X Y Z) x =
        (2 : ℝ) * g.inner x (conn.covDeriv X Y x) (Z x) := by
    simpa [conn, tangentConnectionFromMetric, covDerivFromMetric, covDerivFromMetricFun] using
      koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
        (Y := Y) (Z := Z) x
  have hkoszulXZ :
      (koszulRHS (I := I) (M := M) (E := E) g X Z Y) x =
        (2 : ℝ) * g.inner x (conn.covDeriv X Z x) (Y x) := by
    simpa [conn, tangentConnectionFromMetric, covDerivFromMetric, covDerivFromMetricFun] using
      koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
        (Y := Z) (Z := Y) x
  have hsum :
      (koszulRHS (I := I) (M := M) (E := E) g X Y Z) x +
          (koszulRHS (I := I) (M := M) (E := E) g X Z Y) x =
        (2 : ℝ) * (TangentSection.toDerivation (I := I) (M := M) X
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z)) x := by
    have hsymmZY :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z Y =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z := by
      simpa using (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) g Z Y)
    have hsymmZX :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Z X =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Z := by
      simpa using (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) g Z X)
    have hsymmYX :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y X =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) g X Y := by
      simpa using (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) g Y X)
    have hbr_swap :
        VectorField.mlieBracket I (fun z : M => Z z) (fun z : M => Y z) x =
          - VectorField.mlieBracket I (fun z : M => Y z) (fun z : M => Z z) x := by
      simpa using
        (VectorField.mlieBracket_swap_apply (I := I) (V := fun z : M => Z z) (W := fun z : M => Y z)
          (x := x))
    have hbr_inner :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) g
            (SmoothTangentSection.mlieBracket (I := I) Z Y) X x =
          - smoothTangentSectionInnerFromMetric (I := I) (M := M) g
              (SmoothTangentSection.mlieBracket (I := I) Y Z) X x := by
      -- Convert to pointwise `g.inner` and use `hbr_swap`.
      simp [SmoothTangentSection.mlieBracket_apply, smoothTangentSectionInnerFromMetric_apply,
        hbr_swap]
    -- Expand and cancel.
    simp [-TangentSection.toDerivation_apply, koszulRHS, hsymmZY, hsymmZX, hsymmYX,
      hbr_inner]
    ring
  have hinner2 :
      (2 : ℝ) *
          (TangentSection.toDerivation (I := I) (M := M) X
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z)) x =
        (2 : ℝ) *
          (g.inner x (conn.covDeriv X Y x) (Z x) + g.inner x (Y x) (conn.covDeriv X Z x)) := by
    have hsymm :
        g.inner x (conn.covDeriv X Z x) (Y x) = g.inner x (Y x) (conn.covDeriv X Z x) := by
      simpa using (g.symm x (conn.covDeriv X Z x) (Y x))
    calc
      (2 : ℝ) *
          (TangentSection.toDerivation (I := I) (M := M) X
            (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z)) x =
          (koszulRHS (I := I) (M := M) (E := E) g X Y Z) x +
            (koszulRHS (I := I) (M := M) (E := E) g X Z Y) x := by
              simp [hsum]
      _ =
          (2 : ℝ) * g.inner x (conn.covDeriv X Y x) (Z x) +
            (2 : ℝ) * g.inner x (conn.covDeriv X Z x) (Y x) := by
              simp [hkoszulXY, hkoszulXZ]
      _ =
          (2 : ℝ) * (g.inner x (conn.covDeriv X Y x) (Z x) +
            g.inner x (Y x) (conn.covDeriv X Z x)) := by
              -- rewrite the second term using symmetry and factor out `2`
              simp [hsymm, mul_add]
  -- Cancel the nonzero factor `2`.
  have :
      (TangentSection.toDerivation (I := I) (M := M) X
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z)) x =
        g.inner x (conn.covDeriv X Y x) (Z x) + g.inner x (Y x) (conn.covDeriv X Z x) :=
    mul_left_cancel₀ (a := (2 : ℝ))
      (b := (TangentSection.toDerivation (I := I) (M := M) X
          (smoothTangentSectionInnerFromMetric (I := I) (M := M) g Y Z)) x)
      (c := g.inner x (conn.covDeriv X Y x) (Z x) + g.inner x (Y x) (conn.covDeriv X Z x))
      two_ne_zero (by simpa [mul_assoc] using hinner2)
  -- Rewrite in terms of `smoothTangentSectionInnerFromMetric`.
  simpa [SmoothTangentConnection.IsMetricCompatibleFromMetric,
    smoothTangentSectionInnerFromMetric_apply, conn] using this
/-- Existence: the Koszul-constructed tangent connection is torsion-free and metric-compatible. -/
theorem exists_leviCivitaTangentConnectionFromMetric
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) :
    ∃ conn : SmoothTangentConnection (I := I) (M := M) (E := E),
      conn.IsTorsionFree (I := I) (M := M) ∧
        SmoothTangentConnection.IsMetricCompatibleFromMetric (I := I) (M := M) g conn := by
  refine ⟨tangentConnectionFromMetric (I := I) (M := M) (E := E) g, ?_, ?_⟩
  · simpa using tangentConnectionFromMetric_isTorsionFree (I := I) (M := M) (E := E) g
  · simpa using
      tangentConnectionFromMetric_isMetricCompatibleFromMetric (I := I) (M := M) (E := E) g
end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
