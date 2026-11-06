/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import LeviCivitaSmoothness.KoszulTransfer

/-!
# Identifying Mathlib's Levi-Civita derivative on global smooth pairs

The explicit `hinner` premise guarantees that the metric data used by the smooth construction
is precisely the metric underlying Mathlib's scoped Riemannian bundle instance.
-/

open scoped Bundle Manifold ContDiff
open Bundle

namespace LeviCivitaSmoothness

open MathlibExtensions.Geometry.Manifold.VectorBundle

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 2) M]
  [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

local notation "TM" => fun x : M => TangentSpace I x
local notation "Γ∞" => Cₛ^∞⟮I; E, TM⟯

/-- Mathlib's chosen Levi-Civita derivative agrees with the smooth Koszul construction on
global smooth input sections, when both use the same metric. -/
theorem leviCivitaConnection_eq_covDerivFromMetric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (hinner : ∀ (x : M) (u v : TangentSpace I x), inner ℝ u v = g.inner x u v)
    (X Y : Γ∞) :
    (fun x => CovariantDerivative.leviCivitaConnection I M (fun z => Y z) x (X x)) =
      fun x => SmoothTangentSection.covDerivFromMetric g X Y x := by
  apply eq_covDerivFromMetric_of_koszul g X Y
  intro Z x
  have h := CovariantDerivative.leviCivitaConnection_apply_inner I
    (X := fun z => X z) (Y := fun z => Y z) (Z := fun z => Z z) (x := x)
    (X.contMDiff.mdifferentiableAt (by simp))
    (Y.contMDiff.mdifferentiableAt (by simp))
    (Z.contMDiff.mdifferentiableAt (by simp))
  simp_rw [hinner] at h
  have hswapYX := VectorField.mlieBracket_swap_apply (I := I) (V := fun z => Y z)
    (W := fun z => X z) (x := x)
  have hswapZY := VectorField.mlieBracket_swap_apply (I := I) (V := fun z => Z z)
    (W := fun z => Y z) (x := x)
  simp only [hswapYX, hswapZY, map_neg] at h
  change
    mvfderiv I (fun z => g.inner z (Y z) (Z z)) x (X x) +
        mvfderiv I (fun z => g.inner z (Z z) (X z)) x (Y x) -
      mvfderiv I (fun z => g.inner z (X z) (Y z)) x (Z x) +
        g.inner x (VectorField.mlieBracket I (fun z => X z) (fun z => Y z) x) (Z x) -
      g.inner x (VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x) (Y x) -
      g.inner x (VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x) (X x) =
        2 * g.inner x
          (CovariantDerivative.leviCivitaConnection I M (fun z => Y z) x (X x)) (Z x)
  rw [g.symm x (Y x) (VectorField.mlieBracket I (fun z => X z) (fun z => Z z) x),
    g.symm x (Z x) (VectorField.mlieBracket I (fun z => X z) (fun z => Y z) x),
    g.symm x (X x) (VectorField.mlieBracket I (fun z => Y z) (fun z => Z z) x)] at h
  linear_combination -2 * h

/-- Mathlib's chosen Levi-Civita derivative is smooth when evaluated on global smooth pairs.
Recovering Hom-valued regularity is needed for `ContMDiffCovariantDerivative`.
Regularity for inputs only smooth on a set is a further local theorem. -/
theorem contMDiff_leviCivitaConnection_smooth_pair
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (hinner : ∀ (x : M) (u v : TangentSpace I x), inner ℝ u v = g.inner x u v)
    (X Y : Γ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x
        (CovariantDerivative.leviCivitaConnection I M (fun z => Y z) x (X x))) := by
  have h := leviCivitaConnection_eq_covDerivFromMetric g hinner X Y
  simp_rw [congrFun h]
  exact (SmoothTangentSection.covDerivFromMetric g X Y).contMDiff

end

end LeviCivitaSmoothness
