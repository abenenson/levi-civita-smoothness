/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentConnectionFromMetric

@[expose] public section

/-!
# Transferring the smooth Koszul construction to another representative

The target operation may take arbitrary sections in its ambient API. This file only compares
its values on global smooth inputs. No regularity of arbitrary or locally regular inputs is
assumed or concluded.
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
  [IsManifold I 1 M] [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 2) M]
  [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]

local notation "TM" => fun x : M => TangentSpace I x
local notation "Γ∞" => Cₛ^∞⟮I; E, TM⟯

omit [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
/-- Testing against global smooth sections determines a tangent vector at a point.
The test section is obtained from a local bump construction; no sigma compactness is needed. -/
theorem eq_of_inner_smooth_sections
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM) (x : M)
    (u v : TangentSpace I x)
    (h : ∀ Z : Γ∞, g.inner x u (Z x) = g.inner x v (Z x)) : u = v := by
  obtain ⟨Z, hZ⟩ := SmoothTangentSection.exists_eq_at (I := I) (M := M) x (u - v)
  have huv := h Z
  rw [hZ] at huv
  have hzero : g.inner x (u - v) (u - v) = 0 := by
    calc
      g.inner x (u - v) (u - v) = g.inner x u (u - v) - g.inner x v (u - v) :=
        congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (u - v))
          ((g.inner x).map_sub u v)
      _ = 0 := sub_eq_zero.mpr huv
  by_contra hne
  exact (ne_of_gt (g.pos x (u - v) (sub_ne_zero.mpr hne))) hzero

/-- A section satisfying the smooth Koszul identities agrees with the smooth construction.
This is an equality of values, so it does not identify unconstrained junk on nonsmooth inputs. -/
theorem eq_covDerivFromMetric_of_koszul
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (X Y : Γ∞) (D : (x : M) → TangentSpace I x)
    (hD : ∀ (Z : Γ∞) (x : M),
      SmoothTangentSection.koszulRHS g X Y Z x = 2 * g.inner x (D x) (Z x)) :
    D = fun x => SmoothTangentSection.covDerivFromMetric g X Y x := by
  funext x
  apply eq_of_inner_smooth_sections g x
  intro Z
  have h := (hD Z x).symm.trans
    (SmoothTangentSection.koszulRHS_eq_two_inner_covDerivFromMetricFun g X Y Z x)
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h

/-- Smoothness transfers along the Koszul identification on smooth input sections. -/
theorem contMDiff_of_koszul
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (X Y : Γ∞) (D : (x : M) → TangentSpace I x)
    (hD : ∀ (Z : Γ∞) (x : M),
      SmoothTangentSection.koszulRHS g X Y Z x = 2 * g.inner x (D x) (Z x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => TotalSpace.mk' E x (D x)) := by
  rw [eq_covDerivFromMetric_of_koszul g X Y D hD]
  exact (SmoothTangentSection.covDerivFromMetric g X Y).contMDiff

end

end LeviCivitaSmoothness
