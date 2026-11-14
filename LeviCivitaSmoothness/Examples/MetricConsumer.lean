/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeviCivitaSmoothness

@[expose] public section

/-!
# Using the global Levi-Civita smoothness API

These consumers install a supplied genuine smooth metric and use Mathlib's chosen
covariant derivative. The inputs are globally smooth sections. The examples are opt-in
and do not add imports to the library roots.
-/

open scoped Bundle Manifold ContDiff
open Bundle

namespace LeviCivitaSmoothness.Examples

open MathlibExtensions.Geometry.Manifold.VectorBundle

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 2) M]
  [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]

local notation "TM" => fun x : M => TangentSpace I x
local notation "Γ∞" => Cₛ^∞⟮I; E, TM⟯

/-- A metric and two globally smooth tangent sections give a smooth covariant derivative. -/
theorem smooth_pair_from_metric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM) (X Y : Γ∞) :
    letI : SmoothRiemannianTangentBundle I M := ⟨g⟩
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x
        (CovariantDerivative.leviCivitaConnection I M (fun z => Y z) x (X x))) := by
  exact contMDiff_leviCivitaConnection_fromMetric g X Y

/-- The connection class applies to an unbundled globally smooth input and returns a smooth
Hom-valued section, before choosing any direction field. -/
theorem hom_section_from_metric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (Y : (x : M) → TM x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => TotalSpace.mk' E x (Y x))) :
    letI : SmoothRiemannianTangentBundle I M := ⟨g⟩
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x
        (CovariantDerivative.leviCivitaConnection I M Y x)) := by
  let : SmoothRiemannianTangentBundle I M := ⟨g⟩
  have hcov := contMDiffCovariantDerivative_leviCivitaConnection_fromMetric g
  have hHom := hcov.contMDiff.contMDiff (σ := Y) (by simpa using hY.contMDiffOn)
  simpa only [contMDiffOn_univ] using hHom

omit [IsManifold I 2 M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
/-- Any prescribed tangent direction can be tested by a global smooth section. -/
theorem global_test_section_exists (x : M) (v : TM x) :
    ∃ X : Γ∞, X x = v := by
  exact SmoothTangentSection.exists_eq_at x v

end

end LeviCivitaSmoothness.Examples
