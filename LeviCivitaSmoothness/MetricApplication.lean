/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeviCivitaSmoothness.MathlibBridge

@[expose] public section

/-! # Applying the bridge with the Riemannian structure induced by the supplied metric -/

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

local notation "TM" => fun x : M => TangentSpace I x
local notation "Γ∞" => Cₛ^∞⟮I; E, TM⟯

/-- Install the supplied metric as the scoped Riemannian structure, so the same-metric
premise of the bridge is definitionally satisfied. -/
theorem contMDiff_leviCivitaConnection_fromMetric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM) (X Y : Γ∞) :
    letI : SmoothRiemannianTangentBundle I M := ⟨g⟩
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x
        (CovariantDerivative.leviCivitaConnection I M (fun z => Y z) x (X x))) := by
  let : SmoothRiemannianTangentBundle I M := ⟨g⟩
  exact contMDiff_leviCivitaConnection_smooth_pair g (fun _ _ _ => rfl) X Y

end

end LeviCivitaSmoothness
