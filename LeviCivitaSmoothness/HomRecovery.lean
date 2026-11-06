import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import LeviCivitaSmoothness.MetricApplication

/-!
# Global smoothness of the Levi-Civita covariant derivative

Recover Hom-bundle smoothness from smooth evaluation on global smooth tangent sections.
Local chart-constant test sections can be globalized near the point under consideration;
finite-dimensional operator smoothness then recovers the Hom section. The result concerns
global smooth inputs and makes no finite-regularity or arbitrary-set regularity assertion.
-/

open scoped Bundle Manifold ContDiff Topology
open Bundle

namespace LeviCivitaSmoothness

open MathlibExtensions.Geometry.Manifold.VectorBundle

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [T2Space M]

local notation "TM" => fun x : M => TangentSpace I x
local notation "Γ∞" => Cₛ^∞⟮I; E, TM⟯

/-- A tangent endomorphism section is smooth if evaluation on every global smooth tangent
section is smooth. Each chart-constant test vector needs only its own neighborhood. -/
theorem contMDiff_hom_of_smooth_apply
    (φ : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (hφ : ∀ X : Γ∞, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (φ x (X x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (φ x)) := by
  intro x₀
  refine (contMDiffAt_hom_bundle
    (fun x => TotalSpace.mk' (E →L[ℝ] E) x (φ x))).mpr ⟨contMDiffAt_id, ?_⟩
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  apply contDiffWithinAt_clm_apply.mpr
  intro w
  have hCoordinate : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun x => ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (φ x) w) x₀ := by
    let e := trivializationAt E TM x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x₀
    obtain ⟨s, hs⟩ :=
      SmoothTangentSection.exists_eq_localConst_nhds (I := I) (M := M) x₀ w
    have hSmooth : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun x => (e (⟨x, φ x (s x)⟩ : TangentBundle I M)).2) x₀ :=
      (Bundle.contMDiffAt_section x₀).mp (hφ s x₀)
    apply hSmooth.congr_of_eventuallyEq
    filter_upwards [hs, e.open_baseSet.mem_nhds hx₀] with x hsx hx
    change e.continuousLinearMapAt ℝ x (φ x (e.symmL ℝ x w)) =
      (e (⟨x, φ x (s x)⟩ : TangentBundle I M)).2
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hx]
    have hSymm : e.symmL ℝ x w = s x := by
      apply (e.continuousLinearEquivAt ℝ x hx).injective
      change (e (⟨x, e.symmL ℝ x w⟩ : TangentBundle I M)).2 =
        (e (⟨x, s x⟩ : TangentBundle I M)).2
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hx,
        e.continuousLinearMapAt_symmL hx, hsx]
      exact (SmoothTangentSection.localConst_trivializationAt_snd
        (I := I) (M := M) (x₀ := x₀) (w := w) hx).symm
    rw [hSymm]
  simpa only [Function.comp_def] using
    (contMDiffAt_iff_source.mp hCoordinate).contDiffWithinAt

section LeviCivita

variable [IsManifold I 2 M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

/-- The chosen Levi-Civita covariant derivative is globally smooth when the supplied smooth
metric agrees with the Riemannian bundle structure. -/
theorem contMDiffCovariantDerivative_leviCivitaConnection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (hinner : ∀ (x : M) (u v : TangentSpace I x), inner ℝ u v = g.inner x u v) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.leviCivitaConnection I M) ∞ := by
  refine ⟨⟨?_⟩⟩
  intro Y hY
  let s : Γ∞ := ⟨Y, by simpa [contMDiffOn_univ] using hY⟩
  have hs : (fun z => s z) = Y := rfl
  have hHom := contMDiff_hom_of_smooth_apply
    (fun x => CovariantDerivative.leviCivitaConnection I M Y x)
    (fun X => by
      have hPair := contMDiff_leviCivitaConnection_smooth_pair g hinner X s
      rw [hs] at hPair
      exact hPair)
  exact hHom.contMDiffOn

end LeviCivita

/-- Installing the smooth metric supplies a globally smooth Levi-Civita connection in
Mathlib's full Hom-valued regularity class. -/
theorem contMDiffCovariantDerivative_leviCivitaConnection_fromMetric
    [IsManifold I 2 M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E TM) :
    letI : SmoothRiemannianTangentBundle I M := ⟨g⟩
    CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.leviCivitaConnection I M) ∞ := by
  let : SmoothRiemannianTangentBundle I M := ⟨g⟩
  exact contMDiffCovariantDerivative_leviCivitaConnection g (fun _ _ _ => rfl)

end

end LeviCivitaSmoothness
