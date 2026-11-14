/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs

import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentExistence
import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentExistenceLocal
import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentConnection

/-!
# Levi–Civita construction on `TM` from a smooth metric (global `covDeriv`)

This file defines the (candidate) covariant derivative `∇_X Y` from a smooth Riemannian metric `g`
using the Koszul formula.

We first define `covDerivFromMetricFun` pointwise (using the pointwise Riesz representation), and
prove its pointwise Koszul identity.

The global smoothness proof and packaging as a `SmoothTangentConnection` are built on top of the
local smooth solver in `LeviCivitaTangentExistenceLocal`.
-/

open scoped Topology Bundle Manifold ContDiff

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

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

/-- Pointwise definition of the Levi–Civita covariant derivative (as a section-valued function),
using the pointwise Riesz representer of `koszulRHSLinear` and scaling by `1/2`. -/
noncomputable def covDerivFromMetricFun
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) (x : M) : TM x :=
  (1 / 2 : ℝ) •
    Classical.choose
      (exists_koszulRHSInnerAt (I := I) (M := M) (E := E) (g := g) (X := X) (Y := Y) x)

/-- The Koszul linear functional is twice the metric pairing with the constructed derivative. -/
theorem koszulRHSLinear_eq_two_inner_covDerivFromMetricFun
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z : Γ∞) (x : M) :
    (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x =
      (2 : ℝ) * g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (Z x) := by
  classical
  -- Unpack the pointwise representer `w`.
  set w :=
    Classical.choose
      (exists_koszulRHSInnerAt (I := I) (M := M) (E := E) (g := g) (X := X) (Y := Y) x) with hw
  have hwZ :
      (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x = (g.inner x w) (Z x) := by
    simpa [w] using
      (Classical.choose_spec
        (exists_koszulRHSInnerAt (I := I) (M := M) (E := E) (g := g) (X := X) (Y := Y) x) Z)
  -- Scale by `1/2` and clear the factor `2`.
  have hsmul :
      g.inner x ((1 / 2 : ℝ) • w) (Z x) = (1 / 2 : ℝ) * (g.inner x w) (Z x) := by
    -- `g.inner x` is linear in the first slot.
    change g.inner x ((1 / 2 : ℝ) • w) (Z x) = (1 / 2 : ℝ) • (g.inner x w) (Z x)
    exact congrArg (fun L : TM x →L[ℝ] ℝ => L (Z x)) ((g.inner x).map_smul (1 / 2 : ℝ) w)
  -- Finish.
  calc
    (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x = g.inner x w (Z x) := hwZ
    _ = (2 : ℝ) * g.inner x ((1 / 2 : ℝ) • w) (Z x) := by
      rw [hsmul]
      ring
    _ = (2 : ℝ) * g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (Z x) := by
      simp [covDerivFromMetricFun, w, div_eq_mul_inv]

/-- Global smooth section `∇_X Y`, obtained from the pointwise definition `covDerivFromMetricFun`
and the local smooth solver. -/
noncomputable def covDerivFromMetric
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) : Γ∞ :=
  ⟨covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y, by
    -- Let `F` be the total-space map of the section.
    let F : M → Bundle.TotalSpace E TM :=
      fun x => TotalSpace.mk' E x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x)
    -- Prove smoothness by local identification with the locally constructed smooth solution.
    have hloc :
        ∀ x₀ : M,
          ∃ u : Set M, IsOpen u ∧ x₀ ∈ u ∧
            ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ F u := by
      intro x₀
      -- Choose the local smooth solution `W` near `x₀` (Koszul system solved smoothly).
      rcases
          SmoothTangentSection.exists_koszulRHSInner_nhds (I := I) (M := M) (E := E) (g := g)
            (X := X) (Y := Y) x₀ with
        ⟨W, hW⟩
      -- Choose the localConst finBasis frame `s i` near `x₀`, used to identify fibers.
      rcases
          SmoothTangentSection.exists_localConst_finBasis_nhds (I := I) (M := M) (E := E) x₀ with
        ⟨s, hs, -⟩
      let e := trivializationAt E TM x₀
      have he : e.baseSet ∈ 𝓝 x₀ := by
        have hx₀ : x₀ ∈ e.baseSet := by
          change x₀ ∈ (trivializationAt E TM x₀).baseSet
          simp [TangentBundle.trivializationAt_baseSet]
        exact e.open_baseSet.mem_nhds hx₀
      have hxU : ∀ᶠ x in 𝓝 x₀, x ∈ e.baseSet := he
      have hs_all :
          ∀ᶠ x in 𝓝 x₀, ∀ i : Fin (Module.finrank ℝ E),
            s i x = localConst (I := I) (M := M) (E := E) x₀ ((Module.finBasis ℝ E) i) x := by
        simpa using Filter.eventually_all.2 hs
      have hW_all :
          ∀ᶠ x in 𝓝 x₀, ∀ i : Fin (Module.finrank ℝ E),
            (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
              (2 : ℝ) *
                smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
        -- Apply the local Koszul identity to the finite family `s i`.
        have : ∀ i : Fin (Module.finrank ℝ E),
            ∀ᶠ x in 𝓝 x₀,
              (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
                (2 : ℝ) *
                  smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x :=
          fun i => hW (s i)
        simpa using Filter.eventually_all.2 this
      -- Show `covDerivFromMetricFun = W` near `x₀`, using the frame `s i`.
      have hEq :
          ∀ᶠ x in 𝓝 x₀,
            covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x = W x := by
        filter_upwards [hxU, hs_all, hW_all] with x hxU hsx hWx
        -- Compare inner products against the frame at `x`.
        have hinner :
            ∀ i : Fin (Module.finrank ℝ E),
              g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x) =
                g.inner x (W x) (s i x) := by
          intro i
          have h1 :
              (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
                (2 : ℝ) *
                  g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x) := by
            simpa [smoothTangentSectionInnerFromMetric_apply] using
              (koszulRHSLinear_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E)
                (g := g) (X := X) (Y := Y) (Z := s i) x)
          have h2 :
              (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
                (2 : ℝ) * g.inner x (W x) (s i x) := by
            simpa [smoothTangentSectionInnerFromMetric_apply] using hWx i
          have hEq2 :
              (2 : ℝ) *
                  g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x) =
                (2 : ℝ) * g.inner x (W x) (s i x) := by
            exact h1.symm.trans h2
          exact
            mul_left_cancel₀ (a := (2 : ℝ))
              (b := g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x))
              (c := g.inner x (W x) (s i x)) two_ne_zero hEq2
        -- Let `w = covDerivFromMetricFun - W`. Show `w = 0` using the explicit `localConst` frame.
        set w : TM x :=
          covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x - W x with hw
        have hw_inner : ∀ i : Fin (Module.finrank ℝ E), g.inner x w (s i x) = 0 := by
          intro i
          have hsub :
              g.inner x w (s i x) =
                g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x) -
                  g.inner x (W x) (s i x) := by
            -- linearity in the first slot
            change
              g.inner x
                  (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x - W x) (s i x) =
                g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x) -
                  g.inner x (W x) (s i x)
            exact congrArg (fun L : TM x →L[ℝ] ℝ => L (s i x))
              ((g.inner x).map_sub
                (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (W x))
          have : g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (s i x) =
                g.inner x (W x) (s i x) := hinner i
          simp [hsub, this]
        -- Express `w` in the `localConst` finBasis frame, then compute `⟪w,w⟫ = 0`.
        let φx := (e.continuousLinearEquivAt (R := ℝ) x hxU)
        let bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
        let coeff : Fin (Module.finrank ℝ E) → ℝ := fun i => (bE.coord i) (φx w)
        have hw_decomp :
            w =
              ∑ i : Fin (Module.finrank ℝ E),
                (coeff i) • localConst (I := I) (M := M) (E := E) x₀ (bE i) x := by
          -- Apply `φx` and use basis expansion in `E`.
          apply φx.injective
          have hφ_localConst (i : Fin (Module.finrank ℝ E)) :
              φx (localConst (I := I) (M := M) (E := E) x₀ (bE i) x) = bE i := by
            -- inside the base set, the trivialization coordinate is constant `bE i`
            simpa [φx, e] using
              (localConst_trivializationAt_snd (I := I) (M := M) (E := E) (x₀ := x₀) (w := bE i)
                (x := x) hxU)
          have hbasis :
              φx w = ∑ i : Fin (Module.finrank ℝ E), (coeff i) • (bE i) := by
            have hbasis' := (Module.Basis.sum_repr bE (φx w)).symm
            calc
              φx w = ∑ i : Fin (Module.finrank ℝ E), (bE.repr (φx w)) i • bE i := hbasis'
              _ = ∑ i : Fin (Module.finrank ℝ E), (coeff i) • bE i := by
                simp [coeff, Module.Basis.coord_apply]
          have hsum :
              φx
                  (∑ i : Fin (Module.finrank ℝ E),
                    (coeff i) • localConst (I := I) (M := M) (E := E) x₀ (bE i) x) =
                ∑ i : Fin (Module.finrank ℝ E), (coeff i) • (bE i) := by
            simp [hφ_localConst, map_sum, map_smul]
          simpa [hsum] using hbasis
        have hw_decomp' :
            w = ∑ i : Fin (Module.finrank ℝ E), (coeff i) • (s i x) := by
          classical
          -- Replace `localConst` by `s i` using `hsx`.
          have hsx' :
              ∀ i : Fin (Module.finrank ℝ E),
                localConst (I := I) (M := M) (E := E) x₀ (bE i) x = s i x := by
            intro i
            simpa [bE] using (hsx i).symm
          simpa [hsx'] using hw_decomp
        have hww : g.inner x w w = 0 := by
          -- Expand the second slot using linearity and `hw_inner`.
          -- First, rewrite `w` in terms of the frame `s i x`.
          calc
            g.inner x w w = g.inner x w (∑ i : Fin (Module.finrank ℝ E), (coeff i) • (s i x)) := by
              rw [hw_decomp']
            _ = ∑ i : Fin (Module.finrank ℝ E), (coeff i) * g.inner x w (s i x) := by
              simp [map_sum, map_smul, smul_eq_mul]
            _ = 0 := by
              classical
              simp [hw_inner]
        -- Conclude `w = 0` from positive-definiteness, hence `covDerivFromMetricFun = W`.
        have hw0 : w = 0 := by
          by_contra hw0
          have hpos : 0 < (g.inner x w) w := g.pos x w hw0
          exact (ne_of_gt hpos) hww
        have : covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x = W x := by
          have : covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x - W x = 0 := by
            simpa [w] using hw0
          exact sub_eq_zero.mp this
        exact this
      -- Extract an open set on which `covDerivFromMetricFun = W`.
      rcases hEq.exists_mem with ⟨V, hVnhds, hV⟩
      rcases mem_nhds_iff.1 hVnhds with ⟨u, huV, huOpen, hx₀u⟩
      refine ⟨u, huOpen, hx₀u, ?_⟩
      -- On `u`, the total-space map `F` agrees with the smooth section `W`.
      have hFu : ∀ x ∈ u, F x = TotalSpace.mk' E x (W x) := by
        intro x hx
        have : covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x = W x := hV x (huV hx)
        simp [F, this]
      -- Use congruence to inherit smoothness from `W`.
      have hWcont :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ (fun x ↦ TotalSpace.mk' E x (W x)) u := by
        exact (W.contMDiff.contMDiffOn)
      refine hWcont.congr ?_
      intro x hx
      simp [hFu x hx]
    -- Finish using locality of `ContMDiff`.
    have : ContMDiff I (I.prod 𝓘(ℝ, E)) n∞ F :=
      contMDiff_of_locally_contMDiffOn (I := I) (I' := (I.prod 𝓘(ℝ, E))) (n := n∞) (f := F) hloc
    simpa [F] using this⟩

/-! ### Packaging as a `SmoothTangentConnection` -/

/-- Pointwise Koszul identity for `covDerivFromMetricFun`, in the `koszulRHS` form. -/
theorem koszulRHS_eq_two_inner_covDerivFromMetricFun
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y Z : Γ∞) (x : M) :
    (koszulRHS (I := I) (M := M) (E := E) g X Y Z) x =
      (2 : ℝ) * g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X Y x) (Z x) := by
  simpa [koszulRHSLinear] using
    (koszulRHSLinear_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E)
      (g := g) (X := X) (Y := Y) (Z := Z) x)

omit [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
private theorem exists_smoothTangentSection_eq_at (x₀ : M) (v₀ : TM x₀) : ∃ s : Γ∞, s x₀ = v₀ := by
  classical
  let e := trivializationAt E TM x₀
  let w : E := (e (⟨x₀, v₀⟩ : TangentBundle I M)).2
  rcases exists_eq_localConst_nhds (I := I) (M := M) (E := E) (x₀ := x₀) (w := w) with ⟨s, hs⟩
  have hs' :
      s x₀ = localConst (I := I) (M := M) (E := E) x₀ w x₀ :=
    (Filter.EventuallyEq.eq_of_nhds (f := fun x => s x)
      (g := fun x => localConst (I := I) (M := M) (E := E) x₀ w x) (by
        simpa using! hs))
  refine ⟨s, ?_⟩
  simpa [w, hs'] using (localConst_apply_self (I := I) (M := M) (E := E) (x₀ := x₀) v₀)

/-- The constructed covariant derivative preserves addition of sections. -/
theorem covDerivFromMetric_add
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X s t : Γ∞) :
    covDerivFromMetric (I := I) (M := M) (E := E) g X (s + t) =
      covDerivFromMetric (I := I) (M := M) (E := E) g X s +
        covDerivFromMetric (I := I) (M := M) (E := E) g X t := by
  classical
  ext x
  let lhs : TM x := covDerivFromMetricFun (I := I) (M := M) (E := E) g X (s + t) x
  let rhs : TM x :=
    covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x +
      covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x
  set w : TM x := lhs - rhs with hw
  rcases exists_smoothTangentSection_eq_at (I := I) (M := M) (E := E) (x₀ := x) w with ⟨W, hW⟩
  have hkoszul :
      (koszulRHS (I := I) (M := M) (E := E) g X (s + t) W) x =
        (koszulRHS (I := I) (M := M) (E := E) g X s W) x +
          (koszulRHS (I := I) (M := M) (E := E) g X t W) x := by
    simpa using congrArg (fun F : C∞ => F x)
      (MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothTangentSection.koszulRHS_add_middle
        (I := I) (M := M) (E := E) (g := g) X s t W)
  have h1 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := (s + t)) (Z := W) x
  have h2 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := s) (Z := W) x
  have h3 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := t) (Z := W) x
  have hinner2 :
      (2 : ℝ) * g.inner x lhs (W x) =
        (2 : ℝ) * (g.inner x
            (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
          g.inner x
            (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x)) := by
    -- Convert the Koszul additivity into an identity of `2 * ⟪-, W x⟫`.
    calc
      (2 : ℝ) * g.inner x lhs (W x) =
          (koszulRHS (I := I) (M := M) (E := E) g X (s + t) W) x := by
            simpa [lhs] using h1.symm
      _ = (koszulRHS (I := I) (M := M) (E := E) g X s W) x +
            (koszulRHS (I := I) (M := M) (E := E) g X t W) x := hkoszul
      _ =
          (2 : ℝ) * g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
            (2 : ℝ) * g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x) := by
            simp [h2, h3]
      _ = (2 : ℝ) *
            (g.inner x
                (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
              g.inner x
                (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x)) := by
            ring
  have hinner :
      g.inner x lhs (W x) =
        g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
          g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x) :=
    mul_left_cancel₀ (a := (2 : ℝ))
      (b := g.inner x lhs (W x))
      (c := g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
        g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x))
      two_ne_zero hinner2
  have hww : g.inner x w w = 0 := by
    have hWw : W x = w := hW
    have hsub :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x)) ((g.inner x).map_sub lhs rhs)
    have hsum :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x))
        ((g.inner x).map_add
          (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x)
          (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x))
    -- Rewrite `W x` as `w` and simplify using `hinner`.
    have : g.inner x w (W x) = 0 := by
      -- `w = lhs - rhs` and `rhs` is the sum of the two terms.
      have : g.inner x w (W x) =
          g.inner x lhs (W x) - g.inner x rhs (W x) := by
        change g.inner x (lhs - rhs) (W x) = g.inner x lhs (W x) - g.inner x rhs (W x)
        exact hsub
      -- Expand `g.inner x rhs`.
      have hrhs :
          g.inner x rhs (W x) =
            g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
              g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x) := by
        change
          g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x +
                covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x) =
            g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
              g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X t x) (W x)
        exact hsum
      -- Conclude.
      simp [this, hrhs, hinner]
    rw [hWw] at this
    exact this
  have hw0 : w = 0 := by
    by_contra hw0
    have hpos : 0 < (g.inner x w) w := g.pos x w hw0
    exact (ne_of_gt hpos) hww
  have : lhs = rhs := by
    have : lhs - rhs = 0 := by simpa [w] using hw0
    exact sub_eq_zero.mp this
  simpa [lhs, rhs, covDerivFromMetric, covDerivFromMetricFun] using this

/-- The constructed covariant derivative preserves addition of tangent fields. -/
theorem covDerivFromMetric_add_vec
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y s : Γ∞) :
    covDerivFromMetric (I := I) (M := M) (E := E) g (X + Y) s =
      covDerivFromMetric (I := I) (M := M) (E := E) g X s +
        covDerivFromMetric (I := I) (M := M) (E := E) g Y s := by
  classical
  ext x
  let lhs : TM x := covDerivFromMetricFun (I := I) (M := M) (E := E) g (X + Y) s x
  let rhs : TM x :=
    covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x +
      covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x
  set w : TM x := lhs - rhs with hw
  rcases exists_smoothTangentSection_eq_at (I := I) (M := M) (E := E) (x₀ := x) w with ⟨W, hW⟩
  have hkoszul :
      (koszulRHS (I := I) (M := M) (E := E) g (X + Y) s W) x =
        (koszulRHS (I := I) (M := M) (E := E) g X s W) x +
          (koszulRHS (I := I) (M := M) (E := E) g Y s W) x := by
    simpa using congrArg (fun F : C∞ => F x)
      (MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothTangentSection.koszulRHS_add_left
        (I := I) (M := M) (E := E) (g := g) X Y s W)
  have h1 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := (X + Y))
      (Y := s) (Z := W) x
  have h2 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := s) (Z := W) x
  have h3 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := Y)
      (Y := s) (Z := W) x
  have hinner2 :
      (2 : ℝ) * g.inner x lhs (W x) =
        (2 : ℝ) * (g.inner x
            (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
          g.inner x
            (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x)) := by
    calc
      (2 : ℝ) * g.inner x lhs (W x) =
          (koszulRHS (I := I) (M := M) (E := E) g (X + Y) s W) x := by
            simpa [lhs] using h1.symm
      _ = (koszulRHS (I := I) (M := M) (E := E) g X s W) x +
            (koszulRHS (I := I) (M := M) (E := E) g Y s W) x := hkoszul
      _ =
          (2 : ℝ) * g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
            (2 : ℝ) * g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x) := by
            simp [h2, h3]
      _ = (2 : ℝ) *
            (g.inner x
                (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
              g.inner x
                (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x)) := by
            ring
  have hinner :
      g.inner x lhs (W x) =
        g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
          g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x) :=
    mul_left_cancel₀ (a := (2 : ℝ))
      (b := g.inner x lhs (W x))
      (c := g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
        g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x))
      two_ne_zero hinner2
  have hww : g.inner x w w = 0 := by
    have hWw : W x = w := hW
    have hsub :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x)) ((g.inner x).map_sub lhs rhs)
    have hsum :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x))
        ((g.inner x).map_add
          (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x)
          (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x))
    have : g.inner x w (W x) = 0 := by
      have : g.inner x w (W x) =
          g.inner x lhs (W x) - g.inner x rhs (W x) := by
        change g.inner x (lhs - rhs) (W x) = g.inner x lhs (W x) - g.inner x rhs (W x)
        exact hsub
      have hrhs :
          g.inner x rhs (W x) =
            g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
              g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x) := by
        change
          g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x +
                covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x) =
            g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) +
              g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g Y s x) (W x)
        exact hsum
      simp [this, hrhs, hinner]
    rw [hWw] at this
    exact this
  have hw0 : w = 0 := by
    by_contra hw0
    have hpos : 0 < (g.inner x w) w := g.pos x w hw0
    exact (ne_of_gt hpos) hww
  have : lhs = rhs := by
    have : lhs - rhs = 0 := by simpa [w] using hw0
    exact sub_eq_zero.mp this
  simpa [lhs, rhs, covDerivFromMetric, covDerivFromMetricFun] using this

/-- The constructed covariant derivative is smooth-function linear in its tangent field. -/
theorem covDerivFromMetric_smul_vec
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (f : C∞) (X s : Γ∞) :
    covDerivFromMetric (I := I) (M := M) (E := E) g (f • X) s =
      f • covDerivFromMetric (I := I) (M := M) (E := E) g X s := by
  classical
  ext x
  let lhs : TM x := covDerivFromMetricFun (I := I) (M := M) (E := E) g (f • X) s x
  let rhs : TM x := (f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x
  set w : TM x := lhs - rhs with hw
  rcases exists_smoothTangentSection_eq_at (I := I) (M := M) (E := E) (x₀ := x) w with ⟨W, hW⟩
  have hkoszul :
      (koszulRHS (I := I) (M := M) (E := E) g (f • X) s W) x =
        (f * koszulRHS (I := I) (M := M) (E := E) g X s W) x := by
    simpa using congrArg (fun F : C∞ => F x)
      (MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothTangentSection.koszulRHS_smul_left
        (I := I) (M := M) (E := E) (g := g) (X := X) (Y := s) (Z := W) (f := f))
  have h1 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := (f • X))
      (Y := s) (Z := W) x
  have h2 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := s) (Z := W) x
  have hinner2 :
      (2 : ℝ) * g.inner x lhs (W x) =
        (2 : ℝ) * (f x * g.inner x
          (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
    calc
      (2 : ℝ) * g.inner x lhs (W x) =
          (koszulRHS (I := I) (M := M) (E := E) g (f • X) s W) x := by
            simpa [lhs] using h1.symm
      _ = (f * koszulRHS (I := I) (M := M) (E := E) g X s W) x := hkoszul
      _ = (f x) * (koszulRHS (I := I) (M := M) (E := E) g X s W) x := rfl
      _ = (f x) * ((2 : ℝ) * g.inner x
        (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
            simp [h2]
      _ = (2 : ℝ) * (f x * g.inner x
        (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
            ring
  have hinner :
      g.inner x lhs (W x) =
        f x * g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) :=
    mul_left_cancel₀ (a := (2 : ℝ))
      (b := g.inner x lhs (W x))
      (c := f x * g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x))
      two_ne_zero hinner2
  have hww : g.inner x w w = 0 := by
    have hWw : W x = w := hW
    have hsub :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x)) ((g.inner x).map_sub lhs rhs)
    have hsmul :
        g.inner x rhs (W x) =
          (f x) • g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) := by
      change
        g.inner x ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) =
          (f x) • g.inner x (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)
      exact congrArg (fun L : TM x →L[ℝ] ℝ => L (W x))
        ((g.inner x).map_smul (f x)
          (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x))
    have : g.inner x w (W x) = 0 := by
      have : g.inner x w (W x) =
          g.inner x lhs (W x) - g.inner x rhs (W x) := by
        change g.inner x (lhs - rhs) (W x) = g.inner x lhs (W x) - g.inner x rhs (W x)
        exact hsub
      simp [this, hsmul, hinner, smul_eq_mul]
    rw [hWw] at this
    exact this
  have hw0 : w = 0 := by
    by_contra hw0
    have hpos : 0 < (g.inner x w) w := g.pos x w hw0
    exact (ne_of_gt hpos) hww
  have : lhs = rhs := by
    have : lhs - rhs = 0 := by simpa [w] using hw0
    exact sub_eq_zero.mp this
  -- rewrite `rhs` as pointwise scalar multiplication by `f`
  simpa [lhs, rhs, covDerivFromMetric, covDerivFromMetricFun, smul_apply] using this

/-- The constructed covariant derivative obeys the Leibniz rule in its section. -/
theorem covDerivFromMetric_leibniz
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X : Γ∞) (f : C∞) (s : Γ∞) :
    covDerivFromMetric (I := I) (M := M) (E := E) g X (f • s) =
        (TangentSection.toDerivation (I := I) (M := M) X f) • s +
          f • covDerivFromMetric (I := I) (M := M) (E := E) g X s := by
  classical
  ext x
  let lhs : TM x := covDerivFromMetricFun (I := I) (M := M) (E := E) g X (f • s) x
  let rhs : TM x :=
    ((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x +
      (f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x
  set w : TM x := lhs - rhs with hw
  rcases exists_smoothTangentSection_eq_at (I := I) (M := M) (E := E) (x₀ := x) w with ⟨W, hW⟩
  have hkoszul :
      (koszulRHS (I := I) (M := M) (E := E) g X (f • s) W) x =
        ((2 : ℝ) • ((TangentSection.toDerivation (I := I) (M := M) X f) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) g s W) +
            f * koszulRHS (I := I) (M := M) (E := E) g X s W) x := by
    simpa using congrArg (fun F : C∞ => F x)
      (MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothTangentSection.koszulRHS_smul_middle
        (I := I) (M := M) (E := E) (g := g) (X := X) (Y := s) (Z := W) (f := f))
  have h1 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := (f • s)) (Z := W) x
  have h2 :=
    koszulRHS_eq_two_inner_covDerivFromMetricFun (I := I) (M := M) (E := E) (g := g) (X := X)
      (Y := s) (Z := W) x
  have hinner2 :
      (2 : ℝ) * g.inner x lhs (W x) =
        (2 : ℝ) *
          (g.inner x (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
            g.inner x
              ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
    calc
      (2 : ℝ) * g.inner x lhs (W x) =
          (koszulRHS (I := I) (M := M) (E := E) g X (f • s) W) x := by
            simpa [lhs] using h1.symm
      _ =
          ((2 : ℝ) • ((TangentSection.toDerivation (I := I) (M := M) X f) *
                smoothTangentSectionInnerFromMetric (I := I) (M := M) g s W) +
              f * koszulRHS (I := I) (M := M) (E := E) g X s W) x := hkoszul
      _ =
          (2 : ℝ) * ((TangentSection.toDerivation (I := I) (M := M) X f) x *
              (smoothTangentSectionInnerFromMetric (I := I) (M := M) g s W) x) +
            (f x) * (koszulRHS (I := I) (M := M) (E := E) g X s W) x := by
            simp [smul_eq_mul]
      _ =
          (2 : ℝ) * g.inner x
            (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
            (f x) * ((2 : ℝ) * g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
            have hsmul :
                g.inner x
                    (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) =
                  ((TangentSection.toDerivation (I := I) (M := M) X f) x) *
                    g.inner x (s x) (W x) := by
              change
                g.inner x
                    (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) =
                  ((TangentSection.toDerivation (I := I) (M := M) X f) x) •
                    g.inner x (s x) (W x)
              exact congrArg (fun L : TM x →L[ℝ] ℝ => L (W x))
                ((g.inner x).map_smul
                  ((TangentSection.toDerivation (I := I) (M := M) X f) x) (s x))
            rw [hsmul]
            simp only [smoothTangentSectionInnerFromMetric_apply, h2]
      _ =
          (2 : ℝ) * g.inner x
            (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
            (2 : ℝ) * ((f x) * g.inner x
              (covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
            ring
      _ =
          (2 : ℝ) * g.inner x
            (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
            (2 : ℝ) * g.inner x
              ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) := by
            -- move `f x` into the first slot
            simp [smul_eq_mul]
      _ =
          (2 : ℝ) *
            (g.inner x (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
              g.inner x
                ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)) := by
            ring
  have hinner :
      g.inner x lhs (W x) =
        g.inner x (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
          g.inner x ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) :=
    mul_left_cancel₀ (a := (2 : ℝ))
      (b := g.inner x lhs (W x))
      (c :=
        g.inner x (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
          g.inner x ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x))
      two_ne_zero hinner2
  have hww : g.inner x w w = 0 := by
    have hWw : W x = w := hW
    have hsub :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x)) ((g.inner x).map_sub lhs rhs)
    have hsum :=
      congrArg (fun L : TM x →L[ℝ] ℝ => L (W x))
        ((g.inner x).map_add
          (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x)
          ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x))
    have : g.inner x w (W x) = 0 := by
      have : g.inner x w (W x) =
          g.inner x lhs (W x) - g.inner x rhs (W x) := by
        change g.inner x (lhs - rhs) (W x) = g.inner x lhs (W x) - g.inner x rhs (W x)
        exact hsub
      have hrhs :
          g.inner x rhs (W x) =
            g.inner x (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
              g.inner x
                ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) := by
        change
          g.inner x
              (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x +
                (f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x) =
            g.inner x (((TangentSection.toDerivation (I := I) (M := M) X f) x) • s x) (W x) +
              g.inner x ((f x) • covDerivFromMetricFun (I := I) (M := M) (E := E) g X s x) (W x)
        exact hsum
      simp [this, hrhs, hinner]
    rw [hWw] at this
    exact this
  have hw0 : w = 0 := by
    by_contra hw0
    have hpos : 0 < (g.inner x w) w := g.pos x w hw0
    exact (ne_of_gt hpos) hww
  have : lhs = rhs := by
    have : lhs - rhs = 0 := by simpa [w] using hw0
    exact sub_eq_zero.mp this
  simpa [lhs, rhs, covDerivFromMetric, covDerivFromMetricFun, smul_apply] using this

/-- The constructed covariant derivative respects constant real scaling of its section. -/
theorem covDerivFromMetric_smul
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X : Γ∞) (a : ℝ) (s : Γ∞) :
    covDerivFromMetric (I := I) (M := M) (E := E) g X (a • s) =
      a • covDerivFromMetric (I := I) (M := M) (E := E) g X s := by
  classical
  let aC : C∞ := ⟨fun _ : M => a, contMDiff_const⟩
  have h :=
    covDerivFromMetric_leibniz (I := I) (M := M) (E := E) (g := g) (X := X) (f := aC) (s := s)
  -- simplify `X(aC) = 0` and `aC`-scalar multiplication to real scalar multiplication
  ext x
  have haC : aC x = a := rfl
  have hXaC : (TangentSection.toDerivation (I := I) (M := M) X aC) x = 0 := by
    have haCmap : aC = algebraMap ℝ C∞ a := by
      ext y
      rfl
    rw [haCmap]
    exact congrArg (fun F : C∞ => F x)
      ((TangentSection.toDerivation (I := I) (M := M) X).map_algebraMap a)
  -- rewrite at the point `x`
  have haCs : aC • s = a • s := by
    ext y
    rfl
  rw [haCs] at h
  have hEval := congrArg (fun Z : Γ∞ => Z x) h
  change
    covDerivFromMetric (I := I) (M := M) (E := E) g X (a • s) x =
      ((TangentSection.toDerivation (I := I) (M := M) X aC) x) • s x +
        (aC x) • covDerivFromMetric (I := I) (M := M) (E := E) g X s x at hEval
  rw [hXaC, haC, zero_smul, zero_add] at hEval
  exact hEval

/-- The tangent connection obtained from the supplied metric and Koszul construction. -/
noncomputable def tangentConnectionFromMetric
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) :
    SmoothTangentConnection (I := I) (M := M) (E := E) where
  covDeriv X Y := covDerivFromMetric (I := I) (M := M) (E := E) g X Y
  covDeriv_add X s t := covDerivFromMetric_add (I := I) (M := M) (E := E) (g := g) X s t
  covDeriv_smul X a s := covDerivFromMetric_smul (I := I) (M := M) (E := E) (g := g) (X := X) a s
  covDeriv_add_vec X Y s := covDerivFromMetric_add_vec (I := I) (M := M) (E := E) (g := g) X Y s
  covDeriv_smul_vec f X s := covDerivFromMetric_smul_vec (I := I) (M := M) (E := E) (g := g) f X s
  leibniz X f s := covDerivFromMetric_leibniz (I := I) (M := M) (E := E) (g := g) X f s

end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
