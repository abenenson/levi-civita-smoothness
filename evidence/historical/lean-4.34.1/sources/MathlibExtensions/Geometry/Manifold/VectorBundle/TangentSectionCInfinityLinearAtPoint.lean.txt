/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

import MathlibExtensions.Geometry.Manifold.VectorBundle.Connection
import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionPrescribedValue

/-!
# `C^∞`-linear maps on smooth tangent sections, evaluated at a point

This file proves a standard "order-0 locality" fact: evaluating a `C^∞(M)`-linear map
`Γ(TM) → C^∞(M)` at a point depends only on the value of the section in the fiber at that point.

This is a preparatory lemma for defining the Levi–Civita connection via the Koszul formula.

## Main Result

- `SmoothTangentSection.exists_eval_eq_linear_apply`:
  for `φ : Γ∞ →ₗ[C∞] C∞` and `x₀ : M`, there exists `ℓ : TangentSpace I x₀ →ₗ[ℝ] ℝ` such that
  `(φ Z) x₀ = ℓ (Z x₀)` for all `Z : Γ∞`.
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

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

variable [IsManifold I 1 M] [IsManifold I n∞ M]
variable [FiniteDimensional ℝ E] [T2Space M]

/-- Sections agreeing near a point have equal evaluations under a smooth-function-linear map. -/
private theorem eval_congr_of_eventuallyEq
    (x₀ : M) (φ : Γ∞ →ₗ[C∞] C∞) {Z Z' : Γ∞} (hZZ' : Z =ᶠ[𝓝 x₀] Z') :
    (φ Z) x₀ = (φ Z') x₀ := by
  classical
  -- Pick a set `V` on which `Z = Z'`, then choose a bump function supported in `V` and equal to 1
  -- at `x₀`. Use `C^∞(M)`-linearity to reduce to equality of `Z` and `Z'` on `support`.
  rcases hZZ'.exists_mem with ⟨V, hVnhds, hV⟩
  rcases (SmoothBumpFunction.nhds_basis_support (I := I) (c := x₀) hVnhds).mem_iff.1
      (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 x₀) with
    ⟨f, hfV, -⟩
  let fC : C∞ := ⟨fun x : M => (f x : ℝ), SmoothBumpFunction.contMDiff (I := I) (f := f)⟩
  have hsmul : (fC • Z) = (fC • Z') := by
    ext x
    change fC x • Z x = fC x • Z' x
    by_cases hx : (f x : ℝ) = 0
    · simp [fC, hx]
    · have hxV : x ∈ V := by
        have hx_supp : x ∈ Function.support (fun y : M => (f y : ℝ)) := by
          simp [Function.support, hx]
        exact hfV (subset_closure hx_supp)
      have : Z x = Z' x := hV hxV
      simp [fC, this]
  have hf_one : (fC x₀) = 1 := by
    simp [fC]
  have hφZ : (φ (fC • Z)) x₀ = (φ Z) x₀ := by
    have h := congrArg (fun g : C∞ => g x₀) (LinearMap.map_smul φ fC Z)
    have hscale : (fC • φ Z) x₀ = (φ Z) x₀ := by
      simp [smul_eq_mul, hf_one]
    exact h.trans hscale
  have hφZ' : (φ (fC • Z')) x₀ = (φ Z') x₀ := by
    have h := congrArg (fun g : C∞ => g x₀) (LinearMap.map_smul φ fC Z')
    have hscale : (fC • φ Z') x₀ = (φ Z') x₀ := by
      simp [smul_eq_mul, hf_one]
    exact h.trans hscale
  have hmid : (φ (fC • Z)) x₀ = (φ (fC • Z')) x₀ :=
    congrArg (fun W : Γ∞ => (φ W) x₀) hsmul
  calc
    (φ Z) x₀ = (φ (fC • Z)) x₀ := by simpa using hφZ.symm
    _ = (φ (fC • Z')) x₀ := hmid
    _ = (φ Z') x₀ := by simpa using hφZ'

/-- A section vanishing at a point has zero evaluation under a smooth-function-linear map. -/
private theorem eval_eq_zero_of_apply_eq_zero
    (x₀ : M) (φ : Γ∞ →ₗ[C∞] C∞) {Z : Γ∞} (hZ : Z x₀ = 0) :
    (φ Z) x₀ = 0 := by
  classical
  -- Choose a basis of the model fiber and globalize the corresponding locally-constant sections.
  let n : ℕ := Module.finrank ℝ E
  let b : Module.Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let e := trivializationAt E TM x₀
  let U : Set M := e.baseSet
  have hU : U ∈ 𝓝 x₀ := by
    have hx₀ : x₀ ∈ U := by
      simp [U, e, TangentBundle.trivializationAt_baseSet]
    simpa [U] using e.open_baseSet.mem_nhds hx₀
  -- A bump function `χ` with `tsupport χ ⊆ U` and `χ = 1` near `x₀`.
  rcases (SmoothBumpFunction.nhds_basis_support (I := I) (c := x₀) hU).mem_iff.1
      (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 x₀) with
    ⟨χ, hχU, -⟩
  let χC : C∞ := ⟨fun x : M => (χ x : ℝ), SmoothBumpFunction.contMDiff (I := I) (f := χ)⟩
  have hχ_one : χC x₀ = 1 := by
    simp [χC]
  -- Global sections `s i` that agree with `localConst x₀ (b i)` in a neighborhood of `x₀`.
  classical
  choose s hs using fun i : Fin n =>
    (exists_eq_localConst_nhds (I := I) (M := M) (E := E) (x₀ := x₀) (w := b i))
  have hs_all : ∀ᶠ x in 𝓝 x₀, ∀ i : Fin n, s i x = localConst (I := I) (M := M) (E := E) x₀ (b i) x := by
    simpa [Filter.Eventually] using Filter.eventually_all.2 hs
  -- Coordinate map of `Z` in the trivialization `e`.
  let coordZ : M → E := fun x => (e (⟨x, Z x⟩ : TangentBundle I M)).2
  have hcoordZ : ContMDiffOn I 𝓘(ℝ, E) n∞ coordZ U := by
    have hZsec :
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
          (fun x ↦ TotalSpace.mk' E x (Z x)) U :=
      (Z.contMDiff.contMDiffOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ (fun x ↦ TotalSpace.mk' E x (Z x)) U)
    -- extract the coordinate map using `contMDiffOn_section_baseSet_iff`
    simpa [coordZ, U, e] using (e.contMDiffOn_section_baseSet_iff (IB := I) (n := n∞)).1 hZsec
  -- The `i`-th coefficient function in the basis `b`, multiplied by `χ` to make it globally smooth.
  have hcoeff_at : ∀ i : Fin n, ContMDiffOn I 𝓘(ℝ) n∞ (fun x => (b.coord i) (coordZ x)) U := by
    intro i
    -- Use the fact that linear maps from finite-dimensional normed spaces are continuous.
    let ℓi : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
    have hℓi : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] ℝ) n∞ (fun _ : M => ℓi) U :=
      (contMDiff_const.contMDiffOn : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] ℝ) n∞ (fun _ : M => ℓi) U)
    simpa [ℓi, coordZ] using (hℓi.clm_apply hcoordZ)
  let coeff (i : Fin n) : M → ℝ := fun x => (b.coord i) (coordZ x)
  have hcoeff : ∀ i : Fin n, ContMDiffOn I 𝓘(ℝ) n∞ (coeff i) U := by
    intro i
    simpa [coeff] using hcoeff_at i
  let a (i : Fin n) : C∞ :=
    ⟨fun x : M => (χ x : ℝ) * coeff i x,
      contMDiff_of_tsupport (I := I) (n := n∞) (f := fun x : M => (χ x : ℝ) * coeff i x)
        (fun x hx => by
          have hxU : x ∈ U := hχU <| (tsupport_smul_subset_left (fun x : M => (χ x : ℝ)) (coeff i) hx)
          have hχx : ContMDiffAt I 𝓘(ℝ) n∞ (fun y : M => (χ y : ℝ)) x :=
            (SmoothBumpFunction.contMDiff (I := I) (f := χ)).contMDiffAt
          have hcoeffx : ContMDiffAt I 𝓘(ℝ) n∞ (coeff i) x :=
            (hcoeff i).contMDiffAt (e.open_baseSet.mem_nhds hxU)
          simpa [coeff, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using! hχx.mul hcoeffx)⟩
  -- A section built from these coefficients and the globalized local constants.
  let Z' : Γ∞ := ∑ i : Fin n, (a i) • (s i)
  have hZ'_eq : Z =ᶠ[𝓝 x₀] Z' := by
    have hxU : ∀ᶠ x in 𝓝 x₀, x ∈ U := by
      exact hU
    have hχone : ∀ᶠ x in 𝓝 x₀, (χ x : ℝ) = 1 := by
      simpa using! (χ.eventuallyEq_one : χ =ᶠ[𝓝 x₀] 1)
    filter_upwards [hxU, hχone, hs_all] with x hxU hxχ hsx
    -- Pointwise, inside `U`, `Z` decomposes in the trivialization using the basis `b`.
    have hx_target : (x, coordZ x) ∈ e.target := by
      simpa [coordZ, U, e, TangentBundle.trivializationAt_target, TangentBundle.trivializationAt_baseSet, hxU]
    have hx_source : (⟨x, Z x⟩ : TangentBundle I M) ∈ e.source := by
      simpa [U, e, TangentBundle.trivializationAt_source, hxU]
    have hZcoord : Z x = localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x := by
      -- `e.symm (e ⟨x, Z x⟩) = ⟨x, Z x⟩` on `U`.
      have : (e.toPartialEquiv.symm (x, coordZ x) : TangentBundle I M) = ⟨x, Z x⟩ := by
        calc
          (e.toPartialEquiv.symm (x, coordZ x) : TangentBundle I M)
              = e.toPartialEquiv.symm (e (⟨x, Z x⟩ : TangentBundle I M)) := by
                  rfl
          _ = (⟨x, Z x⟩ : TangentBundle I M) := by
                simpa using (e.symm_apply_apply hx_source)
      simpa [localConst, coordZ, e] using! (congrArg (fun z : TangentBundle I M => z.2) this).symm
    -- Expand `coordZ x` in the basis `b` and translate back via `localConst`.
    have hdecomp :
        localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x =
          ∑ i : Fin n, (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x := by
      -- Apply the trivialization at `x` and use linearity + `Basis.sum_coords`.
      have hx_base : x ∈ e.baseSet := hxU
      have hxV : x ∈ (trivializationAt E TM x₀).baseSet := hxU
      -- Use injectivity of the coordinate map `v ↦ (e ⟨x, v⟩).2` on the fiber.
      let φx := (e.continuousLinearEquivAt (R := ℝ) x hx_base)
      have hφx :
          (fun v : TangentSpace I x => (e (⟨x, v⟩ : TangentBundle I M)).2) = φx := by
        rfl
      have hφx_localConst (w : E) :
          φx (localConst (I := I) (M := M) (E := E) x₀ w x) = w := by
        -- unpack `localConst` and simplify in the trivialization
        have hx' : x ∈ e.baseSet := hx_base
        simpa [φx, localConst, e] using
          (localConst_trivializationAt_snd (I := I) (M := M) (E := E) (x₀ := x₀) w (x := x) hx')
      have hφx_coord :
          φx (localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x) = coordZ x := by
        simpa using hφx_localConst (coordZ x)
      have hφx_sum :
          φx (∑ i : Fin n, (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x) =
            ∑ i : Fin n, (coeff i x) • (b i) := by
        -- linearity of `φx`
        simp [φx, hφx_localConst]
      -- Now use the basis identity.
      have hbasis : coordZ x = ∑ i : Fin n, (coeff i x) • (b i) := by
        simp [coeff, Module.Basis.coord_apply]
      apply φx.injective
      calc
        φx (localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x) = coordZ x := hφx_coord
        _ = ∑ i : Fin n, (coeff i x) • (b i) := hbasis
        _ =
            φx
              (∑ i : Fin n,
                (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x) := hφx_sum.symm
    -- Put it together and rewrite the definition of `Z'` pointwise.
    have : Z x = ∑ i : Fin n, ((a i) x) • (s i x) := by
      calc
        Z x = localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x := hZcoord
        _ = ∑ i : Fin n, (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x := hdecomp
        _ = ∑ i : Fin n, ((a i) x) • (s i x) := by
              -- On the neighborhood, `χ = 1` and `s i = localConst ...`.
              simp [a, coeff, hsx, hxχ]
    have hZ'x : Z' x = ∑ i : Fin n, (a i x) • (s i x) := by
      classical
      -- `simp` does not automatically push evaluation through `∑` for smooth sections, so we use an
      -- explicit evaluation additive morphism.
      let eval : Γ∞ →+ TangentSpace I x :=
        { toFun := fun Z => Z x
          map_zero' := by simp
          map_add' := by
            intro Z W
            simp }
      -- Unfold `Z'` and simplify pointwise.
      change eval Z' = ∑ i : Fin n, (a i x) • (s i x)
      simp [Z', eval, smul_apply]
    simpa [hZ'x] using! this
  -- Use locality to reduce to `Z'`, and compute using `C∞`-linearity.
  have hlocal : (φ Z) x₀ = (φ Z') x₀ :=
    eval_congr_of_eventuallyEq (I := I) (M := M) (E := E) x₀ φ hZ'_eq
  have ha0 : ∀ i : Fin n, (a i) x₀ = 0 := by
    intro i
    have hx₀ : x₀ ∈ U := by
      simp [U, e, TangentBundle.trivializationAt_baseSet]
    have hcoord0 : coordZ x₀ = 0 := by
      -- `coordZ x₀` is linear in the fiber, and `Z x₀ = 0`.
      let φx₀ := (e.continuousLinearEquivAt (R := ℝ) x₀ hx₀)
      change (φx₀ (Z x₀)) = 0
      simp [hZ]
    -- `a i x₀ = χ x₀ * coeff i x₀`, and `coeff i x₀ = 0`.
    have : coeff i x₀ = 0 := by
      simp [coeff, hcoord0]
    simp [a, this]
  -- Finish: `φ Z'` evaluates to zero at `x₀`, hence so does `φ Z`.
  have hφZ' : (φ Z') x₀ = ∑ i : Fin n, (a i x₀) * (φ (s i) x₀) := by
    classical
    have h1 : (φ Z') x₀ = (∑ i : Fin n, (a i) * (φ (s i))) x₀ := by
      simp [Z', smul_eq_mul]
    have h2 :
        (∑ i : Fin n, (a i) * (φ (s i))) x₀ = ∑ i : Fin n, (a i x₀) * (φ (s i) x₀) := by
      -- Evaluate at `x₀` using the ring hom `ContMDiffMap.evalRingHom`.
      let ev : C∞ →+* ℝ :=
        ContMDiffMap.evalRingHom (I := I) (I' := 𝓘(ℝ, ℝ)) (n := n∞) (N := M) (m := x₀)
      have hsum :
          ev (∑ i : Fin n, (a i) * (φ (s i))) = ∑ i : Fin n, ev ((a i) * (φ (s i))) := by
        classical
        exact map_sum ev (fun i : Fin n => (a i) * (φ (s i))) Finset.univ
      calc
        (∑ i : Fin n, (a i) * (φ (s i))) x₀
            = ev (∑ i : Fin n, (a i) * (φ (s i))) := rfl
        _ = ∑ i : Fin n, ev ((a i) * (φ (s i))) := hsum
        _ = ∑ i : Fin n, (a i x₀) * (φ (s i) x₀) := by
              simp [ev, ContMDiffMap.evalRingHom, map_mul]
    exact h1.trans h2
  have : (φ Z') x₀ = 0 := by
    simp [hφZ', ha0]
  simpa [hlocal] using this

/-- Evaluating a `C^∞(M)`-linear map `Γ∞ → C∞` at a point factors through the fiber at that point. -/
theorem exists_eval_eq_linear_apply
    (x₀ : M) (φ : Γ∞ →ₗ[C∞] C∞) :
    ∃ ℓ : TangentSpace I x₀ →ₗ[ℝ] ℝ, ∀ Z : Γ∞, (φ Z) x₀ = ℓ (Z x₀) := by
  classical
  -- Choose a global section `σ v` with `σ v x₀ = v` using a localized trivialization.
  let e := trivializationAt E TM x₀
  have hsec : ∀ v₀ : TangentSpace I x₀, ∃ σ : Γ∞, σ x₀ = v₀ := by
    intro v₀
    let w : E := (e (⟨x₀, v₀⟩ : TangentBundle I M)).2
    rcases exists_eq_localConst_nhds (I := I) (M := M) (E := E) (x₀ := x₀) (w := w) with ⟨σ, hσ⟩
    have hσ' : σ x₀ = localConst (I := I) (M := M) (E := E) x₀ w x₀ :=
      (Filter.EventuallyEq.eq_of_nhds (f := fun x => σ x)
        (g := fun x => localConst (I := I) (M := M) (E := E) x₀ w x) (by
          simpa using! hσ))
    refine ⟨σ, ?_⟩
    simpa [w, hσ'] using (localConst_apply_self (I := I) (M := M) (E := E) (x₀ := x₀) v₀)
  choose σ hσ using hsec
  -- Define `ℓ v := (φ (σ v)) x₀` and prove it is well-defined / linear using the kernel lemma.
  refine ⟨
    { toFun := fun v => (φ (σ v)) x₀
      map_add' := by
        intro v₁ v₂
        have h0 : (σ (v₁ + v₂) - (σ v₁ + σ v₂)) x₀ = 0 := by
          simp [hσ]
        have hφ0 :
            (φ (σ (v₁ + v₂) - (σ v₁ + σ v₂))) x₀ = 0 :=
          eval_eq_zero_of_apply_eq_zero (I := I) (M := M) (E := E) (x₀ := x₀) φ h0
        have hEq : (φ (σ (v₁ + v₂))) x₀ = (φ (σ v₁ + σ v₂)) x₀ := by
          apply sub_eq_zero.mp
          simpa [map_sub] using hφ0
        calc
          (φ (σ (v₁ + v₂))) x₀ = (φ (σ v₁ + σ v₂)) x₀ := hEq
          _ = (φ (σ v₁)) x₀ + (φ (σ v₂)) x₀ := by simp [map_add]
      map_smul' := by
        intro a v
        let aC : C∞ := ⟨fun _ : M => a, contMDiff_const⟩
        have h0 : (σ (a • v) - (aC • σ v)) x₀ = 0 := by
          change (σ (a • v)) x₀ - aC x₀ • (σ v) x₀ = 0
          simp [hσ, aC]
        have hφ0 :
            (φ (σ (a • v) - (aC • σ v))) x₀ = 0 :=
          eval_eq_zero_of_apply_eq_zero (I := I) (M := M) (E := E) (x₀ := x₀) φ h0
        have hEq : (φ (σ (a • v))) x₀ = (φ (aC • σ v)) x₀ := by
          apply sub_eq_zero.mp
          simpa [map_sub] using hφ0
        have hsmul :
            (φ (aC • σ v)) x₀ = (aC • (φ (σ v))) x₀ := by
          exact congrArg (fun g : C∞ => g x₀) (LinearMap.map_smul φ aC (σ v))
        have haC : aC x₀ = a := rfl
        simpa [hsmul, smul_eq_mul, haC] using hEq }, ?_⟩
  intro Z
  have h0 : (Z - σ (Z x₀)) x₀ = 0 := by
    simp [hσ]
  have hφ0 :
      (φ (Z - σ (Z x₀))) x₀ = 0 :=
    eval_eq_zero_of_apply_eq_zero (I := I) (M := M) (E := E) (x₀ := x₀) φ h0
  have hEq : (φ Z) x₀ = (φ (σ (Z x₀))) x₀ := by
    apply sub_eq_zero.mp
    simpa [map_sub] using hφ0
  simpa using hEq
  end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
