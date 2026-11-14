/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public import MathlibExtensions.Geometry.Manifold.VectorBundle.Connection
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionPrescribedValue

@[expose] public section

/-!
# Local decomposition of smooth tangent sections

Near a point `x₀`, smooth tangent sections can be decomposed (locally) as a finite `C^∞(M)`-linear
combination of a fixed finite family of sections coming from a local trivialization.

This is used to extend identities proved on a local frame to all tangent sections.
-/

open scoped Topology Bundle Manifold ContDiff BigOperators

namespace MathlibExtensions.Geometry.Manifold.VectorBundle

open Bundle

local notation "n∞" => (∞ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I n∞ M]
  [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

omit [CompleteSpace E] in
/-- Fix a localConst frame given by the `finBasis` of `E`, globalize it to smooth sections using a
bump function, and show that any smooth tangent section decomposes locally as a `C∞`-linear
combination of this frame. -/
theorem exists_localConst_finBasis_nhds (x₀ : M) :
    ∃ (s : Fin (Module.finrank ℝ E) → Γ∞),
      (∀ i, ∀ᶠ x in 𝓝 x₀,
        s i x = localConst (I := I) (M := M) (E := E) x₀ ((Module.finBasis ℝ E) i) x) ∧
      (∀ Z : Γ∞, ∃ a : Fin (Module.finrank ℝ E) → C∞,
        Z =ᶠ[𝓝 x₀] (∑ i, (a i) • (s i) : Γ∞)) := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let b : Module.Basis (Fin n) ℝ E := Module.finBasis ℝ E
  -- Choose global smooth sections `s i` that agree with the local constants near `x₀`.
  have hs_exists :
      ∀ i : Fin n,
        ∃ s : Γ∞,
          ∀ᶠ x in 𝓝 x₀, s x = localConst (I := I) (M := M) (E := E) x₀ (b i) x := by
    intro i
    simpa [b] using
      (exists_eq_localConst_nhds (I := I) (M := M) (E := E) (x₀ := x₀) (w := b i))
  choose s hs using hs_exists
  have hs_all :
      ∀ᶠ x in 𝓝 x₀, ∀ i : Fin n, s i x = localConst (I := I) (M := M) (E := E) x₀ (b i) x := by
    simpa using Filter.eventually_all.2 hs
  refine ⟨(fun i => s i), ?_, ?_⟩
  · intro i
    simpa [n, b] using hs i
  · intro Z
    -- Work in the chart-based trivialization at `x₀`.
    let e := trivializationAt E TM x₀
    let U : Set M := e.baseSet
    have hU : U ∈ 𝓝 x₀ := by
      have hx₀ : x₀ ∈ U := by
        simp [U, e, TangentBundle.trivializationAt_baseSet]
      simpa [U] using e.open_baseSet.mem_nhds hx₀
    -- Choose a bump function `χ` with `tsupport χ ⊆ U`.
    rcases (SmoothBumpFunction.nhds_basis_support (I := I) (c := x₀) hU).mem_iff.1
        (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 x₀) with
      ⟨χ, hχU, -⟩
    -- Coordinate map of `Z` in the trivialization.
    let coordZ : M → E := fun x => (e (⟨x, Z x⟩ : TangentBundle I M)).2
    have hcoordZ : ContMDiffOn I 𝓘(ℝ, E) n∞ coordZ U := by
      have hZsec :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
            (fun x ↦ TotalSpace.mk' E x (Z x)) U :=
        (Z.contMDiff.contMDiffOn :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ (fun x ↦ TotalSpace.mk' E x (Z x)) U)
      -- extract the coordinate map using `contMDiffOn_section_baseSet_iff`
      simpa [coordZ, U, e] using (e.contMDiffOn_section_baseSet_iff (IB := I) (n := n∞)).1 hZsec
    -- Coefficient functions in the basis `b`, globalized via `χ`.
    have hcoeff_at : ∀ i : Fin n, ContMDiffOn I 𝓘(ℝ) n∞ (fun x => (b.coord i) (coordZ x)) U := by
      intro i
      let ℓi : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
      have hℓi : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] ℝ) n∞ (fun _ : M => ℓi) U :=
        (contMDiff_const.contMDiffOn :
          ContMDiffOn I 𝓘(ℝ, E →L[ℝ] ℝ) n∞ (fun _ : M => ℓi) U)
      simpa [ℓi, coordZ] using (hℓi.clm_apply hcoordZ)
    let coeff (i : Fin n) : M → ℝ := fun x => (b.coord i) (coordZ x)
    have hcoeff : ∀ i : Fin n, ContMDiffOn I 𝓘(ℝ) n∞ (coeff i) U := by
      intro i
      simpa [coeff] using hcoeff_at i
    let a (i : Fin n) : C∞ :=
      ⟨fun x : M => (χ x : ℝ) * coeff i x,
        contMDiff_of_tsupport (I := I) (n := n∞) (f := fun x : M => (χ x : ℝ) * coeff i x)
          (fun x hx => by
            have hxU : x ∈ U := hχU <|
              (tsupport_smul_subset_left (fun x : M => (χ x : ℝ)) (coeff i) hx)
            have hχx : ContMDiffAt I 𝓘(ℝ) n∞ (fun y : M => (χ y : ℝ)) x :=
              (SmoothBumpFunction.contMDiff (I := I) (f := χ)).contMDiffAt
            have hcoeffx : ContMDiffAt I 𝓘(ℝ) n∞ (coeff i) x :=
              (hcoeff i).contMDiffAt (e.open_baseSet.mem_nhds hxU)
            simpa [coeff, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using! hχx.mul hcoeffx)⟩
    -- A section built from these coefficients and the globalized local constants.
    let Z' : Γ∞ := ∑ i : Fin n, (a i) • (s i)
    have hZ'_eq : Z =ᶠ[𝓝 x₀] Z' := by
      have hxU : ∀ᶠ x in 𝓝 x₀, x ∈ U := hU
      have hχone : ∀ᶠ x in 𝓝 x₀, (χ x : ℝ) = 1 := by
        simpa using! (χ.eventuallyEq_one : χ =ᶠ[𝓝 x₀] 1)
      filter_upwards [hxU, hχone, hs_all] with x hxU hxχ hsx
      have hx_source : (⟨x, Z x⟩ : TangentBundle I M) ∈ e.source := by
        simpa [U, e, TangentBundle.trivializationAt_source, hxU]
      have hZcoord : Z x = localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x := by
        have : (e.toPartialEquiv.symm (x, coordZ x) : TangentBundle I M) = ⟨x, Z x⟩ := by
          calc
            (e.toPartialEquiv.symm (x, coordZ x) : TangentBundle I M)
                = e.toPartialEquiv.symm (e (⟨x, Z x⟩ : TangentBundle I M)) := by
                    rfl
            _ = (⟨x, Z x⟩ : TangentBundle I M) := by
                  simpa using (e.symm_apply_apply hx_source)
        simpa [localConst, coordZ, e] using! (congrArg (fun z : TangentBundle I M => z.2) this).symm
      have hdecomp :
          localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x =
            ∑ i : Fin n, (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x := by
        have hx_base : x ∈ e.baseSet := hxU
        let φx := (e.continuousLinearEquivAt (R := ℝ) x hx_base)
        have hφx_localConst (w : E) :
            φx (localConst (I := I) (M := M) (E := E) x₀ w x) = w := by
          have hx' : x ∈ e.baseSet := hx_base
          simpa [φx, localConst, e] using
            (localConst_trivializationAt_snd (I := I) (M := M) (E := E) (x₀ := x₀) w (x := x) hx')
        have hφx_coord :
            φx (localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x) = coordZ x := by
          simpa using hφx_localConst (coordZ x)
        have hφx_sum :
            φx (∑ i : Fin n, (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x) =
              ∑ i : Fin n, (coeff i x) • (b i) := by
          simp [φx, hφx_localConst]
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
      have : Z x = ∑ i : Fin n, ((a i) x) • (s i x) := by
        calc
          Z x = localConst (I := I) (M := M) (E := E) x₀ (coordZ x) x := hZcoord
          _ =
              ∑ i : Fin n, (coeff i x) • localConst (I := I) (M := M) (E := E) x₀ (b i) x := hdecomp
          _ = ∑ i : Fin n, ((a i) x) • (s i x) := by
                simp [a, coeff, hsx, hxχ]
      have hZ'x : Z' x = ∑ i : Fin n, (a i x) • (s i x) := by
        classical
        let eval : Γ∞ →+ TangentSpace I x :=
          { toFun := fun Z => Z x
            map_zero' := by simp
            map_add' := by
              intro Z W
              simp }
        have hs :
            eval (∑ i : Fin n, a i • s i) = ∑ i : Fin n, eval (a i • s i) := by
          classical
          exact (map_sum eval (fun i : Fin n => a i • s i) Finset.univ)
        change eval Z' = ∑ i : Fin n, (a i x) • (s i x)
        -- Unfold `Z'` and rewrite the RHS pointwise using `smul_apply`.
        simp [Z']
        have hsR : (∑ i : Fin n, eval (a i • s i)) = ∑ i : Fin n, (a i x) • (s i x) := by
          simp [eval, smul_apply]
        exact hsR
      simpa [hZ'x] using! this
    refine ⟨a, ?_⟩
    simpa [Z'] using hZ'_eq

end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
