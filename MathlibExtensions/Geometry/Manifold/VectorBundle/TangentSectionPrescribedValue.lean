/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section

/-!
# Smooth tangent sections with prescribed value

This file provides small existence lemmas for smooth tangent sections with prescribed pointwise
values.

This is a preparatory tool for the Koszul-based construction of the Levi–Civita connection.
-/

open scoped Topology Bundle Manifold ContDiff

namespace MathlibExtensions.Geometry.Manifold.VectorBundle

open Bundle

local notation "n∞" => (∞ : WithTop ℕ∞)

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

section LocalConst

variable [IsManifold I 1 M] [IsManifold I n∞ M]

/-- The tangent section that is (fiberwise) constant in the chart-based trivialization
`trivializationAt ... x₀`, on its base set. Outside the base set, this is just a convenient
total-space representative (no smoothness is claimed there). -/
noncomputable def localConst (x₀ : M) (w : E) : (x : M) → TangentSpace I x :=
  fun x => ((trivializationAt E TM x₀).toPartialEquiv.symm (x, w)).2

omit [IsManifold I n∞ M] in
/-- If `w` is the `trivializationAt`-coordinate of a tangent vector `v₀ : TM x₀`, then
`localConst x₀ w` evaluates back to `v₀` at `x₀`. -/
theorem localConst_apply_self (x₀ : M) (v₀ : TangentSpace I x₀) :
    localConst (I := I) (M := M) (E := E) x₀
        ((trivializationAt E TM x₀ (⟨x₀, v₀⟩ : TangentBundle I M)).2) x₀ = v₀ := by
  let e := trivializationAt E TM x₀
  have hx₀_source : (⟨x₀, v₀⟩ : TangentBundle I M) ∈ e.source := by
    simp [e, TangentBundle.trivializationAt_source]
  have he_pair :
      e (⟨x₀, v₀⟩ : TangentBundle I M) =
        (x₀, (e (⟨x₀, v₀⟩ : TangentBundle I M)).2) := by
    ext
    · simp [e]
    · rfl
  have :
      (e.toPartialEquiv.symm
          (x₀, (e (⟨x₀, v₀⟩ : TangentBundle I M)).2) : TangentBundle I M) =
        (⟨x₀, v₀⟩ : TangentBundle I M) := by
    calc
      (e.toPartialEquiv.symm
          (x₀, (e (⟨x₀, v₀⟩ : TangentBundle I M)).2) : TangentBundle I M) =
          e.toPartialEquiv.symm (e (⟨x₀, v₀⟩ : TangentBundle I M)) := by
            simpa using congrArg e.toPartialEquiv.symm he_pair.symm
      _ = (⟨x₀, v₀⟩ : TangentBundle I M) := by
            simpa using (e.symm_apply_apply hx₀_source)
  simpa [localConst, e] using! congrArg (fun z : TangentBundle I M => z.2) this

omit [IsManifold I n∞ M] in
/-- On the trivialization base set, the chart coordinate of the local section is `w`. -/
theorem localConst_trivializationAt_snd (x₀ : M) (w : E) {x : M}
    (hx : x ∈ (trivializationAt E TM x₀).baseSet) :
    (trivializationAt E TM x₀ (⟨x, localConst (I := I) (M := M) (E := E) x₀ w x⟩ : TangentBundle I M)).2 = w := by
  let e := trivializationAt E TM x₀
  have hx_target : (x, w) ∈ e.target := by
    simpa [e, TangentBundle.trivializationAt_target, TangentBundle.trivializationAt_baseSet, hx]
  have hx_mk :
      (e.toPartialEquiv.symm (x, w) : TangentBundle I M) = ⟨x, (e.toPartialEquiv.symm (x, w)).2⟩ := by
    ext
    · simpa using (e.proj_symm_apply hx_target)
    · rfl
  have hx_mk' :
      (⟨x, localConst (I := I) (M := M) (E := E) x₀ w x⟩ : TangentBundle I M) = e.toPartialEquiv.symm (x, w) := by
    simp [localConst, e, hx_mk]
  calc
    (trivializationAt E TM x₀ (⟨x, localConst (I := I) (M := M) (E := E) x₀ w x⟩ : TangentBundle I M)).2
        = (e (e.toPartialEquiv.symm (x, w))).2 := by
            simp [e, hx_mk']
    _ = (x, w).2 := by
          simpa [e] using congrArg Prod.snd (e.apply_symm_apply hx_target)
    _ = w := rfl

/-- The local section is smooth on the base set of its defining trivialization. -/
theorem contMDiffOn_localConst (x₀ : M) (w : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
      (fun x ↦ TotalSpace.mk' E x (localConst (I := I) (M := M) (E := E) x₀ w x))
      (trivializationAt E TM x₀).baseSet := by
  let e := trivializationAt E TM x₀
  have hcoord :
      ContMDiffOn I 𝓘(ℝ, E) n∞
        (fun x ↦ (e (⟨x, localConst (I := I) (M := M) (E := E) x₀ w x⟩ : TangentBundle I M)).2)
        e.baseSet := by
    refine (contMDiff_const.contMDiffOn : ContMDiffOn I 𝓘(ℝ, E) n∞ (fun _ : M => w) e.baseSet).congr
      (fun x hx => ?_)
    simpa [e, localConst] using
      localConst_trivializationAt_snd (I := I) (M := M) (E := E) (x₀ := x₀) w (x := x) hx
  exact ((e.contMDiffOn_section_baseSet_iff (IB := I) (n := n∞)).2 hcoord)

section BumpGlobalize

variable [FiniteDimensional ℝ E] [T2Space M]

/-- If `x` lies in the source of the preferred chart at `c`, then the chart-local constant field
`localConst c w` can be bump-globalized to a smooth tangent section agreeing with it on a
neighborhood of `x`. -/
theorem exists_eq_localConst_nhds_of_mem_source
    (c : M) {x : M} (hx : x ∈ (chartAt H c).source) (w : E) :
    ∃ s : Γ∞, ∀ᶠ y in 𝓝 x, s y = localConst (I := I) (M := M) (E := E) c w y := by
  classical
  let U : Set M := (trivializationAt E TM c).baseSet
  have hU : U ∈ 𝓝 x := by
    have hxU : x ∈ U := by
      simpa [U, TangentBundle.trivializationAt_baseSet] using hx
    exact (trivializationAt E TM c).open_baseSet.mem_nhds hxU
  -- Choose a smooth bump function `f` with `tsupport f ⊆ U`.
  rcases (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hU).mem_iff.1
      (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 x) with
    ⟨f, hfU, -⟩
  have hf_cont : ContMDiffOn I 𝓘(ℝ) n∞ (fun x : M => (f x : ℝ)) U :=
    (SmoothBumpFunction.contMDiff (I := I) (f := f)).contMDiffOn
  have hs0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
      (fun x ↦ TotalSpace.mk' E x (localConst (I := I) (M := M) (E := E) c w x)) U := by
    simpa [U] using contMDiffOn_localConst (I := I) (M := M) (E := E) (x₀ := c) w
  have hs_mul :
      ContMDiff I (I.prod 𝓘(ℝ, E)) n∞
        (fun x ↦ TotalSpace.mk' E x ((f x : ℝ) • localConst (I := I) (M := M) (E := E) c w x)) := by
    have hU_open : IsOpen U := by
      simpa [U] using (trivializationAt E TM c).open_baseSet
    simpa [U] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (n := n∞) (F := E) (V := TM)
        (u := U) (s := localConst (I := I) (M := M) (E := E) c w) (ψ := fun x : M => (f x : ℝ))
        hf_cont hU_open hfU hs0)
  refine ⟨⟨fun y => (f y : ℝ) • localConst (I := I) (M := M) (E := E) c w y, hs_mul⟩, ?_⟩
  filter_upwards [f.eventuallyEq_one] with x hx
  simp [hx]

/-- If a compact set `K` lies in the source of the preferred chart at `c`, then
`localConst c w` can be globalized to a smooth tangent section agreeing with it on
some neighborhood of `K`. -/
theorem exists_eq_localConst_nhdsSet_of_isCompact_of_subset_source
    [SigmaCompactSpace M] [T3Space M]
    (c : M) {K : Set M} (hK : IsCompact K) (hKsource : K ⊆ (chartAt H c).source) (w : E) :
    ∃ s : Γ∞, ∀ᶠ y in 𝓝ˢ K, s y = localConst (I := I) (M := M) (E := E) c w y := by
  classical
  let U : Set M := (trivializationAt E TM c).baseSet
  have hU_open : IsOpen U := by
    simpa [U] using (trivializationAt E TM c).open_baseSet
  have hKU : K ⊆ U := by
    simpa [U, TangentBundle.trivializationAt_baseSet] using hKsource
  have hU : U ∈ 𝓝ˢ K := (hU_open.mem_nhdsSet).2 hKU
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hV_open, hKV, hVclU⟩
  have hKintV : K ⊆ interior V := by
    simpa [hV_open.interior_eq] using hKV
  rcases exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (n := (⊤ : ℕ∞))
      (s := K) (t := V) hK.isClosed hKintV
      with ⟨f, hf_one, hf_zero, _hf_range⟩
  have hsupportV : Function.support (fun x : M => (f x : ℝ)) ⊆ V :=
    Function.support_subset_iff'.mpr hf_zero
  have htsupportU : tsupport (fun x : M => (f x : ℝ)) ⊆ U := by
    refine (closure_minimal ?_ isClosed_closure).trans hVclU
    intro x hx
    exact subset_closure (hsupportV hx)
  have hf_cont : ContMDiffOn I 𝓘(ℝ) n∞ (fun x : M => (f x : ℝ)) U :=
    f.contMDiff.contMDiffOn
  have hs0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
      (fun x ↦ TotalSpace.mk' E x (localConst (I := I) (M := M) (E := E) c w x)) U := by
    simpa [U] using contMDiffOn_localConst (I := I) (M := M) (E := E) (x₀ := c) w
  have hs_mul :
      ContMDiff I (I.prod 𝓘(ℝ, E)) n∞
        (fun x ↦ TotalSpace.mk' E x ((f x : ℝ) • localConst (I := I) (M := M) (E := E) c w x)) := by
    simpa [U] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (n := n∞) (F := E) (V := TM)
        (u := U) (s := localConst (I := I) (M := M) (E := E) c w) (ψ := fun x : M => (f x : ℝ))
        hf_cont hU_open htsupportU hs0)
  refine ⟨⟨fun y => (f y : ℝ) • localConst (I := I) (M := M) (E := E) c w y, hs_mul⟩, ?_⟩
  filter_upwards [hf_one] with y hy
  simp [hy]

/-- Finite families of chart-local constant model vectors can be globalized simultaneously on one
neighborhood of a compact set inside a fixed chart source. -/
theorem exists_forall_eq_localConst_nhdsSet_of_isCompact_of_subset_source
    [SigmaCompactSpace M] [T3Space M] {ι : Type*} [Fintype ι]
    (c : M) {K : Set M} (hK : IsCompact K) (hKsource : K ⊆ (chartAt H c).source) (w : ι → E) :
    ∃ s : ι → Γ∞, ∀ᶠ y in 𝓝ˢ K, ∀ i, s i y = localConst (I := I) (M := M) (E := E) c (w i) y := by
  classical
  choose s hs using fun i : ι =>
    exists_eq_localConst_nhdsSet_of_isCompact_of_subset_source
      (I := I) (M := M) (E := E) c hK hKsource (w i)
  refine ⟨s, ?_⟩
  have hall :
      ∀ t : Finset ι,
        ∀ᶠ y in 𝓝ˢ K, ∀ i ∈ t, s i y = localConst (I := I) (M := M) (E := E) c (w i) y := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · exact Filter.Eventually.of_forall fun y i hi => False.elim (Finset.notMem_empty i hi)
    · intro a t hat hIH
      filter_upwards [hs a, hIH] with y hya hyt i hi
      rcases Finset.mem_insert.mp hi with rfl | hit
      · exact hya
      · exact hyt i hit
  simpa using (hall Finset.univ)

/-- A smooth tangent section agrees with the local section near its base point. -/
theorem exists_eq_localConst_nhds (x₀ : M) (w : E) :
    ∃ s : Γ∞, ∀ᶠ x in 𝓝 x₀, s x = localConst (I := I) (M := M) (E := E) x₀ w x := by
  exact exists_eq_localConst_nhds_of_mem_source (I := I) (M := M) (E := E) x₀ (hx := by simp) w

/-- Any tangent vector at a point extends to a global smooth tangent section with that value.
This lightweight version follows from chart-local constants and does not require the stronger
selection theorem used by `exists_eq`. -/
theorem exists_eq_at (x₀ : M) (v₀ : TangentSpace I x₀) : ∃ s : Γ∞, s x₀ = v₀ := by
  classical
  let w : E := (trivializationAt E TM x₀ (⟨x₀, v₀⟩ : TangentBundle I M)).2
  rcases exists_eq_localConst_nhds (I := I) (M := M) (E := E) x₀ w with ⟨s, hs⟩
  have hs' :
      s x₀ = localConst (I := I) (M := M) (E := E) x₀ w x₀ :=
    (Filter.EventuallyEq.eq_of_nhds (f := fun x => s x)
      (g := fun x => localConst (I := I) (M := M) (E := E) x₀ w x) (by
        simpa using! hs))
  refine ⟨s, ?_⟩
  simpa [w, hs'] using
    (localConst_apply_self (I := I) (M := M) (E := E) (x₀ := x₀) v₀)

end BumpGlobalize

end LocalConst

section PrescribedValue

variable [IsManifold I 1 M] [IsManifold I n∞ M]
variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- A smooth tangent section takes the prescribed tangent value at the specified point. -/
theorem exists_eq (x₀ : M) (v₀ : TangentSpace I x₀) : ∃ s : Γ∞, s x₀ = v₀ := by
  classical
  -- Fiberwise constraints: enforce `s x₀ = v₀` and leave other fibers unconstrained.
  let t : ∀ x : M, Set (TangentSpace I x) :=
    fun x => if hx : x = x₀ then { by subst hx; exact v₀ } else Set.univ
  have ht_conv : ∀ x : M, Convex ℝ (t x) := by
    intro x
    by_cases hx : x = x₀ <;> simp [t, hx, convex_singleton, convex_univ]
  have Hloc :
      ∀ p : M, ∃ U ∈ 𝓝 p, ∃ (s_loc : (x : M) → TangentSpace I x),
        (ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ (fun x ↦ TotalSpace.mk' E x (s_loc x)) U) ∧
          (∀ y ∈ U, s_loc y ∈ t y) := by
    intro p
    by_cases hp : p = x₀
    · subst p
      let e := trivializationAt E TM x₀
      let v : E := (e (⟨x₀, v₀⟩ : TangentBundle I M)).2
      let s_loc : (x : M) → TangentSpace I x := fun x => (e.toPartialEquiv.symm (x, v)).2
      refine ⟨e.baseSet, ?_, s_loc, ?_, ?_⟩
      · -- `e.baseSet` is open and contains `x₀`.
        have hx₀ : x₀ ∈ e.baseSet := by
          simp [e, TangentBundle.trivializationAt_baseSet]
        exact e.open_baseSet.mem_nhds hx₀
      · -- Smoothness: in `e`-coordinates, the section has constant fiber coordinate `v`.
        have hcoord : ContMDiffOn I 𝓘(ℝ, E) n∞ (fun x ↦ (e (⟨x, s_loc x⟩ : TangentBundle I M)).2)
            e.baseSet := by
          -- It suffices to show the coordinate map is (locally) equal to a constant function.
          refine (contMDiff_const.contMDiffOn : ContMDiffOn I 𝓘(ℝ, E) n∞ (fun _ : M => v) e.baseSet).congr
            (fun x hx => ?_)
          have hx_target : (x, v) ∈ e.target := by
            simpa [e, TangentBundle.trivializationAt_target, TangentBundle.trivializationAt_baseSet, hx]
          have hx_mk :
              (e.toPartialEquiv.symm (x, v) : TangentBundle I M) =
                ⟨x, (e.toPartialEquiv.symm (x, v)).2⟩ := by
            ext
            · -- `proj` of `e.symm (x,v)` is `x` on the target.
              simpa using (e.proj_symm_apply hx_target)
            · rfl
          have hx_mk' :
              (⟨x, s_loc x⟩ : TangentBundle I M) = e.toPartialEquiv.symm (x, v) := by
            simp [s_loc, hx_mk]
          -- Now compute in the trivialization.
          calc
            (e (⟨x, s_loc x⟩ : TangentBundle I M)).2 = (e (e.toPartialEquiv.symm (x, v))).2 := by
              simp [hx_mk']
            _ = (x, v).2 := by
              simpa using congrArg Prod.snd (e.apply_symm_apply hx_target)
            _ = v := rfl
        -- Convert to smoothness of the section on `e.baseSet`.
        exact ((e.contMDiffOn_section_baseSet_iff (IB := I) (n := n∞)).2 hcoord)
      · intro y hy
        by_cases hy' : y = x₀
        · subst y
          have hx₀_source : (⟨x₀, v₀⟩ : TangentBundle I M) ∈ e.source := by
            -- `e.source` is the preimage of the chart source under the bundle projection.
            simp [e, TangentBundle.trivializationAt_source]
          have he_pair : e (⟨x₀, v₀⟩ : TangentBundle I M) = (x₀, v) := by
            ext
            · simp [e]
            · rfl
          have hs_loc_x₀ : s_loc x₀ = v₀ := by
            -- `e.symm (e ⟨x₀,v₀⟩) = ⟨x₀,v₀⟩`.
            have : (e.toPartialEquiv.symm (x₀, v) : TangentBundle I M) = ⟨x₀, v₀⟩ := by
              calc
                (e.toPartialEquiv.symm (x₀, v) : TangentBundle I M) =
                    e.toPartialEquiv.symm (e (⟨x₀, v₀⟩ : TangentBundle I M)) := by
                  simp [he_pair]
                _ = (⟨x₀, v₀⟩ : TangentBundle I M) := by
                  simpa using (e.symm_apply_apply hx₀_source)
            simpa [s_loc] using! congrArg (fun z : TangentBundle I M => z.2) this
          simpa [t] using hs_loc_x₀
        · simp [t, hy']
    · -- If `p ≠ x₀`, choose a neighborhood avoiding `x₀` so the fiber constraint is vacuous.
      let e := trivializationAt E TM p
      let s_loc : (x : M) → TangentSpace I x := fun x => (e.toPartialEquiv.symm (x, (0 : E))).2
      let U : Set M := e.baseSet ∩ (Set.singleton x₀)ᶜ
      refine ⟨U, ?_, s_loc, ?_, ?_⟩
      · have hp_base : p ∈ e.baseSet := by
          simp [e, TangentBundle.trivializationAt_baseSet]
        have hp_ne : p ∈ (Set.singleton x₀)ᶜ := by
          simpa [Set.mem_compl_singleton_iff] using! hp
        have hU_open : IsOpen U := by
          simpa [U] using! e.open_baseSet.inter isOpen_compl_singleton
        exact hU_open.mem_nhds ⟨hp_base, hp_ne⟩
      · have hcoord : ContMDiffOn I 𝓘(ℝ, E) n∞
            (fun x ↦ (e (⟨x, s_loc x⟩ : TangentBundle I M)).2) e.baseSet := by
          refine (contMDiff_const.contMDiffOn : ContMDiffOn I 𝓘(ℝ, E) n∞ (fun _ : M => (0 : E)) e.baseSet).congr
            (fun x hx => ?_)
          have hx_target : (x, (0 : E)) ∈ e.target := by
            simpa [e, TangentBundle.trivializationAt_target, TangentBundle.trivializationAt_baseSet, hx]
          have hx_mk :
              (e.toPartialEquiv.symm (x, (0 : E)) : TangentBundle I M) =
                ⟨x, (e.toPartialEquiv.symm (x, (0 : E))).2⟩ := by
            ext
            · simpa using (e.proj_symm_apply hx_target)
            · rfl
          have hx_mk' :
              (⟨x, s_loc x⟩ : TangentBundle I M) = e.toPartialEquiv.symm (x, (0 : E)) := by
            simp [s_loc, hx_mk]
          calc
            (e (⟨x, s_loc x⟩ : TangentBundle I M)).2 =
                (e (e.toPartialEquiv.symm (x, (0 : E)))).2 := by
              simp [hx_mk']
            _ = (x, (0 : E)).2 := by
              simpa using congrArg Prod.snd (e.apply_symm_apply hx_target)
            _ = (0 : E) := rfl
        have hsmooth_base :
            ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ (fun x ↦ TotalSpace.mk' E x (s_loc x)) e.baseSet :=
          ((e.contMDiffOn_section_baseSet_iff (IB := I) (n := n∞)).2 hcoord)
        exact hsmooth_base.mono (by intro x hx; exact hx.1)
      · intro y hy
        have hy_ne : y ≠ x₀ := by
          exact (Set.mem_compl_singleton_iff.mp hy.2)
        simp [t, hy_ne]
  -- Global section from the convex-valued local data.
  have : IsManifold I (↑(⊤ : ℕ∞)) M :=
    IsManifold.of_le (I := I) (M := M) (hmn := (by simp : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ n∞))
  rcases
      exists_contMDiffSection_forall_mem_convex_of_local (I := I) (M := M) (E := E) (n := (⊤ : ℕ∞))
        (F_fiber := E) (V := TM) t ht_conv Hloc with
    ⟨s, hs⟩
  refine ⟨s, ?_⟩
  simpa [t] using hs x₀

end PrescribedValue

end SmoothTangentSection

end MathlibExtensions.Geometry.Manifold.VectorBundle
