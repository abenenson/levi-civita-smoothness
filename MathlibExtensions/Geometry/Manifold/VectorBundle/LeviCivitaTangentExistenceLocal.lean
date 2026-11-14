/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentExistence
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionLocalDecomposition
public import MathlibExtensions.Geometry.Manifold.VectorBundle.TangentSectionPrescribedValue

@[expose] public section

/-!
# Levi–Civita existence: local smooth construction (Koszul)

This module contains the local smooth linear-algebra step in the Koszul-based construction of the
Levi–Civita connection on the tangent bundle.

The goal is to solve, locally and smoothly in `x`, the linear system that represents the Koszul
right-hand side against a local frame.
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
  [IsManifold I 1 M] [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]

local notation "TM" => (fun x : M => TangentSpace I x)
local notation "C∞" => C^n∞⟮I, M; ℝ⟯
local notation "Γ∞" => Cₛ^n∞⟮I; E, TM⟯

namespace SmoothTangentSection

section Gram

variable [FiniteDimensional ℝ E] [T2Space M]

omit [IsManifold I n∞ M] [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- If the given sections agree with a basis at the point, their Gram determinant for `g`
is nonzero there. -/
theorem det_gram_ne_zero_at_of_eq_basis
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) {x₀ : M}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x₀)) (s : ι → Γ∞)
    (hs : ∀ i, s i x₀ = b i) :
    Matrix.det
        (fun i j =>
          smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j) x₀) ≠ 0 := by
  classical
  let B : LinearMap.BilinForm ℝ (TangentSpace I x₀) :=
    metricBilinForm (I := I) (M := M) (E := E) g x₀
  have hB : B.Nondegenerate :=
    metricBilinForm_nondegenerate (I := I) (M := M) (E := E) (g := g) x₀
  have hdetB : ((LinearMap.BilinForm.toMatrix b) B).det ≠ 0 := by
    have hdetB' : ((LinearMap.BilinForm.toMatrix b) B).det ≠ (0 : ℝ) :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (B := B) b).1 hB
    simpa using hdetB'
  have hMat :
      (fun i j =>
          smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j) x₀) =
        fun i j => B (b i) (b j) := by
    funext i j
    simp [B, smoothTangentSectionInnerFromMetric_apply, metricBilinForm_apply, hs]
  have hMatB : (LinearMap.BilinForm.toMatrix b) B = fun i j => B (b i) (b j) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  have hdetB' : Matrix.det (fun i j => B (b i) (b j)) ≠ 0 := by
    simpa [hMatB] using hdetB
  have hdetEq :
      Matrix.det
          (fun i j =>
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j) x₀) =
        Matrix.det (fun i j => B (b i) (b j)) :=
    congrArg Matrix.det hMat
  rw [hdetEq]
  exact hdetB'

end Gram

section LocalFrame

variable [FiniteDimensional ℝ E] [T2Space M]

omit [IsManifold I (minSmoothness ℝ 2) M] [CompleteSpace E] in
/-- Build a finite family of smooth tangent sections whose Gram determinant (for `g`) is nonzero at
`x₀`. This is the local linear algebra input for solving the Koszul system smoothly near `x₀`. -/
theorem exists_frame_det_gram_ne_zero_at
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (x₀ : M) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (s : ι → Γ∞),
      Matrix.det
          (fun i j =>
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j) x₀) ≠ 0 := by
  classical
  let ι : Type := Fin (Module.finrank ℝ (TangentSpace I x₀))
  let b : Module.Basis ι ℝ (TangentSpace I x₀) := Module.finBasis ℝ (TangentSpace I x₀)
  let wE : ι → E :=
    fun i => (trivializationAt E TM x₀ (⟨x₀, b i⟩ : TangentBundle I M)).2
  have hs_exists :
      ∀ i : ι, ∃ s : Γ∞, ∀ᶠ x in 𝓝 x₀, s x = localConst (I := I) (M := M) (E := E) x₀ (wE i) x :=
    fun i => exists_eq_localConst_nhds (I := I) (M := M) (E := E) x₀ (wE i)
  choose s hs using hs_exists
  have hsx₀ : ∀ i : ι, s i x₀ = b i := by
    intro i
    have hEq :
        (fun x : M => s i x) =ᶠ[𝓝 x₀]
          fun x => localConst (I := I) (M := M) (E := E) x₀ (wE i) x :=
      hs i
    have hEq₀ : s i x₀ = localConst (I := I) (M := M) (E := E) x₀ (wE i) x₀ :=
      Filter.EventuallyEq.eq_of_nhds hEq
    have hLC : localConst (I := I) (M := M) (E := E) x₀ (wE i) x₀ = b i := by
      simpa [wE] using
        localConst_apply_self (I := I) (M := M) (E := E) (x₀ := x₀) (v₀ := b i)
    exact hEq₀.trans hLC
  refine ⟨ι, inferInstance, inferInstance, s, ?_⟩
  simpa using
    det_gram_ne_zero_at_of_eq_basis (I := I) (M := M) (E := E) (g := g) (x₀ := x₀) (b := b)
      (s := s) hsx₀

end LocalFrame

section LocalSolve

variable [FiniteDimensional ℝ E] [T2Space M]

/-- Local smooth solver for the Koszul system on a *fixed* finite family of sections with
non-vanishing Gram determinant at `x₀`. -/
theorem exists_koszulRHSInner_nhds_on_frame_of_det
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) (x₀ : M)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Γ∞)
    (hdet :
      Matrix.det
          (fun i j =>
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j) x₀) ≠ 0) :
    ∃ (W : Γ∞),
      ∀ i : ι,
        ∀ᶠ x in 𝓝 x₀,
          (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
            (2 : ℝ) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
  classical
  -- Gram matrix and Koszul RHS vector.
  let A : Matrix ι ι C∞ :=
    fun i j => smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j)
  let rhs : ι → C∞ :=
    fun j => koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s j)
  let half : C∞ := ⟨fun _ : M => (1 / 2 : ℝ), contMDiff_const⟩
  let rhsHalf : ι → C∞ := fun j => half * rhs j
  let detA : C∞ := A.det
  -- Neighborhood where `detA` is nonzero.
  let U : Set M := {x | detA x ≠ 0}
  have hdetA0 : detA x₀ ≠ 0 := by
    -- Evaluate `detA` at `x₀` using the ring hom `ContMDiffMap.evalRingHom`.
    let ev : C∞ →+* ℝ :=
      ContMDiffMap.evalRingHom (I := I) (I' := 𝓘(ℝ, ℝ)) (n := n∞) (N := M) (m := x₀)
    have hdet_ev : ev detA = Matrix.det (fun i j => ev (A i j)) := by
      simpa [detA] using! (RingHom.map_det ev A)
    have hdet_ne : ev detA ≠ 0 := by
      have : Matrix.det (fun i j => ev (A i j)) ≠ 0 := by
        simpa [A, ev, ContMDiffMap.evalRingHom] using hdet
      exact hdet_ev ▸ this
    simpa [ev, ContMDiffMap.evalRingHom] using hdet_ne
  have hU : U ∈ 𝓝 x₀ := by
    have hcont : Continuous fun x : M => detA x :=
      ContMDiff.continuous detA.2
    have hopen : IsOpen U := isOpen_ne_fun hcont continuous_const
    exact hopen.mem_nhds hdetA0
  -- Choose a smooth bump function `f` with `tsupport f ⊆ U`.
  rcases (SmoothBumpFunction.nhds_basis_support (I := I) (c := x₀) hU).mem_iff.1
      (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 x₀) with
    ⟨f, hfU, -⟩
  -- Smoothness of `detA⁻¹` on `U`.
  have hinvDet : ContMDiffOn I 𝓘(ℝ, ℝ) n∞ (fun x : M => (detA x)⁻¹) U := by
    refine ContMDiffOn.inv₀ (I' := I) (I := 𝓘(ℝ, ℝ)) (n := n∞) (f := fun x : M => detA x)
        (s := U) detA.2.contMDiffOn ?_
    intro x hx
    exact hx
  -- Smooth coefficients on `U` via Cramer's rule.
  let coeff : ι → M → ℝ :=
    fun i x => (A.cramer rhsHalf i) x * (detA x)⁻¹
  have hcoeff : ∀ i : ι, ContMDiffOn I 𝓘(ℝ, ℝ) n∞ (coeff i) U := by
    intro i
    have hnum :
        ContMDiffOn I 𝓘(ℝ, ℝ) n∞ (fun x : M => (A.cramer rhsHalf i) x) U :=
      (A.cramer rhsHalf i).2.contMDiffOn
    simpa [coeff, mul_assoc] using! hnum.mul hinvDet
  -- Local solution section (smooth on `U`).
  let Wlocal : (x : M) → TangentSpace I x :=
    fun x => ∑ i, (coeff i x) • s i x
  have hWlocal :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
        (fun x ↦ TotalSpace.mk' E x (Wlocal x)) U := by
    classical
    have hsOn :
        ∀ i : ι,
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞ (fun x ↦ TotalSpace.mk' E x (s i x)) U := by
      intro i
      exact (s i).contMDiff.contMDiffOn
    have hterm :
        ∀ i : ι,
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) n∞
            (fun x ↦ TotalSpace.mk' E x ((coeff i x) • s i x)) U := by
      intro i
      exact (hcoeff i).smul_section (hsOn i)
    -- Sum over the finite index type.
    simpa [Wlocal] using
      (ContMDiffOn.sum_section (I := I) (n := n∞) (F := E) (V := TM) (u := U)
        (t := fun i => fun x => (coeff i x) • s i x) (s := (Finset.univ : Finset ι))
        (hs := by
          intro i hi
          simpa using hterm i))
  -- Globalize the local section using the bump function.
  have hψ_cont : ContMDiffOn I 𝓘(ℝ, ℝ) n∞ (fun x : M => (f x : ℝ)) U :=
    (SmoothBumpFunction.contMDiff (I := I) (f := f)).contMDiffOn
  have hU_open : IsOpen U := by
    have hcont : Continuous fun x : M => detA x :=
      ContMDiff.continuous detA.2
    simpa [U] using (isOpen_ne_fun hcont continuous_const)
  have hs_mul :
      ContMDiff I (I.prod 𝓘(ℝ, E)) n∞
        (fun x ↦ TotalSpace.mk' E x ((f x : ℝ) • Wlocal x)) := by
    simpa using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (n := n∞) (F := E) (V := TM)
        (u := U) (s := Wlocal) (ψ := fun x : M => (f x : ℝ))
        hψ_cont hU_open hfU hWlocal)
  let W : Γ∞ := ⟨fun x => (f x : ℝ) • Wlocal x, hs_mul⟩
  refine ⟨W, ?_⟩
  intro i
  -- Work on the neighborhood where `f = 1`.
  filter_upwards [f.eventuallyEq_one] with x hx1
  have hx_tsupport : x ∈ tsupport (fun y : M => (f y : ℝ)) := by
    have hx_support : x ∈ Function.support (fun y : M => (f y : ℝ)) := by
      simp [Function.support, hx1]
    exact subset_closure hx_support
  have hxU : x ∈ U := hfU hx_tsupport
  have hdetx : detA x ≠ 0 := hxU
  have hWx : W x = Wlocal x := by
    simp [W, Wlocal, hx1]
  -- Cramer's rule in `C∞`, evaluated at `x`.
  have hcr : A.mulVec (fun j => A.cramer rhsHalf j) = detA • rhsHalf := by
    change A.mulVec (fun j => A.cramer rhsHalf j) = A.det • rhsHalf
    exact Matrix.mulVec_cramer (A := A) (b := rhsHalf)
  have hcrx :
      (∑ j, (A i j x) * ((A.cramer rhsHalf j) x)) = detA x * rhsHalf i x := by
    have h0 := congrArg (fun v => (v i) x) hcr
    have h0' :
        (∑ j, (A i j * A.cramer rhsHalf j)) x = detA x * rhsHalf i x := by
      simpa [Matrix.mulVec, dotProduct] using h0
    have hsum :
        (∑ j, (A i j * A.cramer rhsHalf j)) x =
          ∑ j, (A i j x) * ((A.cramer rhsHalf j) x) := by
      let evx : C∞ →+* ℝ :=
        ContMDiffMap.evalRingHom (I := I) (I' := 𝓘(ℝ, ℝ)) (n := n∞) (N := M) (m := x)
      have hmap :
          evx (∑ j, A i j * A.cramer rhsHalf j) =
            ∑ j, evx (A i j * A.cramer rhsHalf j) := by
        classical
        exact map_sum evx (fun j => A i j * A.cramer rhsHalf j) Finset.univ
      calc
        (∑ j, A i j * A.cramer rhsHalf j) x
            = evx (∑ j, A i j * A.cramer rhsHalf j) := rfl
        _ = ∑ j, evx (A i j * A.cramer rhsHalf j) := hmap
        _ = ∑ j, (A i j x) * ((A.cramer rhsHalf j) x) := by
              simp [evx, ContMDiffMap.evalRingHom, map_mul]
    simpa [hsum] using h0'
  -- Solve for the inner products with `s i`.
  have hsolve :
      (∑ j, (A i j x) * (coeff j x)) = rhsHalf i x := by
    -- Multiply the Cramer identity by `detA x` inverse.
    have h1 :
        (∑ j, (A i j x) * ((A.cramer rhsHalf j) x)) * (detA x)⁻¹ =
          (detA x * rhsHalf i x) * (detA x)⁻¹ := by
      simp [hcrx]
    have h2 :
        (detA x * rhsHalf i x) * (detA x)⁻¹ = rhsHalf i x := by
      calc
        (detA x * rhsHalf i x) * (detA x)⁻¹
            = detA x * (rhsHalf i x * (detA x)⁻¹) := by simp [mul_assoc]
        _ = detA x * ((detA x)⁻¹ * rhsHalf i x) := by simp [mul_comm]
        _ = (detA x * (detA x)⁻¹) * rhsHalf i x := by simp [mul_assoc]
        _ = rhsHalf i x := by simp [hdetx]
    -- Push `(detA x)⁻¹` into the sum and rewrite using `coeff`.
    have hsum :
        (∑ j, (A i j x) * ((A.cramer rhsHalf j) x)) * (detA x)⁻¹ =
          ∑ j, (A i j x) * (coeff j x) := by
      classical
      simp [coeff, mul_assoc, Finset.sum_mul]
    exact (hsum ▸ (h1.trans (by simp [h2])))
  -- Compute `⟪W, s i⟫ x` using symmetry and linearity in the second slot.
  have hinner :
      smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x = rhsHalf i x := by
    have hsymm :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) W x := by
      simpa using congrArg (fun (F : C∞) => F x)
        (smoothTangentSectionInnerFromMetric_symm (I := I) (M := M) (g := g) W (s i))
    -- Expand the right-hand side using `W x = Wlocal x`.
    have hlin :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) W x =
          ∑ j, (coeff j x) * (A i j x) := by
      simp [smoothTangentSectionInnerFromMetric_apply, A, W, Wlocal, hWx, map_sum, map_smul,
        smul_eq_mul, mul_comm]
    have hlin' :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) W x =
          ∑ j, (A i j x) * (coeff j x) := by
      classical
      simpa [mul_comm] using hlin
    have : smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) W x = rhsHalf i x :=
      hlin'.trans hsolve
    exact hsymm.trans this
  -- Clear the factor `1/2`.
  have hrhs :
      rhs i x = (2 : ℝ) * rhsHalf i x := by
    have hHalf : rhsHalf i x = (1 / 2 : ℝ) * rhs i x := rfl
    rw [hHalf]
    ring
  calc
    rhs i x = (2 : ℝ) * rhsHalf i x := hrhs
    _ =
        (2 : ℝ) *
          smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
            simp [hinner]

/-- Local smooth linear-algebra step: near any `x₀`, solve the Koszul system against a finite
family of sections, producing a smooth section `W` whose inner products against that family match
the Koszul right-hand side. -/
theorem exists_koszulRHSInner_nhds_on_frame
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) (x₀ : M) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (s : ι → Γ∞) (W : Γ∞),
      ∀ i : ι,
        ∀ᶠ x in 𝓝 x₀,
          (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
            (2 : ℝ) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
  classical
  -- Choose a smooth frame with invertible Gram determinant at `x₀`.
  rcases exists_frame_det_gram_ne_zero_at (I := I) (M := M) (E := E) (g := g) x₀ with
    ⟨ι, instF, instD, s, hdet⟩
  classical
  rcases
      exists_koszulRHSInner_nhds_on_frame_of_det (I := I) (M := M) (E := E) (g := g)
        (X := X) (Y := Y) (x₀ := x₀) (s := s) hdet with
    ⟨W, hW⟩
  exact ⟨ι, instF, instD, s, W, hW⟩

/-- Local existence in the Koszul construction: near `x₀`, the Koszul RHS (linear in the third slot)
is represented by inner product with some smooth section `W`. -/
theorem exists_koszulRHSInner_nhds
    (g : Bundle.ContMDiffRiemannianMetric I n∞ E TM) (X Y : Γ∞) (x₀ : M) :
    ∃ W : Γ∞,
      ∀ Z : Γ∞,
        ∀ᶠ x in 𝓝 x₀,
          (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x =
            (2 : ℝ) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W Z x := by
  classical
  -- Choose a fixed finite family `s i` that is locally the `localConst` finBasis frame, and that
  -- locally spans every tangent section with smooth coefficients.
  rcases
      SmoothTangentSection.exists_localConst_finBasis_nhds (I := I) (M := M) (E := E) x₀ with
    ⟨s, hs, hdecomp⟩
  -- Show the Gram determinant at `x₀` is nonzero for this family.
  let e := trivializationAt E TM x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    change x₀ ∈ (trivializationAt E TM x₀).baseSet
    simp [TangentBundle.trivializationAt_baseSet]
  let φ₀ := (e.continuousLinearEquivAt (R := ℝ) x₀ hx₀)
  let bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    bE.map (φ₀.symm.toLinearEquiv)
  have hsx₀ : ∀ i, s i x₀ = b i := by
    intro i
    have hs0 :
        s i x₀ =
          localConst (I := I) (M := M) (E := E) x₀ (bE i) x₀ :=
      (hs i).self_of_nhds
    have hlocalConst :
        localConst (I := I) (M := M) (E := E) x₀ (bE i) x₀ = φ₀.symm (bE i) := by
      apply φ₀.injective
      have hφ₀_localConst :
          φ₀ (localConst (I := I) (M := M) (E := E) x₀ (bE i) x₀) = bE i := by
        -- unfold `φ₀` as the trivialization coordinate map
        simpa [φ₀, e] using
          (localConst_trivializationAt_snd (I := I) (M := M) (E := E) (x₀ := x₀) (w := bE i)
            (x := x₀) hx₀)
      have hφ₀_symm : φ₀ (φ₀.symm (bE i)) = bE i := by simp
      simp [hφ₀_localConst, hφ₀_symm]
    -- rewrite `b` and finish
    have : φ₀.symm (bE i) = b i := by
      rfl
    simpa [this] using hs0.trans hlocalConst
  have hdet :
      Matrix.det
          (fun i j =>
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) (s i) (s j) x₀) ≠ 0 :=
    det_gram_ne_zero_at_of_eq_basis (I := I) (M := M) (E := E) (g := g) (x₀ := x₀) (b := b)
      (s := s) hsx₀
  -- Solve the Koszul system smoothly near `x₀` on this fixed family.
  rcases
      exists_koszulRHSInner_nhds_on_frame_of_det (I := I) (M := M) (E := E) (g := g)
        (X := X) (Y := Y) (x₀ := x₀) (s := s) hdet with
    ⟨W, hW⟩
  refine ⟨W, ?_⟩
  intro Z
  rcases hdecomp Z with ⟨a, hZa⟩
  let Zsum : Γ∞ := ∑ i : Fin (Module.finrank ℝ E), a i • s i
  -- Pointwise congruence for `koszulRHSLinear` under equality of section values.
  have hkoszul_congr (x : M) {Z Z' : Γ∞} (hZZ' : Z x = Z' x) :
      (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x =
        (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z') x := by
    rcases
        SmoothTangentSection.exists_eval_eq_linear_apply (I := I) (M := M) (E := E) x
          (koszulRHSLinear (I := I) (M := M) (E := E) g X Y) with
      ⟨ℓ, hℓ⟩
    simp [hℓ, hZZ']
  have hkoszul_eq :
      ∀ᶠ x in 𝓝 x₀,
        (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Z) x =
          (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Zsum) x :=
    hZa.mono (fun x hx => hkoszul_congr (x := x) hx)
  have hinner_eq :
      ∀ᶠ x in 𝓝 x₀,
        smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W Z x =
          smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W Zsum x :=
    hZa.mono (fun x hx => by
      simp [smoothTangentSectionInnerFromMetric_apply, hx, Zsum])
  -- Expand on the finite sum and use the frame identities from `hW`.
  have hW_all :
      ∀ᶠ x in 𝓝 x₀,
        ∀ i : Fin (Module.finrank ℝ E),
          (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
            (2 : ℝ) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
    simpa using Filter.eventually_all.2 hW
  have hsum :
      ∀ᶠ x in 𝓝 x₀,
        (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Zsum) x =
          (2 : ℝ) *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W Zsum x := by
    filter_upwards [hW_all] with x hx
    -- LHS: use `C∞`-linearity in the third slot.
    have hL :
        (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Zsum) x =
          ∑ i : Fin (Module.finrank ℝ E), (a i x) * (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x := by
      classical
      let φ := koszulRHSLinear (I := I) (M := M) (E := E) g X Y
      let evx : C∞ →+* ℝ :=
        ContMDiffMap.evalRingHom (I := I) (I' := 𝓘(ℝ, ℝ)) (n := n∞) (N := M) (m := x)
      have hφ :
          φ Zsum = ∑ i : Fin (Module.finrank ℝ E), a i * φ (s i) := by
        simp [Zsum, φ, map_sum, map_smul, smul_eq_mul]
      calc
        (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Zsum) x
            = evx (φ Zsum) := rfl
        _ = evx (∑ i : Fin (Module.finrank ℝ E), a i * φ (s i)) := by
              simp [hφ]
        _ = ∑ i : Fin (Module.finrank ℝ E), evx (a i * φ (s i)) := by
              classical
              exact map_sum evx (fun i : Fin (Module.finrank ℝ E) => a i * φ (s i)) Finset.univ
        _ = ∑ i : Fin (Module.finrank ℝ E), (a i x) * (φ (s i) x) := by
              simp [evx, ContMDiffMap.evalRingHom, map_mul]
    -- RHS: linearity of the inner product in the second slot.
    have hR :
        smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W Zsum x =
          ∑ i : Fin (Module.finrank ℝ E), (a i x) *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
      classical
      -- Evaluate the section sum at `x` explicitly.
      let eval : Γ∞ →+ TangentSpace I x :=
        { toFun := fun Z => Z x
          map_zero' := by simp
          map_add' := by intro Z W; simp }
      have hZsumx : Zsum x = ∑ i : Fin (Module.finrank ℝ E), (a i x) • (s i x) := by
        have hs' :
            eval (∑ i : Fin (Module.finrank ℝ E), a i • s i) =
              ∑ i : Fin (Module.finrank ℝ E), eval (a i • s i) := by
          exact map_sum eval (fun i : Fin (Module.finrank ℝ E) => a i • s i) Finset.univ
        change eval (∑ i : Fin (Module.finrank ℝ E), a i • s i) =
          ∑ i : Fin (Module.finrank ℝ E), (a i x) • (s i x)
        calc
          eval (∑ i : Fin (Module.finrank ℝ E), a i • s i) =
              ∑ i : Fin (Module.finrank ℝ E), eval (a i • s i) := hs'
          _ = ∑ i : Fin (Module.finrank ℝ E), (a i x) • (s i x) := by
              simp [eval, smul_apply]
      -- Now use linearity of the continuous linear map `g.inner x (W x)` on the fiber.
      simp [smoothTangentSectionInnerFromMetric_apply, hZsumx, map_sum, map_smul]
    -- Combine and use the frame identities `hx`.
    have hx' :
        ∀ i : Fin (Module.finrank ℝ E),
          (a i x) * (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x =
            (a i x) * ((2 : ℝ) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x) :=
      fun i => congrArg (fun t : ℝ => (a i x) * t) (hx i)
    calc
      (koszulRHSLinear (I := I) (M := M) (E := E) g X Y Zsum) x
          = ∑ i : Fin (Module.finrank ℝ E), (a i x) *
              (koszulRHSLinear (I := I) (M := M) (E := E) g X Y (s i)) x := hL
      _ = ∑ i : Fin (Module.finrank ℝ E), (a i x) *
            ((2 : ℝ) *
              smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x) := by
            classical
            simp [hx']
      _ = (2 : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E), (a i x) *
            smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W (s i) x := by
            classical
            simp [Finset.mul_sum, mul_left_comm]
      _ = (2 : ℝ) *
          smoothTangentSectionInnerFromMetric (I := I) (M := M) (g := g) W Zsum x := by
            simp [hR]
  filter_upwards [hkoszul_eq, hinner_eq, hsum] with x hk hi hs
  simpa [hk, hi] using hs

end LocalSolve

end SmoothTangentSection

end

end MathlibExtensions.Geometry.Manifold.VectorBundle
