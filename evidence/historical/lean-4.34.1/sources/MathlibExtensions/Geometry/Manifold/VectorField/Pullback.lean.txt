import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Extra lemmas for manifold vector-field pullbacks

This module provides small API extensions for `VectorField.mpullbackWithin` / `VectorField.mpullback`
that are convenient when lifting vector-space lemmas to manifolds.

## Main Results

- `VectorField.mpullbackWithin_smul_fun_apply`: pullback of a vector field scaled by a scalar
  function.
- `VectorField.mpullback_smul_fun_apply`: the corresponding lemma for `mpullback`.
-/

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f : M → M'} {s : Set M} {x : M}
  {V : Π x : M', TangentSpace I' x}

lemma mpullbackWithin_smul_fun_apply (c : M' → 𝕜) :
    mpullbackWithin I I' f (fun y ↦ c y • V y) s x =
      c (f x) • mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply, map_smul]

lemma mpullback_smul_fun_apply (c : M' → 𝕜) :
    mpullback I I' f (fun y ↦ c y • V y) x =
      c (f x) • mpullback I I' f V x := by
  simp [mpullback_apply, map_smul]

end VectorField

