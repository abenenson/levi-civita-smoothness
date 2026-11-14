/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Finite-dimensional tangent-space bookkeeping

This file collects small reusable lemmas transporting real finrank facts from a manifold model
space to each tangent fiber. In mathlib, `TangentSpace I x` is a type synonym for the model space
`E`, so these lemmas are thin wrappers around unfolding that synonym.

## Main results

- `tangentSpace_finrank_eq`
- `tangentSpace_finrank_eq_of_finrank_eq`
- `tangentSpace_finrank_eq_four`
- `tangentSpace_finrank_le_of_finrank_le`
- `tangentSpace_finrank_le_four`
-/

open scoped Manifold ContDiff

namespace MathlibExtensions.Geometry.Manifold.VectorBundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Tangent fibers are finite-dimensional when the model space is finite-dimensional. -/
instance instFiniteDimensionalTangentSpace [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) := by
  exact inferInstanceAs (FiniteDimensional ℝ E)

/-- Each tangent fiber has the same real finrank as the model space. -/
theorem tangentSpace_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := by
  rfl

/-- Transport an exact real finrank hypothesis from the model space to a tangent fiber. -/
theorem tangentSpace_finrank_eq_of_finrank_eq {n : ℕ}
    (h : Module.finrank ℝ E = n) (x : M) :
    Module.finrank ℝ (TangentSpace I x) = n := by
  simpa [TangentSpace] using! h

/-- Tangent fibers of a real `4`-dimensional model space have real finrank `4`. -/
theorem tangentSpace_finrank_eq_four
    (h4 : Module.finrank ℝ E = 4) (x : M) :
    Module.finrank ℝ (TangentSpace I x) = 4 :=
  tangentSpace_finrank_eq_of_finrank_eq (I := I) h4 x

/-- Transport a real finrank upper bound from the model space to a tangent fiber. -/
theorem tangentSpace_finrank_le_of_finrank_le {n : ℕ}
    (h : Module.finrank ℝ E ≤ n) (x : M) :
    Module.finrank ℝ (TangentSpace I x) ≤ n := by
  simpa [TangentSpace] using! h

/-- Tangent fibers of a model space with real finrank at most `4` also have finrank at most `4`. -/
theorem tangentSpace_finrank_le_four
    (h4 : Module.finrank ℝ E ≤ 4) (x : M) :
    Module.finrank ℝ (TangentSpace I x) ≤ 4 :=
  tangentSpace_finrank_le_of_finrank_le (I := I) h4 x

end MathlibExtensions.Geometry.Manifold.VectorBundle
