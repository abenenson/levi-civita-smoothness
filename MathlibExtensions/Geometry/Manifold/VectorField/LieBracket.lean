/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

public import MathlibExtensions.Geometry.Manifold.VectorField.Pullback

@[expose] public section

/-!
# Extra lemmas for manifold vector-field Lie brackets

This module adds a small API extension for `VectorField.mlieBracket`: a Leibniz/product rule when
scaling a vector field by a scalar function on the manifold.

## Main Results

- `VectorField.mlieBracket_smul_fun_right`: `[V, c • W] = (dc(V)) • W + c • [V, W]` (pointwise).
- `VectorField.mlieBracket_smul_fun_left`: `[c • V, W] = -(dc(W)) • V + c • [V, W]` (pointwise).
-/

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "I𝕜" => 𝓘(𝕜, 𝕜)

section

variable [IsManifold I 2 M] [CompleteSpace E]
  {V W : Π x : M, TangentSpace I x} {c : M → 𝕜} {x : M}

/-- Pointwise Lie-bracket product rule for scaling the second field, using the supplied
differentiability of the scalar function and the second field. -/
lemma mlieBracket_smul_fun_right
    (hc : MDifferentiableAt I I𝕜 c x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) :
    mlieBracket I V (fun y ↦ c y • W y) x =
      (mvfderiv I c x) (V x) • W x + c x • mlieBracket I V W x := by
  exact mlieBracket_smul_right (I := I) (V := V) (W := W) (f := c) hc hW

/-- Pointwise Lie-bracket product rule for scaling the first field, using the supplied
differentiability of the scalar function and the first field. -/
lemma mlieBracket_smul_fun_left
    (hc : MDifferentiableAt I I𝕜 c x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x) :
    mlieBracket I (fun y ↦ c y • V y) W x =
      - (mvfderiv I c x) (W x) • V x + c x • mlieBracket I V W x := by
  exact mlieBracket_smul_left (I := I) (V := V) (W := W) (f := c) hc hV

end

end VectorField
