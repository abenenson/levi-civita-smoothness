/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeviCivitaSmoothness.MetricApplication
public import MathlibExtensions.Geometry.Manifold.VectorBundle.LeviCivitaTangentExistenceTheorem

@[expose] public section

/-! # Transitive axiom checks for the original construction and smooth-pair bridge -/

open MathlibExtensions.Geometry.Manifold.VectorBundle.SmoothTangentSection

#print axioms exists_leviCivitaTangentConnectionFromMetric
#print axioms LeviCivitaSmoothness.eq_covDerivFromMetric_of_koszul
#print axioms LeviCivitaSmoothness.leviCivitaConnection_eq_covDerivFromMetric
#print axioms LeviCivitaSmoothness.contMDiff_leviCivitaConnection_smooth_pair
#print axioms LeviCivitaSmoothness.contMDiff_leviCivitaConnection_fromMetric
