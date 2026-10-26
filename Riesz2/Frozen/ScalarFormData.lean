/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Scalar form domain and bilinear form: `Riesz2.ScalarFormData`

A subspace of L² together with a bilinear form on it. This encodes the scalar Dirichlet
forms of Subsections 3.1 and 4.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- A subspace of L² together with a bilinear form on it. This encodes the scalar Dirichlet
forms of Subsections 3.1 and 4.1. -/
@[reducible] def ScalarFormData {α : Type*} [MeasurableSpace α] (ρ : Measure α) :=
  Σ D : Submodule ℝ (Lp ℝ 2 ρ), D →ₗ[ℝ] D →ₗ[ℝ] ℝ

end Riesz2

end
end
