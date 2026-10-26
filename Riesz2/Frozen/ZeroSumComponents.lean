/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Zero-sum component subspace: `Riesz2.zeroSumComponents`

The subspace {u : ∑ᵢ uᵢ = 0} for the constrained weak equations in Lemma 4.6 and Subsection
5.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The subspace {u : ∑ᵢ uᵢ = 0} for the constrained weak equations in Lemma 4.6 and Subsection
5.1. -/
def zeroSumComponents (ι : Type*) [Fintype ι] : Submodule ℝ (ι → ℝ) :=
  { carrier := {z | ∑ i, z i = 0}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change (∑ i, (x i + y i)) = 0
      rw [Finset.sum_add_distrib, hx, hy, add_zero]
    smul_mem' := by
      intro a x hx
      change (∑ i, a * x i) = 0
      rw [← Finset.mul_sum, hx, mul_zero] }

end Riesz2

end
end
