/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic

/-!
# Tangent space of the gap simplex: `Riesz2.gapTangentSpace`

The Euclidean subspace 1⊥ = {z : ∑ᵢ zᵢ = 0}, which is the direction space of the mass-N
simplex 𝓜_N in Subsection 3.2. It carries the induced Euclidean norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The Euclidean subspace 1⊥ = {z : ∑ᵢ zᵢ = 0}, which is the direction space of the mass-N
simplex 𝓜_N in Subsection 3.2. It carries the induced Euclidean norm. -/
@[reducible] def gapTangentSpace (N : ℕ+) : Submodule ℝ (EuclideanSpace ℝ (Fin (N : ℕ))) :=
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
