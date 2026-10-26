/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ScalarFormData
public import Riesz2.Frozen.NeumannSobolevGraph

/-!
# Neumann realization of a scalar form: `Riesz2.IsNeumannRealization`

A scalar form whose domain is the full closed intrinsic gradient graph, with unique L²
gradients and energy equal to their L² inner product. This encodes the Neumann H¹ form used
in Subsections 3.1 and 4.1. Comparison with the particle form in `Riesz1` also requires its
periodic domain and quotient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- A scalar form whose domain is the full closed intrinsic gradient graph, with unique L²
gradients and energy equal to their L² inner product. This encodes the Neumann H¹ form used
in Subsections 3.1 and 4.1. Comparison with the particle form in `Riesz1` also requires its
periodic domain and quotient. -/
def IsNeumannRealization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] {ρ : Measure E}
    (Ω : Set E) (Q : ScalarFormData ρ) : Prop :=
  (∀ f : Lp ℝ 2 ρ, f ∈ Q.1 ↔ ∃ g : Lp E 2 ρ, (f, g) ∈ neumannSobolevGraph ρ Ω) ∧
  (∀ (f : Lp ℝ 2 ρ) (g h : Lp E 2 ρ),
    (f, g) ∈ neumannSobolevGraph ρ Ω → (f, h) ∈ neumannSobolevGraph ρ Ω → g = h) ∧
  (∀ (f h : Q.1) (g k : Lp E 2 ρ),
    (f.val, g) ∈ neumannSobolevGraph ρ Ω →
    (h.val, k) ∈ neumannSobolevGraph ρ Ω → Q.2 f h = inner ℝ g k)

end Riesz2

end
end
