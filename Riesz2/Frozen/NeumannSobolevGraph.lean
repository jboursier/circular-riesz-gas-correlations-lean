/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Closed Neumann gradient graph: `Riesz2.neumannSobolevGraph`

The closure in L² × L² of smooth value–gradient pairs defined near the domain closure. This
encodes the intrinsic Neumann H¹ graph in Subsections 3.1 and 4.1. An orthonormal affine
chart identifies it with the corresponding weighted Sobolev graph in `Riesz1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The closure in L² × L² of smooth value–gradient pairs defined near the domain closure. This
encodes the intrinsic Neumann H¹ graph in Subsections 3.1 and 4.1. An orthonormal affine
chart identifies it with the corresponding weighted Sobolev graph in `Riesz1`. -/
def neumannSobolevGraph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] (ρ : Measure E) (Ω : Set E) :
    Set (Lp ℝ 2 ρ × Lp E 2 ρ) :=
  closure {p | ∃ (f : E → ℝ) (hf : MemLp f 2 ρ)
      (hg : MemLp (gradient f) 2 ρ),
    (∃ U : Set E, IsOpen U ∧ closure Ω ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U) ∧
    p = (hf.toLp f, hg.toLp (gradient f))}

end Riesz2

end
end
