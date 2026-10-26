/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsNeumannRealization
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Gibbs potentials on a domain: `Riesz2.IsEuclideanGibbsPotential`

A potential V of the specified regularity with ρ = Z⁻¹e^{-V}σ on Ω and 0 < Z < ∞. For the
Euclidean laws of Subsections 3.1 and 3.4, σ is Lebesgue measure. Values outside Ω do not
enter the density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- A potential V of the specified regularity with ρ = Z⁻¹e^{-V}σ on Ω and 0 < Z < ∞. For the
Euclidean laws of Subsections 3.1 and 3.4, σ is Lebesgue measure. Values outside Ω do not
enter the density. -/
def IsEuclideanGibbsPotential {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] (σ ρ : Measure E)
    (Ω : Set E) (V : E → ℝ) (regularity : WithTop ℕ∞ := (⊤ : ℕ∞)) : Prop :=
  ContDiffOn ℝ regularity V Ω ∧
  let Z := ∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂σ.restrict Ω
  0 < Z ∧ Z < ⊤ ∧
    ρ = Z⁻¹ • (σ.restrict Ω).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))

end Riesz2

end
end
