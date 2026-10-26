/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# Convergence in law along a filter: `Riesz2.ConvergesInLawAlong`

Convergence of probability laws against every bounded continuous real test function, along a
filter. This allows the positive real radius R in Corollary 1.1. For natural indices it
agrees with `Riesz1.ConvergesInLaw`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Convergence of probability laws against every bounded continuous real test function, along a
filter. This allows the positive real radius R in Corollary 1.1. For natural indices it
agrees with `Riesz1.ConvergesInLaw`. -/
def ConvergesInLawAlong {ι : Type*} (l : Filter ι) (laws : ι → Measure ℝ)
    (limit : Measure ℝ) : Prop :=
  (∀ i, IsProbabilityMeasure (laws i)) ∧ IsProbabilityMeasure limit ∧
    ∀ f : ℝ →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂laws i) l (𝓝 (∫ x, f x ∂limit))

end Riesz2

end
end
