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
# Total variation distance: `Riesz2.totalVariation`

The supremum of |μ(A)−ν(A)| over measurable events A, for finite measures. For probability
densities it is half the L¹ distance. This is the distance used in Theorem 3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The supremum of |μ(A)−ν(A)| over measurable events A, for finite measures. For probability
densities it is half the L¹ distance. This is the distance used in Theorem 3. -/
def totalVariation {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ≥0∞ :=
  ⨆ A : {A : Set Ω // MeasurableSet A},
    (μ A.val - ν A.val) + (ν A.val - μ A.val)

end Riesz2

end
end
