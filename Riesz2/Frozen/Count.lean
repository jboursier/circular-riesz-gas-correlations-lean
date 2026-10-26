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
public import Riesz2.Frozen.LineConfiguration

/-!
# Number of particles in a set: `Riesz2.count`

The count N_B(𝓒) = #(𝓒 ∩ B) from Subsection 1.5, with values in ℝ≥0∞. Counts on unbounded
sets may be infinite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The count N_B(𝓒) = #(𝓒 ∩ B) from Subsection 1.5, with values in ℝ≥0∞. Counts on unbounded
sets may be infinite. -/
def count (C : LineConfiguration) (B : Set ℝ) : ℝ≥0∞ := (C.val ∩ B).encard

end Riesz2

end
end
