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
# Block comparison exponent: `Riesz2.exponentB`

The exponent b_s = min(s,1)/2 in the two-volume comparison of Proposition 6.6. Together with
a_s it gives the rate exponent in Theorem 4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The exponent b_s = min(s,1)/2 in the two-volume comparison of Proposition 6.6. Together with
a_s it gives the rate exponent in Theorem 4. -/
def exponentB (s : ℝ) : ℝ := min s 1 / 2

end Riesz2

end
end
