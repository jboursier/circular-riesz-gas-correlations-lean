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
# Exponent for the block size: `Riesz2.exponentA`

The exponent a_s = min(s/2,1) = min(s,2)/2 used to choose the block size in the proof of
Theorem 4 in Subsection 6.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The exponent a_s = min(s/2,1) = min(s,2)/2 used to choose the block size in the proof of
Theorem 4 in Subsection 6.3. -/
def exponentA (s : ℝ) : ℝ := min (s / 2) 1

end Riesz2

end
end
