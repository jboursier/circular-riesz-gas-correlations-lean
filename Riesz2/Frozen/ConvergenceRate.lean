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
public import Riesz2.Frozen.ExponentA
public import Riesz2.Frozen.ExponentB

/-!
# Exponent of the convergence rate: `Riesz2.convergenceRate`

The exponent r_s = a_s b_s = min(s,2) min(s,1)/4 in the rate N^{-r_s+ε} of Theorem 4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The exponent r_s = a_s b_s = min(s,2) min(s,1)/4 in the rate N^{-r_s+ε} of Theorem 4. -/
def convergenceRate (s : ℝ) : ℝ := exponentA s * exponentB s

end Riesz2

end
end
