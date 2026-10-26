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
# Short-range Riesz exponent: `Riesz2.ShortExponent`

The exponent s > 1 of Subsection 1.1. The companion type `Riesz1.RieszExponent` covers 0 < s
< 1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The exponent s > 1 of Subsection 1.1. The companion type `Riesz1.RieszExponent` covers 0 < s
< 1. -/
@[reducible] def ShortExponent := {s : ℝ // 1 < s}

end Riesz2

end
end
