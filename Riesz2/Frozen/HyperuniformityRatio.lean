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
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.IntervalCount
public import Riesz2.Frozen.NumberVariance

/-!
# Number variance per unit length: `Riesz2.hyperuniformityRatio`

The ratio Var_P[N_{(0,R]}]/R for R > 0, with integrability of the count as a hypothesis. Its
limit is zero for the long-range Riesz process in Corollary 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The ratio Var_P[N_{(0,R]}]/R for R > 0, with integrability of the count as a hypothesis. Its
limit is zero for the long-range Riesz process in Corollary 1.1. -/
def hyperuniformityRatio (P : PointProcess) (R : {R : ℝ // 0 < R})
    (h : letI := configurationMeasurableSpace; Integrable (intervalCount 0 R.val) (P : Measure LineConfiguration)) : ℝ≥0∞ :=
  letI := configurationMeasurableSpace
  numberVariance P R.val h / ENNReal.ofReal R.val

end Riesz2

end
end
