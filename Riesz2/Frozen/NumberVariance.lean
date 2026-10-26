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
public import Riesz1.Frozen.Variance
public import Riesz2.Frozen.LineConfiguration
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.IntervalCount

/-!
# Variance of particle counts: `Riesz2.numberVariance`

The extended centered square integral Var_P[N_{(0,R]}] from Corollary 1.1. Integrability of
the count is an explicit proof argument, as in the variance definition of `Riesz1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The extended centered square integral Var_P[N_{(0,R]}] from Corollary 1.1. Integrability of
the count is an explicit proof argument, as in the variance definition of `Riesz1`. -/
def numberVariance (P : PointProcess) (R : ℝ)
    (h : letI := configurationMeasurableSpace; Integrable (intervalCount 0 R) (P : Measure LineConfiguration)) : ℝ≥0∞ :=
  letI := configurationMeasurableSpace
  Riesz1.variance (P : Measure LineConfiguration) (intervalCount 0 R) h

end Riesz2

end
end
