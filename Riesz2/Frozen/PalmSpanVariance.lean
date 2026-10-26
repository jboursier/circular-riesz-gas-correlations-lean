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
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.RootedPalmMeasure
public import Riesz2.Frozen.RootedPoint

/-!
# Variance of a Palm span: `Riesz2.palmSpanVariance`

The variance of z_K under the Palm law Riesz_{s,β}^0, with integrability of z_K as a proof
argument. See Corollary 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The variance of z_K under the Palm law Riesz_{s,β}^0, with integrability of z_K as a proof
argument. See Corollary 1.1. -/
def palmSpanVariance (P : PointProcess) (K : ℕ+)
    (h : letI := configurationMeasurableSpace; Integrable (fun C => rootedPoint C (K : ℕ)) (rootedPalmMeasure P)) : ℝ≥0∞ :=
  letI := configurationMeasurableSpace
  Riesz1.variance (rootedPalmMeasure P) (fun C => rootedPoint C (K : ℕ)) h

end Riesz2

end
end
