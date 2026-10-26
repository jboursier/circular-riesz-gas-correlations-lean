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
public import Riesz2.Frozen.ConfigurationMeasurableSpace

/-!
# Point processes on the line: `Riesz2.PointProcess`

A probability law on Conf(ℝ), the simple locally finite configurations of Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- A probability law on Conf(ℝ), the simple locally finite configurations of Subsection 1.5. -/
@[reducible] def PointProcess :=
  letI := configurationMeasurableSpace
  ProbabilityMeasure LineConfiguration

end Riesz2

end
end
