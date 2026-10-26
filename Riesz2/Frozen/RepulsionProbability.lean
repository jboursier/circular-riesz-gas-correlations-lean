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
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.RootedGap
public import Riesz2.Frozen.RootedPalmMeasure

/-!
# Probability of a small Palm gap: `Riesz2.repulsionProbability`

The event mass P(z_{i+1}−z_i ≤ u) on the rooted Palm carrier. It is a probability when the
Palm regularity conclusions hold. See Proposition 1.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The event mass P(z_{i+1}−z_i ≤ u) on the rooted Palm carrier. It is a probability when the
Palm regularity conclusions hold. See Proposition 1.2. -/
def repulsionProbability (P : PointProcess) (i : ℤ) (u : ℝ) : ℝ≥0∞ :=
  letI := configurationMeasurableSpace
  rootedPalmMeasure P {C | rootedGap C i ≤ u}

end Riesz2

end
end
