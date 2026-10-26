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
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.ShortGibbsWeight

/-!
# Short-range partition function: `Riesz2.shortPartitionFunction`

The partition integral Z_{N,β} = ∫ exp(−βH_N) dx for s > 1, with values in ℝ≥0∞. See
equation (1.3).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The partition integral Z_{N,β} = ∫ exp(−βH_N) dx for s > 1, with values in ℝ≥0∞. See
equation (1.3). -/
def shortPartitionFunction (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) : ℝ≥0∞ :=
  shortGibbsWeight β s N univ

end Riesz2

end
end
