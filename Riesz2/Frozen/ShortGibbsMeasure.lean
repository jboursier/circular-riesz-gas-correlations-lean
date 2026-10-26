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
public import Riesz1.Frozen.Configuration
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.ShortGibbsWeight
public import Riesz2.Frozen.ShortPartitionFunction

/-!
# Gibbs law of the short-range gas: `Riesz2.shortGibbsMeasure`

The law G_{N,β} = Z_{N,β}⁻¹ exp(−βH_N) dx for s > 1, as in equation (1.3). Positivity and
finiteness of the normalizer are proved analytically.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The law G_{N,β} = Z_{N,β}⁻¹ exp(−βH_N) dx for s > 1, as in equation (1.3). Positivity and
finiteness of the normalizer are proved analytically. -/
def shortGibbsMeasure (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    Measure (Riesz1.Configuration N) :=
  (shortPartitionFunction β s N)⁻¹ • shortGibbsWeight β s N

end Riesz2

end
end
