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
public import Riesz1.Frozen.ConfigurationVolume
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.ShortEnergy

/-!
# Unnormalized short-range Gibbs law: `Riesz2.shortGibbsWeight`

The measure exp(−βH_N) dx for s > 1 on the configuration chart of `Riesz1`. Its
normalization gives the Gibbs law in equation (1.3).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The measure exp(−βH_N) dx for s > 1 on the configuration chart of `Riesz1`. Its
normalization gives the Gibbs law in equation (1.3). -/
def shortGibbsWeight (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    Measure (Riesz1.Configuration N) :=
  (Riesz1.configurationVolume N).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-β.val * shortEnergy s X)))

end Riesz2

end
end
