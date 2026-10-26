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
public import Riesz1.Frozen.ParticleNumber
public import Riesz2.Frozen.LineConfiguration
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.RestrictConfiguration
public import Riesz2.Frozen.TotalVariation

/-!
# Local total variation convergence: `Riesz2.LocalConverges`

Convergence of π_R#Q_{N,β} to π_R#P in total variation for every R > 0, as in Theorem 3. All
laws are probabilities. Positive particle numbers are indexed by n + 1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Convergence of π_R#Q_{N,β} to π_R#P in total variation for every R > 0, as in Theorem 3. All
laws are probabilities. Positive particle numbers are indexed by n + 1. -/
def LocalConverges (laws : ℕ+ → @Measure LineConfiguration configurationMeasurableSpace) (P : PointProcess) : Prop :=
  letI := configurationMeasurableSpace
  ∃ h : ∀ N, IsProbabilityMeasure (laws N),
    letI (N : ℕ+) : IsProbabilityMeasure (laws N) := h N
    ∀ R : ℝ, 0 < R →
    Tendsto (fun n : ℕ => totalVariation
      ((laws (Riesz1.particleNumber n)).map (restrictConfiguration (Icc (-R) R)))
      ((P : Measure LineConfiguration).map (restrictConfiguration (Icc (-R) R))))
      atTop (𝓝 0)

end Riesz2

end
end
