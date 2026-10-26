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

/-!
# Mesoscopic sequences of gap spans: `Riesz2.IsMesoscopicSequence`

A sequence of positive integers n_N with n_N → ∞ and n_N/N → 0, as in Theorem 1. The
indexing is by the particle number.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- A sequence of positive integers n_N with n_N → ∞ and n_N/N → 0, as in Theorem 1. The
indexing is by the particle number. -/
def IsMesoscopicSequence (n : ℕ+ → ℕ+) : Prop :=
  Tendsto (fun m : ℕ => ((n (Riesz1.particleNumber m) : ℕ))) atTop atTop ∧
  Tendsto (fun m : ℕ => (n (Riesz1.particleNumber m) : ℝ) /
    (Riesz1.particleNumber m : ℝ)) atTop (𝓝 0)

end Riesz2

end
end
