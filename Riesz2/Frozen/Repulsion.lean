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
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.UniqueRieszLimit
public import Riesz2.Frozen.LimitingRieszProcess
public import Riesz2.Frozen.RepulsionProbability
import Riesz2.Main.Repulsion

/-!
# Repulsion of neighbouring particles: `Riesz2.repulsion`

For β > 0 and s ∈ (0,1) ∪ (1,+∞), the Palm gaps satisfy P(z_{i+1}−z_i ≤ u) ≤ C exp(−cu^{-s})
for every i ∈ ℤ and 0 < u ≤ 1. The constants c,C > 0 depend only on β and s. The statement
includes the limiting process and its Palm probability law.
This is Proposition 1.2 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), the Palm gaps satisfy P(z_{i+1}−z_i ≤ u) ≤ C exp(−cu^{-s})
for every i ∈ ℤ and 0 < u ≤ 1. The constants c,C > 0 depend only on β and s. The statement
includes the limiting process and its Palm probability law.
This is Proposition 1.2 of the paper. -/
theorem repulsion :
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    PalmRegular P ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
        repulsionProbability P i u ≤ ENNReal.ofReal (C * Real.exp (-c * u ^ (-p.val.2))) :=
  by exact Riesz2.Main.repulsion

end Riesz2

end
end
