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
public import Riesz2.Thermodynamic.RepulsionResult
public import Riesz2.Frozen.OrdinaryGapCauchy
public import Riesz2.ToMathlib.External.LogConcaveConvergenceResult

/-!
# Proof of repulsion of neighbouring particles

For β > 0 and s ∈ (0,1) ∪ (1,+∞), the Palm gaps satisfy P(z_{i+1}−z_i ≤ u) ≤ C exp(−cu^{-s})
for every i ∈ ℤ and 0 < u ≤ 1. The constants c,C > 0 depend only on β and s. The statement
includes the limiting process and its Palm probability law.
This is Proposition 1.2 of the paper. The proof specializes `Riesz2.repulsion_locallyUniform` to a singleton temperature
interval and uses convergence of log-concave densities.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2.Main

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), the Palm gaps satisfy P(z_{i+1}−z_i ≤ u) ≤ C exp(−cu^{-s})
for every i ∈ ℤ and 0 < u ≤ 1. The constants c,C > 0 depend only on β and s. The statement
includes the limiting process and its Palm probability law.
This is Proposition 1.2 of the paper. -/
theorem repulsion :
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    PalmRegular P ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
        repulsionProbability P i u ≤ ENNReal.ofReal (C * Real.exp (-c * u ^ (-p.val.2))) := by
  intro p
  obtain ⟨c, C, hc, hC, ht⟩ := Riesz2.repulsion_locallyUniform
    Riesz2.ExternalLogConcave.logConcaveConvergence_result
    p.val.2 p.val.1 p.val.1 p.property.2.1 p.property.2.2 p.property.1 le_rfl
  obtain ⟨h, hreg, hb⟩ := ht p rfl le_rfl le_rfl
  exact ⟨h, hreg, c, C, hc, hC, hb⟩

end Riesz2.Main

end

end
