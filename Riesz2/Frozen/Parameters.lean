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

/-!
# Parameters of the circular Riesz gas: `Riesz2.Parameters`

The parameters (β,s) with β > 0, s > 0 and s ≠ 1, covering both regimes of Subsection 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The parameters (β,s) with β > 0, s > 0 and s ≠ 1, covering both regimes of Subsection 1.1. -/
@[reducible] def Parameters := {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≠ 1}

end Riesz2

end
end
