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
public import Riesz2.Frozen.Gap

/-!
# Finite block of microscopic gaps: `Riesz2.finiteGapBlock`

The block (N(x₂−x₁),…,N(x_{K+1}−x_K)) in Theorem 4, with labels shifted down by one in Lean.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The block (N(x₂−x₁),…,N(x_{K+1}−x_K)) in Theorem 4, with labels shifted down by one in Lean. -/
def finiteGapBlock {N K : ℕ+} (X : Riesz1.Configuration N) : Fin (K : ℕ) → ℝ :=
  fun j => gap X j.val

end Riesz2

end
end
