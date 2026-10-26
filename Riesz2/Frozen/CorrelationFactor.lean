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
public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.DerivativeSup
public import Riesz2.Frozen.GapDerivativeNorm

/-!
# Derivative factor in the covariance bounds: `Riesz2.correlationFactor`

The factor ‖ξ'(N(x_{i+1}−x_i))‖₂ + ‖ξ'‖∞ exp(−c d_N(i,j)^δ) in Theorems 1 and 2. The
derivative representative is part of the gap observable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The factor ‖ξ'(N(x_{i+1}−x_i))‖₂ + ‖ξ'‖∞ exp(−c d_N(i,j)^δ) in Theorems 1 and 2. The
derivative representative is part of the gap observable. -/
def correlationFactor (p : Parameters) (N : ℕ+) (i : ℤ) (f : GapObservable)
    (c δ : ℝ) (d : ℕ) : ℝ :=
  (gapDerivativeNorm p N i f).toReal +
    derivativeSup f * Real.exp (-c * (d : ℝ) ^ δ)

end Riesz2

end
end
