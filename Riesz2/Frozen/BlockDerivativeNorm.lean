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
public import Riesz2.Frozen.BlockObservable
public import Riesz2.Frozen.CoordinateDerivativeNorm

/-!
# Sum of coordinate derivative norms: `Riesz2.blockDerivativeNorm`

The sum ∑ⱼ ‖∂ⱼG‖∞ in Theorem 4, encoded as the sum of the least coordinate Lipschitz
constants of G.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The sum ∑ⱼ ‖∂ⱼG‖∞ in Theorem 4, encoded as the sum of the least coordinate Lipschitz
constants of G. -/
def blockDerivativeNorm {K : ℕ+} (G : BlockObservable K) : ℝ :=
  ∑ j, (coordinateDerivativeNorm G j : ℝ)

end Riesz2

end
end
