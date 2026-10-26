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

/-!
# Coordinate derivative norm: `Riesz2.coordinateDerivativeNorm`

The least Lipschitz constant of G along coordinate j, encoding ‖∂ⱼG‖∞ in Theorem 4. For
Lipschitz G this equals the Lebesgue essential supremum of its weak partial derivative on
ℝᴷ.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The least Lipschitz constant of G along coordinate j, encoding ‖∂ⱼG‖∞ in Theorem 4. For
Lipschitz G this equals the Lebesgue essential supremum of its weak partial derivative on
ℝᴷ. -/
def coordinateDerivativeNorm {K : ℕ+} (G : BlockObservable K) (j : Fin (K : ℕ)) : ℝ≥0 :=
  sInf {L : ℝ≥0 | ∀ (x : Fin (K : ℕ) → ℝ) (t : ℝ),
    |G.val (Function.update x j t) - G.val x| ≤ (L : ℝ) * |t - x j|}

end Riesz2

end
end
