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
# Lipschitz block observables: `Riesz2.BlockObservable`

Lipschitz functions G : ℝᴷ → ℝ as in Theorem 4. Lean uses the sup norm on the finite
coordinate space. It gives the same class of functions as the Euclidean norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Lipschitz functions G : ℝᴷ → ℝ as in Theorem 4. Lean uses the sup norm on the finite
coordinate space. It gives the same class of functions as the Euclidean norm. -/
@[reducible] def BlockObservable (K : ℕ+) :=
  {G : (Fin (K : ℕ) → ℝ) → ℝ // ∃ L : ℝ≥0, LipschitzWith L G}

end Riesz2

end
end
