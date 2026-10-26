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
# One-gap observables and their derivatives: `Riesz2.GapObservable`

A Lipschitz function ξ : ℝ → ℝ with a measurable representative of its almost-everywhere
derivative ξ'. This encodes the locally absolutely continuous observables with bounded
derivatives in Theorems 1 and 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- A Lipschitz function ξ : ℝ → ℝ with a measurable representative of its almost-everywhere
derivative ξ'. This encodes the locally absolutely continuous observables with bounded
derivatives in Theorems 1 and 2. -/
@[reducible] def GapObservable :=
  {f : (ℝ → ℝ) × (ℝ → ℝ) //
    (∃ L : ℝ≥0, LipschitzWith L f.1) ∧ AEStronglyMeasurable f.2 volume ∧
    (∀ᵐ x ∂volume, HasDerivAt f.1 (f.2 x) x) ∧ eLpNorm f.2 ∞ volume < ⊤}

end Riesz2

end
end
