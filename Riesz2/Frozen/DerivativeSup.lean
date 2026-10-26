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

/-!
# Essential bound on a gap derivative: `Riesz2.derivativeSup`

The Lebesgue essential supremum ‖ξ'‖∞ in Theorems 1 and 2. The definition of `GapObservable`
ensures that it is finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The Lebesgue essential supremum ‖ξ'‖∞ in Theorems 1 and 2. The definition of `GapObservable`
ensures that it is finite. -/
def derivativeSup (f : GapObservable) : ℝ := (eLpNorm f.val.2 ∞ volume).toReal

end Riesz2

end
end
