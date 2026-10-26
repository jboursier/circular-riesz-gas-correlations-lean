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
public import Riesz2.Frozen.LineConfiguration

/-!
# Restriction of a configuration: `Riesz2.restrictConfiguration`

The restriction 𝓒|_B of a simple configuration to a set B. In Theorem 3, B is the bounded
window [−R,R].
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The restriction 𝓒|_B of a simple configuration to a set B. In Theorem 3, B is the bounded
window [−R,R]. -/
def restrictConfiguration (B : Set ℝ) (C : LineConfiguration) : LineConfiguration :=
  ⟨C.val ∩ B, fun a b => (C.property a b).subset (by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩)⟩

end Riesz2

end
end
