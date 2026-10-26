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
# Configurations rooted at zero: `Riesz2.rootedConfigurations`

The set of configurations containing zero and unbounded in both directions, used for the
Palm law and enumeration in Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The set of configurations containing zero and unbounded in both directions, used for the
Palm law and enumeration in Subsection 1.5. -/
def rootedConfigurations : Set LineConfiguration :=
  {C | 0 ∈ C.val ∧ (∀ r : ℝ, ∃ x ∈ C.val, r < x) ∧
    (∀ r : ℝ, ∃ x ∈ C.val, x < r)}

end Riesz2

end
end
