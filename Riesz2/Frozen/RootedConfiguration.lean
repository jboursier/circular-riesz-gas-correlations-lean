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
public import Riesz2.Frozen.RootedConfigurations

/-!
# Two-sided rooted configurations: `Riesz2.RootedConfiguration`

Configurations rooted at zero and unbounded in both directions. This is the carrier for the
two-sided Palm enumeration (z_i)_{i ∈ ℤ} of Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Configurations rooted at zero and unbounded in both directions. This is the carrier for the
two-sided Palm enumeration (z_i)_{i ∈ ℤ} of Subsection 1.5. -/
@[reducible] def RootedConfiguration := rootedConfigurations

end Riesz2

end
end
