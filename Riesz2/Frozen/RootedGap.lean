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
public import Riesz2.Frozen.RootedConfiguration
public import Riesz2.Frozen.RootedPoint

/-!
# Labelled Palm gap: `Riesz2.rootedGap`

The gap z_{i+1}−z_i in the two-sided Palm enumeration with z₀ = 0. See Subsection 1.5 and
Proposition 1.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The gap z_{i+1}−z_i in the two-sided Palm enumeration with z₀ = 0. See Subsection 1.5 and
Proposition 1.2. -/
def rootedGap (C : RootedConfiguration) (i : ℤ) : ℝ :=
  rootedPoint C (i + 1) - rootedPoint C i

end Riesz2

end
end
