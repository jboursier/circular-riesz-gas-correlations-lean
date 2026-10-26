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
public import Riesz2.Frozen.RootedGap

/-!
# Block of Palm gaps: `Riesz2.rootedGapBlock`

The block (z₁−z₀,…,z_K−z_{K−1}) under the rooted Palm law, as in Theorem 4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The block (z₁−z₀,…,z_K−z_{K−1}) under the rooted Palm law, as in Theorem 4. -/
def rootedGapBlock (K : ℕ+) (C : RootedConfiguration) : Fin (K : ℕ) → ℝ :=
  fun j => rootedGap C j.val

end Riesz2

end
end
