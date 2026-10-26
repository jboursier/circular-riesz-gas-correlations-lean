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
public import Riesz2.Frozen.Count

/-!
# Two-sided enumeration of a rooted configuration: `Riesz2.rootedPoint`

The increasing enumeration (z_i)_{i ∈ ℤ} with z₀ = 0, specified by count thresholds. Local
finiteness and unboundedness in both directions make the right-tail minima and left-tail
maxima finite and attained. See Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The increasing enumeration (z_i)_{i ∈ ℤ} with z₀ = 0, specified by count thresholds. Local
finiteness and unboundedness in both directions make the right-tail minima and left-tail
maxima finite and attained. See Subsection 1.5. -/
def rootedPoint (C : RootedConfiguration) (i : ℤ) : ℝ :=
  if i = 0 then 0 else if 0 < i then
    sInf {x : ℝ | x ∈ C.val.val ∧ 0 < x ∧
      (i.toNat : ℝ≥0∞) ≤ count C.val (Ioc 0 x)}
  else sSup {x : ℝ | x ∈ C.val.val ∧ x < 0 ∧
      ((-i).toNat : ℝ≥0∞) ≤ count C.val (Ico x 0)}

end Riesz2

end
end
