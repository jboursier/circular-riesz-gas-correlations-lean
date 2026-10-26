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
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.UnitLength
public import Riesz2.Frozen.ShortExponent

/-!
# Short-range periodic Riesz kernel: `Riesz2.shortKernel`

The kernel g_s(x) = ∑_{k ∈ ℤ}|x+k|^{-s} for s > 1, evaluated at the canonical centered lift
of a nonzero circle point. See equation (1.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The kernel g_s(x) = ∑_{k ∈ ℤ}|x+k|^{-s} for s > 1, evaluated at the canonical centered lift
of a nonzero circle point. See equation (1.1). -/
def shortKernel (s : ShortExponent) (x : {x : UnitAddCircle // x ≠ 0}) : ℝ :=
  ∑' k : ℤ, 1 / |(k : ℝ) + Riesz1.centralRep Riesz1.unitLength x.val| ^ s.val

end Riesz2

end
end
