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
public import Riesz2.Frozen.OffLattice
public import Riesz2.Frozen.ShortExponent

/-!
# Short-range Riesz kernel on real lifts: `Riesz2.shortKernelLift`

The absolutely convergent sum g_s(x) = ∑_{k ∈ ℤ}|x+k|^{-s} for s > 1 and x ∉ ℤ. This is the
short-range kernel of equation (1.1), without mean subtraction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The absolutely convergent sum g_s(x) = ∑_{k ∈ ℤ}|x+k|^{-s} for s > 1 and x ∉ ℤ. This is the
short-range kernel of equation (1.1), without mean subtraction. -/
def shortKernelLift (s : ShortExponent) (x : OffLattice) : ℝ :=
  ∑' k : ℤ, 1 / |(k : ℝ) + x.val| ^ s.val

end Riesz2

end
end
