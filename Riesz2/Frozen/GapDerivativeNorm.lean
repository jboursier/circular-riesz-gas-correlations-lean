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
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.Gap
public import Riesz2.Frozen.GibbsMeasure

/-!
# L² norm of a gap derivative: `Riesz2.gapDerivativeNorm`

The norm ‖ξ'(N(x_{i+1}−x_i))‖₂ under G_{N,β}, as used in Theorems 1 and 2. It takes values
in ℝ≥0∞. The decay statements establish its finiteness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The norm ‖ξ'(N(x_{i+1}−x_i))‖₂ under G_{N,β}, as used in Theorems 1 and 2. It takes values
in ℝ≥0∞. The decay statements establish its finiteness. -/
def gapDerivativeNorm (p : Parameters) (N : ℕ+) (i : ℤ) (f : GapObservable) : ℝ≥0∞ :=
  eLpNorm (fun X => f.val.2 (gap X i)) 2 (gibbsMeasure p N)

end Riesz2

end
end
