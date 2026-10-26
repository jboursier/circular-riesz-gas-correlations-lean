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
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.Gap
public import Riesz2.Frozen.GibbsMeasure

/-!
# Covariance of gap observables: `Riesz2.gapCorrelation`

The covariance Cov_{G_{N,β}}[ξ(N(x_{i+1}−x_i)),χ(N(x_{j+1}−x_j))] in Theorems 1 and 2. The
two observables are required to belong to L² of the Gibbs law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The covariance Cov_{G_{N,β}}[ξ(N(x_{i+1}−x_i)),χ(N(x_{j+1}−x_j))] in Theorems 1 and 2. The
two observables are required to belong to L² of the Gibbs law. -/
def gapCorrelation (p : Parameters) (N : ℕ+) (i j : ℤ) (f g : ℝ → ℝ)
    (_hf : MemLp (fun X => f (gap X i)) 2 (gibbsMeasure p N))
    (_hg : MemLp (fun X => g (gap X j)) 2 (gibbsMeasure p N)) : ℝ :=
  ProbabilityTheory.covariance (fun X => f (gap X i))
    (fun X => g (gap X j)) (gibbsMeasure p N)

end Riesz2

end
end
