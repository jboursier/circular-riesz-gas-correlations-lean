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
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.GibbsMeasure
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.ShortGibbsMeasure

/-!
# Gibbs law of the circular Riesz gas: `Riesz2.gibbsMeasure`

The Gibbs law G_{N,β} with density proportional to exp(−βH_N), as in equation (1.3). The
long-range branch uses `Riesz1.gibbsMeasure`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The Gibbs law G_{N,β} with density proportional to exp(−βH_N), as in equation (1.3). The
long-range branch uses `Riesz1.gibbsMeasure`. -/
def gibbsMeasure (p : Parameters) (N : ℕ+) : Measure (Riesz1.Configuration N) :=
  if h : p.val.2 < 1 then
    Riesz1.gibbsMeasure ⟨p.val, p.property.1, p.property.2.1, h⟩ N
  else shortGibbsMeasure ⟨p.val.1, p.property.1⟩
    ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩ N

end Riesz2

end
end
