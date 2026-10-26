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
public import Riesz2.Frozen.HasIntensity
public import Riesz2.Frozen.IsStationary
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.UniqueRieszLimit
public import Riesz2.Frozen.LimitingRieszProcess
import Riesz2.Main.Convergence

/-!
# Convergence to the Riesz process: `Riesz2.convergence`

For β > 0 and s ∈ (0,1) ∪ (1,+∞), the microscopic laws Q_{N,β} converge in total variation
on every bounded window to a unique process Riesz_{s,β}. The limit is translation invariant
and has intensity one. Its Palm law has two-sided, index-stationary gaps of mean one, as
constructed in Subsection 6.3.
This is Theorem 3 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), the microscopic laws Q_{N,β} converge in total variation
on every bounded window to a unique process Riesz_{s,β}. The limit is translation invariant
and has intensity one. Its Palm law has two-sided, index-stationary gaps of mean one, as
constructed in Subsection 6.3.
This is Theorem 3 of the paper. -/
theorem convergence :
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    IsStationary P ∧ HasIntensity P 1 ∧ PalmRegular P :=
  by exact Riesz2.Main.convergence

end Riesz2

end
end
