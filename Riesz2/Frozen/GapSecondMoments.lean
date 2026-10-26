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
# Second moments of gap observables: `Riesz2.GapSecondMoments`

The L² integrability of ξ, χ and their derivative representatives evaluated at the selected
microscopic gaps. These are the moment conclusions used to state the bounds in Theorems 1
and 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The L² integrability of ξ, χ and their derivative representatives evaluated at the selected
microscopic gaps. These are the moment conclusions used to state the bounds in Theorems 1
and 2. -/
def GapSecondMoments (p : Parameters) (N : ℕ+) (i j : ℤ) (f g : GapObservable) : Prop :=
  MemLp (fun X => f.val.1 (gap X i)) 2 (gibbsMeasure p N) ∧
  MemLp (fun X => g.val.1 (gap X j)) 2 (gibbsMeasure p N) ∧
  MemLp (fun X => f.val.2 (gap X i)) 2 (gibbsMeasure p N) ∧
  MemLp (fun X => g.val.2 (gap X j)) 2 (gibbsMeasure p N)

end Riesz2

end
end
