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
public import Riesz2.Frozen.LineConfiguration
public import Riesz2.Frozen.Count

/-!
# Domain of an ordered point: `Riesz2.OrderedPointDomain`

Configurations with at least j points in [a,b) when `leftClosed`, or in (a,b] otherwise.
This is the domain used to enumerate the configurations of Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Configurations with at least j points in [a,b) when `leftClosed`, or in (a,b] otherwise.
This is the domain used to enumerate the configurations of Subsection 1.5. -/
@[reducible] def OrderedPointDomain (a b : ℝ) (leftClosed : Bool) (j : ℕ+) :=
  {C : LineConfiguration //
    (j : ℝ≥0∞) ≤ count C (if leftClosed then Ico a b else Ioc a b)}

end Riesz2

end
end
