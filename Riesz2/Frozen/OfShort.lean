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
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.ShortExponent

/-!
# Inclusion of the short-range parameter regime: `Riesz2.ofShort`

The pair (β,s) with β > 0 and s > 1, viewed as parameters of the circular Riesz gas in
Subsection 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The pair (β,s) with β > 0 and s > 1, viewed as parameters of the circular Riesz gas in
Subsection 1.1. -/
def ofShort (β : InverseTemperature) (s : ShortExponent) : Parameters :=
  ⟨(β.val, s.val), β.property, lt_trans zero_lt_one s.property, ne_of_gt s.property⟩

end Riesz2

end
end
