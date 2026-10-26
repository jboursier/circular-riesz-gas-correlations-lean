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
public import Riesz1.Frozen.Parameters
public import Riesz1.Frozen.RieszExponent
public import Riesz2.Frozen.InverseTemperature

/-!
# Long-range parameters for the companion formalization: `Riesz2.longParameters`

The pair (β,s) with β > 0 and 0 < s < 1, viewed as `Riesz1.Parameters`. See Subsection 1.1
of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The pair (β,s) with β > 0 and 0 < s < 1, viewed as `Riesz1.Parameters`. See Subsection 1.1
of the paper. -/
def longParameters (β : InverseTemperature) (s : Riesz1.RieszExponent) : Riesz1.Parameters :=
  ⟨(β.val, s.val), β.property, s.property⟩

end Riesz2

end
end
