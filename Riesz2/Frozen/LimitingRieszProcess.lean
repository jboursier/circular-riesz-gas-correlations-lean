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
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.UniqueRieszLimit

/-!
# Limiting Riesz point process: `Riesz2.limitingRieszProcess`

The unique local total variation limit Riesz_{s,β} of Theorem 3, selected from a proof of
`UniqueRieszLimit`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The unique local total variation limit Riesz_{s,β} of Theorem 3, selected from a proof of
`UniqueRieszLimit`. -/
def limitingRieszProcess (p : Parameters) (h : UniqueRieszLimit p) : PointProcess :=
  Classical.choose h.exists

end Riesz2

end
end
