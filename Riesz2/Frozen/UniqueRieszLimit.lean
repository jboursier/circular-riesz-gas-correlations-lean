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
public import Riesz2.Frozen.LocalConverges
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.MicroscopicLaw

/-!
# Existence and uniqueness of the local limit: `Riesz2.UniqueRieszLimit`

The assertion that there exists exactly one point process P to which Q_{N,β} converges in
local total variation. This specifies the limit in Theorem 3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The assertion that there exists exactly one point process P to which Q_{N,β} converges in
local total variation. This specifies the limit in Theorem 3. -/
def UniqueRieszLimit (p : Parameters) : Prop :=
  ∃! P : PointProcess, LocalConverges (microscopicLaw p) P

end Riesz2

end
end
