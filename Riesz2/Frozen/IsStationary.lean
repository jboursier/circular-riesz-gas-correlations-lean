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
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.TranslateConfiguration

/-!
# Translation invariance of a point process: `Riesz2.IsStationary`

Invariance of a point process under every real translation, as asserted for Riesz_{s,β} in
Theorem 3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Invariance of a point process under every real translation, as asserted for Riesz_{s,β} in
Theorem 3. -/
def IsStationary (P : PointProcess) : Prop :=
  letI := configurationMeasurableSpace
  ∀ t : ℝ, (P : Measure LineConfiguration).map (translateConfiguration t) = P

end Riesz2

end
end
