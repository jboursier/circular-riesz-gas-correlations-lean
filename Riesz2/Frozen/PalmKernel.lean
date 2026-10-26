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
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.TranslateConfiguration

/-!
# Rooted counting measure for Palm construction: `Riesz2.palmKernel`

The finite measure ∑_{x ∈ 𝓒 ∩ [0,1)} δ_{𝓒−x}, which roots the configuration at each particle
in [0,1). It is used to construct the Palm law Riesz_{s,β}^0 of Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The finite measure ∑_{x ∈ 𝓒 ∩ [0,1)} δ_{𝓒−x}, which roots the configuration at each particle
in [0,1). It is used to construct the Palm law Riesz_{s,β}^0 of Subsection 1.5. -/
def palmKernel (C : LineConfiguration) :
    letI := configurationMeasurableSpace
    Measure LineConfiguration :=
  letI := configurationMeasurableSpace
  Measure.sum (fun x : {x : ℝ // x ∈ C.val ∩ Ico (0 : ℝ) 1} =>
    Measure.dirac (translateConfiguration x.val C))

end Riesz2

end
end
