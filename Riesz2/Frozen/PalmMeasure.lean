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
public import Riesz2.Frozen.PalmKernel

/-!
# Campbell construction of the Palm measure: `Riesz2.palmMeasure`

The mean rooted counting measure E_P[∑_{x ∈ 𝓒 ∩ [0,1)} δ_{𝓒−x}]. For a stationary process of
intensity one this is its Palm probability law. See Subsection 1.5 and the Palm construction
in Subsection 6.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The mean rooted counting measure E_P[∑_{x ∈ 𝓒 ∩ [0,1)} δ_{𝓒−x}]. For a stationary process of
intensity one this is its Palm probability law. See Subsection 1.5 and the Palm construction
in Subsection 6.3. -/
def palmMeasure (P : PointProcess) :
    letI := configurationMeasurableSpace
    Measure LineConfiguration :=
  letI := configurationMeasurableSpace
  (P : Measure LineConfiguration).bind palmKernel

end Riesz2

end
end
