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

/-!
# Counting measure of a configuration: `Riesz2.configurationMeasure`

The counting measure ∑_{x ∈ 𝓒} δ_x of a simple locally finite configuration 𝓒 ∈ Conf(ℝ). See
Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The counting measure ∑_{x ∈ 𝓒} δ_x of a simple locally finite configuration 𝓒 ∈ Conf(ℝ). See
Subsection 1.5. -/
def configurationMeasure (C : LineConfiguration) : Measure ℝ :=
  Measure.sum (fun x : C.val => Measure.dirac x.val)

end Riesz2

end
end
