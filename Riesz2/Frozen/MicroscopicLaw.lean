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
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.MicroscopicConfiguration

/-!
# Law of the microscopic configuration: `Riesz2.microscopicLaw`

The law Q_{N,β} of the microscopic configuration about the fixed spatial origin, as in
equation (1.7).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The law Q_{N,β} of the microscopic configuration about the fixed spatial origin, as in
equation (1.7). -/
def microscopicLaw (p : Parameters) (N : ℕ+) :
    letI := configurationMeasurableSpace
    Measure LineConfiguration :=
  letI := configurationMeasurableSpace
  (gibbsMeasure p N).map (microscopicConfiguration 0)

end Riesz2

end
end
