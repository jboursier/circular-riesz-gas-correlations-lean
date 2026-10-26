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
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.RootedConfiguration
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.PalmMeasure

/-!
# Palm law on the rooted carrier: `Riesz2.rootedPalmMeasure`

The pullback of the Palm law to configurations rooted at zero and unbounded in both
directions. The convergence statement establishes full mass of this carrier and
normalization of the pullback. See Subsection 1.5 and the proof of Theorem 3 in Subsection
6.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The pullback of the Palm law to configurations rooted at zero and unbounded in both
directions. The convergence statement establishes full mass of this carrier and
normalization of the pullback. See Subsection 1.5 and the proof of Theorem 3 in Subsection
6.3. -/
def rootedPalmMeasure (P : PointProcess) :
    letI := configurationMeasurableSpace
    Measure RootedConfiguration :=
  letI := configurationMeasurableSpace
  (palmMeasure P).comap Subtype.val

end Riesz2

end
end
