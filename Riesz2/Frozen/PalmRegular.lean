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
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.PalmMeasure
public import Riesz2.Frozen.RootedConfigurations
public import Riesz2.Frozen.RootedGap
public import Riesz2.Frozen.RootedPalmMeasure

/-!
# Regularity of the Palm gap law: `Riesz2.PalmRegular`

The Palm law is a probability supported on configurations rooted at zero and unbounded in
both directions. Its gaps are invariant under shifts of the labels, integrable and of mean
one. These properties hold for the limit in the proof of Theorem 3 in Subsection 6.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The Palm law is a probability supported on configurations rooted at zero and unbounded in
both directions. Its gaps are invariant under shifts of the labels, integrable and of mean
one. These properties hold for the limit in the proof of Theorem 3 in Subsection 6.3. -/
def PalmRegular (P : PointProcess) : Prop :=
  letI := configurationMeasurableSpace
  MeasurableSet rootedConfigurations ∧ palmMeasure P rootedConfigurations = 1 ∧
    IsProbabilityMeasure (rootedPalmMeasure P) ∧
    IsProbabilityMeasure (palmMeasure P) ∧ palmMeasure P rootedConfigurationsᶜ = 0 ∧
    (rootedPalmMeasure P).map (fun C i => rootedGap C (i + 1)) =
      (rootedPalmMeasure P).map rootedGap ∧
    ∀ i : ℤ, Integrable (fun C => rootedGap C i) (rootedPalmMeasure P) ∧
      (∫ C, rootedGap C i ∂rootedPalmMeasure P) = 1

end Riesz2

end
end
