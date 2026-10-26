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
public import Riesz2.Frozen.Count

/-!
# Intensity of a point process: `Riesz2.HasIntensity`

The identity E_P N_B = ρ |B| for every bounded Borel set B, expressed using nonnegative
extended integrals. The limiting process has ρ = 1 in the construction of Theorem 3 in
Subsection 6.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The identity E_P N_B = ρ |B| for every bounded Borel set B, expressed using nonnegative
extended integrals. The limiting process has ρ = 1 in the construction of Theorem 3 in
Subsection 6.3. -/
def HasIntensity (P : PointProcess) (ρ : ℝ≥0) : Prop :=
  letI := configurationMeasurableSpace
  ∀ B : Set ℝ, MeasurableSet B → Bornology.IsBounded B →
    (∫⁻ C, count C B ∂(P : Measure LineConfiguration)) = (ρ : ℝ≥0∞) * volume B

end Riesz2

end
end
