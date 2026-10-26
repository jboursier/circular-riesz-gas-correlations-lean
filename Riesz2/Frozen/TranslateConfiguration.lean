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
# Translation of a configuration: `Riesz2.translateConfiguration`

The translated configuration 𝓒−t. This sign convention roots a particle at t at the origin
in the Palm construction of Subsection 6.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The translated configuration 𝓒−t. This sign convention roots a particle at t at the origin
in the Palm construction of Subsection 6.3. -/
def translateConfiguration (t : ℝ) (C : LineConfiguration) : LineConfiguration :=
  ⟨{x | x + t ∈ C.val}, fun a b =>
    ((C.property (a + t) (b + t)).image (fun x => x - t)).subset (by
      rintro x ⟨hx, ha, hb⟩
      exact ⟨x + t, ⟨hx, by constructor <;> linarith⟩, by ring⟩)⟩

end Riesz2

end
end
