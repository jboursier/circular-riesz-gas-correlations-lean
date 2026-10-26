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
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.UnitLength
public import Riesz2.Frozen.LineConfiguration

/-!
# Microscopic configuration near a spatial origin: `Riesz2.microscopicConfiguration`

The configuration 𝓒_N obtained by centering at a circle point a, retaining particles whose
centered lift has absolute value less than 1/4, and multiplying positions by N. This is the
microscopic configuration of Subsection 1.4. Distinct particles give distinct atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The configuration 𝓒_N obtained by centering at a circle point a, retaining particles whose
centered lift has absolute value less than 1/4, and multiplying positions by N. This is the
microscopic configuration of Subsection 1.4. Distinct particles give distinct atoms. -/
def microscopicConfiguration {N : ℕ+} (a : UnitAddCircle)
    (X : Riesz1.Configuration N) : LineConfiguration :=
  let r : Fin (N : ℕ) → ℝ := fun i =>
    Riesz1.centralRep Riesz1.unitLength ((X.val i : UnitAddCircle) - a)
  ⟨{x | ∃ i, |r i| < 1 / 4 ∧ x = (N : ℝ) * r i}, fun b c =>
    (Set.finite_range (fun i => (N : ℝ) * r i)).subset (by
      rintro x ⟨⟨i, _, rfl⟩, _⟩
      exact ⟨i, rfl⟩)⟩

end Riesz2

end
end
