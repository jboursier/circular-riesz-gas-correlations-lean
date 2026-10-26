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

/-!
# Simple locally finite configurations on the line: `Riesz2.LineConfiguration`

The space Conf(ℝ) of simple locally finite configurations from Subsection 1.5, represented
as sets of atoms. It includes the empty configuration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The space Conf(ℝ) of simple locally finite configurations from Subsection 1.5, represented
as sets of atoms. It includes the empty configuration. -/
@[reducible] def LineConfiguration :=
  {A : Set ℝ // ∀ a b : ℝ, (A ∩ Icc a b).Finite}

end Riesz2

end
end
