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
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.Energy
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.ShortEnergy

/-!
# Energy of the circular Riesz gas: `Riesz2.energy`

The energy H_N = N^{-s} ∑_{i≠j} g_s(x_i−x_j) of equation (1.2), for either exponent regime.
The branch 0 < s < 1 uses `Riesz1.energy`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The energy H_N = N^{-s} ∑_{i≠j} g_s(x_i−x_j) of equation (1.2), for either exponent regime.
The branch 0 < s < 1 uses `Riesz1.energy`. -/
def energy (p : Parameters) {N : ℕ+} (X : Riesz1.Configuration N) : ℝ :=
  if h : p.val.2 < 1 then Riesz1.energy ⟨p.val.2, p.property.2.1, h⟩ X
  else shortEnergy ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩ X

end Riesz2

end
end
