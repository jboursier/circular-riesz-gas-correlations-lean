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
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.ShortKernelLift

/-!
# Energy of the short-range gas: `Riesz2.shortEnergy`

The energy H_N = N^{-s}∑_{i≠j}g_s(x_i−x_j) for s > 1 in equation (1.2). Both orientations of
each pair are included, using the unsubtracted periodic kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The energy H_N = N^{-s}∑_{i≠j}g_s(x_i−x_j) for s > 1 in equation (1.2). Both orientations of
each pair are included, using the unsubtracted periodic kernel. -/
def shortEnergy (s : ShortExponent) {N : ℕ+} (X : Riesz1.Configuration N) : ℝ :=
  (N : ℝ) ^ (-s.val) *
    ∑ i : Fin (N : ℕ), ∑ j : {j : Fin (N : ℕ) // j ≠ i},
      shortKernelLift s ⟨X.val i - X.val j.val,
        by
          intro h
          have hi : X.val i ∈ Ico (X.val ⟨0, N.pos⟩) (X.val ⟨0, N.pos⟩ + 1) :=
            ⟨X.property.1.monotone (Fin.zero_le i), X.property.2.2.2 i⟩
          have hj : X.val j.val ∈ Ico (X.val ⟨0, N.pos⟩) (X.val ⟨0, N.pos⟩ + 1) :=
            ⟨X.property.1.monotone (Fin.zero_le j.val), X.property.2.2.2 j.val⟩
          have he : (X.val i : UnitAddCircle) = (X.val j.val : UnitAddCircle) := by
            simpa only [AddCircle.coe_sub, sub_eq_zero] using h
          exact j.property (X.property.1.injective
            ((AddCircle.coe_eq_coe_iff_of_mem_Ico hi hj).mp he)).symm⟩

end Riesz2

end
end
