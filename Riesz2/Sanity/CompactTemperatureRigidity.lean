/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.LongRangeRigidityLocallyUniform

/-!
# Sanity checks for the compact-temperature rigidity input

Concrete parameters exercise a nondegenerate temperature interval and a block of length two.
Singleton intervals recover exactly the fixed-β event and quantifier order of the library bridge.

-/

public section

noncomputable section

open Set

namespace Riesz2.ExternalRigiditySanity

/-- A permitted exponent strictly inside the rigidity range. -/
theorem concrete_exponent :
    ∃ s : Riesz1.RieszExponent,
      s.val = 1 / 2 ∧ 0 < (1 / 16 : ℝ) ∧ (1 / 16 : ℝ) < (1 - s.val / 2) / 2 := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, rfl, ?_, ?_⟩ <;> norm_num

/-- The compact interval [1,2] contains the positive temperature 3/2. -/
theorem concrete_interval :
    0 < (1 : ℝ) ∧ (1 : ℝ) ≤ 2 ∧
      ∃ β : InverseTemperature, β.val = 3 / 2 ∧ β.val ∈ Icc (1 : ℝ) 2 := by
  refine ⟨by norm_num, by norm_num, ⟨3 / 2, by norm_num⟩, rfl, ?_⟩
  norm_num

/-- The same permitted exponent gives positive tail and fluctuation powers at a block. -/
theorem concrete_block :
    ∃ N : ℕ+, 2 ≤ (N : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ 2 ≤ (N : ℕ) / 2 ∧
      0 < (2 : ℝ) ^ ((1 / 2 : ℝ) / 2 + 1 / 16) ∧
      0 < (1 / 16 : ℝ) / (4 * (1 / 2 + 2)) := by
  refine ⟨⟨4, by norm_num⟩, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The rigidity estimate supplies constants uniform over temperatures in [1,2]. -/
theorem concrete_uniform_family (h : External.LongRangeRigidityLocallyUniform) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc (1 : ℝ) 2 →
      ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : ℤ) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
        gibbsMeasure (ofLong β ⟨1 / 2, by norm_num, by norm_num⟩) N {X |
          |(N : ℝ) * (Riesz1.cyclicLift X (i + k) - Riesz1.cyclicLift X i) - k| ≥
            (k : ℝ) ^ ((1 / 2 : ℝ) / 2 + 1 / 16)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ ((1 / 16 : ℝ) / (4 * (1 / 2 + 2))))) := by
  exact h ⟨1 / 2, by norm_num, by norm_num⟩ (1 / 16) (by norm_num) (by norm_num)
    1 2 (by norm_num) (by norm_num)

/-- Specializing the interval to {β} gives the exact fixed-β type of `longRangeRigidity`. -/
theorem fixed_beta (h : External.LongRangeRigidityLocallyUniform)
    (β : InverseTemperature) (s : Riesz1.RieszExponent) {b : ℝ}
    (hb : 0 < b) (hbs : b < (1 - s.val / 2) / 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : ℤ) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
        gibbsMeasure (ofLong β s) N {X |
          |(N : ℝ) * (Riesz1.cyclicLift X (i + k) - Riesz1.cyclicLift X i) - k| ≥
            (k : ℝ) ^ (s.val / 2 + b)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / (4 * (s.val + 2))))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := h s b hb hbs β.val β.val β.property le_rfl
  exact ⟨C, c, hC, hc, htail β ⟨le_rfl, le_rfl⟩⟩

end Riesz2.ExternalRigiditySanity

end
