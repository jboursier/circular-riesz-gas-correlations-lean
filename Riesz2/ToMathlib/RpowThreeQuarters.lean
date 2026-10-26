/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Strict midpoint concavity of a power at `1` and `1/2`

For an exponent `0 < p < 1`, strict concavity of `t ↦ t^p` at the points `1` and `1/2` gives
`1 + (1/2)^p < 2 (3/4)^p`, because `3/4` is the midpoint of `1` and `1/2`.
-/

@[expose] public section

noncomputable section

namespace Riesz2.ToMathlib

/-- For `0 < p < 1`, the inequality `1 + (1/2)^p < 2 (3/4)^p` holds. -/
theorem one_add_half_rpow_lt_two_three_quarters_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    1 + (1 / 2 : ℝ) ^ p < 2 * (3 / 4 : ℝ) ^ p := by
  have h := (Real.strictConcaveOn_rpow hp₀ hp₁).2
    (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (by norm_num : (1 : ℝ) ≠ 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (1 / 2 : ℝ) + 1 / 2 * (1 / 2) = 3 / 4 := by norm_num
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at h
  rw [hmid] at h
  linarith

end Riesz2.ToMathlib

end
end
