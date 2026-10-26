/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# A domination bound for power functions

For `s > 0`, the quantity `α (δ ^ (-s - 1)) ^ 2` dominates the lower-order terms
`β (1 + δ ^ (-s - 2)) + γ (δ ^ 2)⁻¹` up to an additive constant, uniformly in `δ > 0`. The exponent
`-2 s - 2` of the leading term exceeds the exponents `-s - 2` and `-2` of the others, so the leading
term wins as `δ` tends to zero. The bound is used to absorb the Laplacian and the distance terms in
the lower bound for `A |∇V|² - ΔV - K d_∂^{-2}`.
-/

@[expose] public section

namespace Riesz2.RpowDomination

/-- Let `s > 0`, `α > 0` and `β, γ ≥ 0`. Then there is a constant `C` such that, for every `δ > 0`,
`β (1 + δ ^ (-s - 2)) + γ (δ ^ 2)⁻¹ ≤ α (δ ^ (-s - 1)) ^ 2 + C`. -/
theorem exists_bound {s α β γ : ℝ} (hs : 0 < s) (hα : 0 < α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
      β * (1 + δ ^ (-s - 2)) + γ * (δ ^ 2)⁻¹ ≤ α * (δ ^ (-s - 1)) ^ 2 + C := by
  set η : ℝ := α / (2 * (β + γ + 1)) with hη
  have hηpos : 0 < η := by positivity
  set δ₀ : ℝ := min 1 (η ^ (1 / s)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min one_pos (Real.rpow_pos_of_pos hηpos _)
  have hηle : (β + γ) * η ≤ α / 2 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨β + β * δ₀ ^ (-s - 2) + γ * (δ₀ ^ 2)⁻¹, fun δ hδ => ?_⟩
  have hXnn : 0 ≤ δ ^ (-2 * s - 2) := Real.rpow_nonneg hδ.le _
  have hXeq : (δ ^ (-s - 1)) ^ 2 = δ ^ (-2 * s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  have hT : δ ^ (-s - 2) = δ ^ (-2 * s - 2) * δ ^ s := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hU : (δ ^ 2)⁻¹ = δ ^ (-2 * s - 2) * δ ^ (2 * s) := by
    rw [← Real.rpow_add hδ, show -2 * s - 2 + 2 * s = -(2 : ℝ) by ring, Real.rpow_neg hδ.le,
      Real.rpow_two]
  rw [hXeq]
  by_cases hle : δ ≤ δ₀
  · -- Near zero, `δ ^ s` and `δ ^ (2 * s)` are at most `η`, which absorbs both lower-order terms.
    have hδ1 : δ ≤ 1 := hle.trans (min_le_left _ _)
    have hδs : δ ^ s ≤ η := by
      have h1 : δ ≤ η ^ (1 / s) := hle.trans (min_le_right _ _)
      calc δ ^ s ≤ (η ^ (1 / s)) ^ s := Real.rpow_le_rpow hδ.le h1 hs.le
        _ = η := by rw [← Real.rpow_mul hηpos.le, one_div_mul_cancel hs.ne', Real.rpow_one]
    have hδ2s : δ ^ (2 * s) ≤ δ ^ s :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hk1 : β * δ ^ s * δ ^ (-2 * s - 2) ≤ β * η * δ ^ (-2 * s - 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδs hβ) hXnn
    have hk2 : γ * δ ^ (2 * s) * δ ^ (-2 * s - 2) ≤ γ * η * δ ^ (-2 * s - 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hδ2s.trans hδs) hγ) hXnn
    have hk3 : (β + γ) * η * δ ^ (-2 * s - 2) ≤ α / 2 * δ ^ (-2 * s - 2) :=
      mul_le_mul_of_nonneg_right hηle hXnn
    have hlhs : β * (1 + δ ^ (-s - 2)) + γ * (δ ^ 2)⁻¹ =
        β + β * δ ^ s * δ ^ (-2 * s - 2) + γ * δ ^ (2 * s) * δ ^ (-2 * s - 2) := by
      rw [hT, hU]
      ring
    have hCnn : 0 ≤ β * δ₀ ^ (-s - 2) + γ * (δ₀ ^ 2)⁻¹ := by
      have h1 : 0 ≤ δ₀ ^ (-s - 2) := Real.rpow_nonneg hδ₀pos.le _
      have h2 : 0 ≤ (δ₀ ^ 2)⁻¹ := by positivity
      positivity
    nlinarith [mul_nonneg hα.le hXnn]
  · -- Away from zero, the two lower-order terms are bounded by their values at `δ₀`.
    rw [not_le] at hle
    have hT' : δ ^ (-s - 2) ≤ δ₀ ^ (-s - 2) :=
      Real.rpow_le_rpow_of_nonpos hδ₀pos hle.le (by linarith)
    have hU' : (δ ^ 2)⁻¹ ≤ (δ₀ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hδ₀pos.le hle.le 2)
    have hk1 : β * δ ^ (-s - 2) ≤ β * δ₀ ^ (-s - 2) := mul_le_mul_of_nonneg_left hT' hβ
    have hk2 : γ * (δ ^ 2)⁻¹ ≤ γ * (δ₀ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hU' hγ
    have hpos : 0 ≤ α * (δ ^ (-2 * s - 2)) := mul_nonneg hα.le hXnn
    nlinarith

end Riesz2.RpowDomination

end
