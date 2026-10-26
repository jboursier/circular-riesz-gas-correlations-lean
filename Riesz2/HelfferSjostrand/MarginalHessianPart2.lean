/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MarginalHessian
public import Riesz2.ToMathlib.CollisionDensityBounds

/-!
# All-order scalar kernel bounds for proper marginal calculus

An ingredient of Appendix A: physical kernel derivatives have inverse
power bounds uniform away from both ends of one period.
-/

public section

noncomputable section

open Set

namespace Riesz2.MarginalHessian

/-- All positive-order scalar kernel bounds used in Appendix A. Both exponent regimes use the image formula. The constant is quantified before the separation and its endpoint bound. -/
theorem kernel_derivative_bound (p : Parameters) (j : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : OffLattice) (δ : ℝ),
      0 < δ → δ ≤ x.val → δ ≤ 1 - x.val →
      |PhysicalEnergy.kernelDerivative p j x| ≤ C * δ ^ (-p.val.2 - (j : ℝ)) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hq : 1 < p.val.2 + (j : ℝ) := by linarith [p.property.2.1]
  let A := (-1 : ℝ) ^ (j : ℕ) * ∏ a ∈ Finset.range j, (p.val.2 + (a : ℝ))
  let B := PeriodicPower.bound (p.val.2 + (j : ℝ)) hq
  have hB : 0 < B := PeriodicPower.bound_pos _ _
  refine ⟨|A| * B + 1, by positivity, fun x δ hδ hx hxc => ?_⟩
  have hsum := PeriodicPower.summable_and_le hq hδ hx hxc
  let f : ℤ → ℝ := fun k => Real.sign (x.val + k) ^ (j : ℕ) /
    |x.val + k| ^ (p.val.2 + (j : ℝ))
  have hnorm (k : ℤ) : ‖f k‖ ≤ |x.val + (k : ℝ) * 1| ^ (-(p.val.2 + (j : ℝ))) := by
    have hn : x.val + (k : ℝ) ≠ 0 := by
      simpa only [add_comm] using Riesz1.add_int_ne_zero_of_nonInt x.property k
    have hsign : |Real.sign (x.val + k)| = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero _ hn with h | h <;> simp [h]
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_div, abs_pow, hsign, one_pow,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), one_div,
      ← Real.rpow_neg (abs_nonneg _), mul_one]
  have hsumnorm : Summable (fun k => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hsum.1
  have hb : ‖∑' k, f k‖ ≤ B * δ ^ (-(p.val.2 + (j : ℝ))) :=
    (norm_tsum_le_tsum_norm hsumnorm).trans
      ((hsumnorm.tsum_le_tsum hnorm hsum.1).trans hsum.2)
  rw [PhysicalEnergy.kernelDerivative_images, abs_mul]
  change |A| * |∑' k, f k| ≤ _
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg A)
  have hpow : 0 ≤ δ ^ (-p.val.2 - (j : ℝ)) := Real.rpow_nonneg hδ.le _
  rw [show -(p.val.2 + (j : ℝ)) = -p.val.2 - (j : ℝ) by ring] at hm
  simp only [Real.norm_eq_abs] at hm
  nlinarith

end Riesz2.MarginalHessian
