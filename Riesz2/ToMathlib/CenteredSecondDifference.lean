/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-!
# Bounds for centered second differences

Subtracting a quadratic turns a lower bound on the second derivative into
convexity. Applying the midpoint inequality then bounds a centered difference.
-/

public section

namespace Riesz2

/-- A lower second derivative bound controls the centered difference on a unit interval. -/
theorem le_centeredSecondDifference {f f' f'' : ℝ → ℝ} {x c : ℝ}
    (hf : ContinuousOn f (Set.Icc (x - 1) (x + 1)))
    (hf' : ∀ y ∈ Set.Ioo (x - 1) (x + 1), HasDerivAt f (f' y) y)
    (hf'' : ∀ y ∈ Set.Ioo (x - 1) (x + 1), HasDerivAt f' (f'' y) y)
    (hc : ∀ y ∈ Set.Ioo (x - 1) (x + 1), c ≤ f'' y) :
    c ≤ f (x + 1) + f (x - 1) - 2 * f x := by
  have hconv : ConvexOn ℝ (Set.Icc (x - 1) (x + 1))
      (fun y => f y - c / 2 * (y - x) ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (hf.sub (by fun_prop))
      (f' := fun y => f' y - c * (y - x)) (f'' := fun y => f'' y - c)
    · intro y hy
      rw [interior_Icc] at hy ⊢
      convert ((hf' y hy).sub
        ((((hasDerivAt_id y).sub_const x).pow 2).const_mul (c / 2))).hasDerivWithinAt using 1
      · ext z
        simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      · simp only [id_eq]
        ring
    · intro y hy
      rw [interior_Icc] at hy ⊢
      convert ((hf'' y hy).sub
        (((hasDerivAt_id y).sub_const x).const_mul c)).hasDerivWithinAt using 1
      · rfl
      · ring
    · intro y hy
      rw [interior_Icc] at hy
      exact sub_nonneg.mpr (hc y hy)
  have h := hconv.2 (show x - 1 ∈ Set.Icc (x - 1) (x + 1) by constructor <;> linarith)
    (show x + 1 ∈ Set.Icc (x - 1) (x + 1) by constructor <;> linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num)
  have hm : (1 / 2 : ℝ) • (x - 1) + (1 / 2 : ℝ) • (x + 1) = x := by
    simp only [smul_eq_mul]; ring
  rw [hm] at h
  simp only [smul_eq_mul, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero] at h
  nlinarith

/-- Two bounds on the ordinary second derivative give the same bounds on the
centered unit second difference. -/
theorem centeredSecondDifference_bounds {f f' f'' : ℝ → ℝ} {x c C : ℝ}
    (hf : ContinuousOn f (Set.Icc (x - 1) (x + 1)))
    (hf' : ∀ y ∈ Set.Ioo (x - 1) (x + 1), HasDerivAt f (f' y) y)
    (hf'' : ∀ y ∈ Set.Ioo (x - 1) (x + 1), HasDerivAt f' (f'' y) y)
    (hc : ∀ y ∈ Set.Ioo (x - 1) (x + 1), c ≤ f'' y)
    (hC : ∀ y ∈ Set.Ioo (x - 1) (x + 1), f'' y ≤ C) :
    c ≤ f (x + 1) + f (x - 1) - 2 * f x ∧
      f (x + 1) + f (x - 1) - 2 * f x ≤ C := by
  refine ⟨le_centeredSecondDifference hf hf' hf'' hc, ?_⟩
  have h := le_centeredSecondDifference (f := fun y => -f y)
    (f' := fun y => -f' y) (f'' := fun y => -f'' y) (c := -C)
    hf.neg (fun y hy => (hf' y hy).neg) (fun y hy => (hf'' y hy).neg)
    (fun y hy => neg_le_neg (hC y hy))
  linarith

end Riesz2
