/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic
public import Riesz1.Kernel.TransportKernelBounds

/-!
# Fourth-order error of a centered second difference

The odd Taylor coefficients cancel at the two endpoints. This gives the
fourth-order comparison needed for the interval coefficients in the proof of Lemma 5.4.
-/

public section

open Set

namespace Riesz2

/-- The error of a centered second difference is at most one twelfth of
the fourth-derivative bound times the fourth power of the step. -/
theorem centeredSecondDifference_fourthOrder_error {f : ℝ → ℝ} {x h C : ℝ}
    (hh : 0 < h) (hf : ContDiffOn ℝ 4 f (Icc (x - h) (x + h)))
    (hC : ∀ y ∈ Icc (x - h) (x + h), |iteratedDeriv 4 f y| ≤ C) :
    |f (x + h) + f (x - h) - 2 * f x - h ^ 2 * iteratedDeriv 2 f x| ≤
      C * h ^ 4 / 12 := by
  have hfx : ContDiffAt ℝ 4 f x := hf.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  have hplus : uIcc x (x + h) ⊆ Icc (x - h) (x + h) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hminus : uIcc x (x - h) ⊆ Icc (x - h) (x + h) := by
    rw [uIcc_of_ge (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  obtain ⟨a, ha, hea⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 3) (show x ≠ x + h by linarith) (hf.mono hplus)
  obtain ⟨b, hb, heb⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 3) (show x ≠ x - h by linarith) (hf.mono hminus)
  have hp (t : ℝ) (ht : x ≠ t) :
      taylorWithinEval f 3 (uIcc x t) x t = f x + (t - x) * iteratedDeriv 1 f x +
        (t - x) ^ 2 / 2 * iteratedDeriv 2 f x +
        (t - x) ^ 3 / 6 * iteratedDeriv 3 f x := by
    have hd (k : ℕ) (hk : k ≤ 4) : iteratedDerivWithin k f (uIcc x t) x =
        iteratedDeriv k f x :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc ht) (hfx.of_le (by exact_mod_cast hk))
        (left_mem_uIcc)
    rw [taylorWithinEval_succ f 2, taylorWithinEval_succ f 1,
      taylorWithinEval_succ f 0]
    simp only [
      taylor_within_zero_eval, hd 1 (by omega), hd 2 (by omega), hd 3 (by omega), smul_eq_mul]
    norm_num
    ring
  rw [hp _ (by linarith)] at hea heb
  norm_num at hea heb
  have haC := hC a (hplus ⟨ha.1.le, ha.2.le⟩)
  have hbC := hC b (hminus ⟨hb.1.le, hb.2.le⟩)
  have he : f (x + h) + f (x - h) - 2 * f x - h ^ 2 * iteratedDeriv 2 f x =
      (iteratedDeriv 4 f a + iteratedDeriv 4 f b) * h ^ 4 / 24 := by
    linear_combination hea + heb
  rw [he, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hh.le 4)]
  norm_num
  have hab : |iteratedDeriv 4 f a + iteratedDeriv 4 f b| ≤ 2 * C :=
    (abs_add_le _ _).trans (by linarith)
  nlinarith only [mul_le_mul_of_nonneg_right hab (pow_nonneg hh.le 4)]

/-- Unit-step version of the fourth-order centered-difference error. -/
theorem centeredSecondDifference_unit_error {f : ℝ → ℝ} {x C : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc (x - 1) (x + 1)))
    (hC : ∀ y ∈ Icc (x - 1) (x + 1), |iteratedDeriv 4 f y| ≤ C) :
    |f (x + 1) + f (x - 1) - 2 * f x - iteratedDeriv 2 f x| ≤ C / 12 := by
  simpa only [one_pow, one_mul, mul_one] using
    centeredSecondDifference_fourthOrder_error zero_lt_one hf hC

/-- Fourth-order error for a negative power, uniformly away from its
singularity. This is the continuous-versus-discrete comparison at every
unregularized lattice site. -/
theorem centeredSecondDifference_neg_rpow_error {s x : ℝ} (hs : 0 ≤ s) (hx : 2 ≤ x) :
    |(x + 1) ^ (-s) + (x - 1) ^ (-s) - 2 * x ^ (-s) -
      s * (s + 1) * x ^ (-s - 2)| ≤
      (s * (s + 1) * (s + 2) * (s + 3) * (1 / 2 : ℝ) ^ (-s - 4) / 12) *
        x ^ (-s - 4) := by
  let C := s * (s + 1) * (s + 2) * (s + 3)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hx0 : 0 < x := by linarith
  have hpow (k : ℕ) (y : ℝ) (hy : 0 < y) := Riesz1.iteratedDeriv_rpow_of_pos (-s) k y hy
  have h₂ : iteratedDeriv 2 (fun t : ℝ => t ^ (-s)) x = s * (s + 1) * x ^ (-s - 2) := by
    rw [hpow 2 x hx0]
    norm_num [Finset.prod_range_succ]
    ring
  have hf : ContDiffOn ℝ 4 (fun t : ℝ => t ^ (-s)) (Icc (x - 1) (x + 1)) := by
    intro y hy
    exact (Real.contDiffAt_rpow_const_of_ne (by linarith [hy.1] : y ≠ 0)).contDiffWithinAt
  have hb : ∀ y ∈ Icc (x - 1) (x + 1),
      |iteratedDeriv 4 (fun t : ℝ => t ^ (-s)) y| ≤
        C * ((1 / 2 : ℝ) ^ (-s - 4) * x ^ (-s - 4)) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have h₄ : iteratedDeriv 4 (fun t : ℝ => t ^ (-s)) y = C * y ^ (-s - 4) := by
      rw [hpow 4 y hy0]
      norm_num [Finset.prod_range_succ, C]
      ring
    rw [h₄, abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hy0.le _))]
    have hbound : (1 / 2 : ℝ) * x ≤ y := by linarith [hy.1]
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 / 2 * x)
      hbound (by linarith : -s - 4 ≤ 0)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hx0.le] at h
    exact mul_le_mul_of_nonneg_left h hC
  have h := centeredSecondDifference_unit_error hf hb
  rw [h₂] at h
  exact h.trans_eq (by dsimp only [C]; ring)

end Riesz2
