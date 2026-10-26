/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic

/-!
# Finite Schur bounds

Counting-measure bounds for real matrices acting on arbitrary real normed spaces.
In particular the same estimates apply to real and complex sequences.
-/

public section

open scoped BigOperators

namespace Riesz2.FiniteSchurBounds

/-- Column sums control the counting-measure `ℓ¹` norm. -/
theorem sum_norm_le {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ι → κ → ℝ) (u : κ → E) {B : ℝ}
    (hcol : ∀ j, ∑ i, |A i j| ≤ B) :
    (∑ i, ‖∑ j, A i j • u j‖) ≤ B * ∑ j, ‖u j‖ := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j| * ‖u j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun j => A i j • u j)
    _ = ∑ j, (∑ i, |A i j|) * ‖u j‖ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, B * ‖u j‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hcol j) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- Row and column sums give the squared finite Schur estimate. -/
theorem sum_sq_norm_le {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ι → κ → ℝ) (u : κ → E) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, |A i j| ≤ B) (hcol : ∀ j, ∑ i, |A i j| ≤ B) :
    (∑ i, ‖∑ j, A i j • u j‖ ^ 2) ≤ B ^ 2 * ∑ j, ‖u j‖ ^ 2 := by
  have hpoint (i : ι) : ‖∑ j, A i j • u j‖ ^ 2 ≤
      B * ∑ j, |A i j| * ‖u j‖ ^ 2 := by
    have hnorm : ‖∑ j, A i j • u j‖ ≤ ∑ j, |A i j| * ‖u j‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun j => A i j • u j)
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => |A i j| * ‖u j‖) (f := fun j => |A i j|)
      (g := fun j => |A i j| * ‖u j‖ ^ 2)
      (fun j _ => abs_nonneg _) (fun j _ => by positivity)
      (fun j _ => le_of_eq (by ring))
    calc
      _ ≤ (∑ j, |A i j| * ‖u j‖) ^ 2 := by gcongr
      _ ≤ (∑ j, |A i j|) * ∑ j, |A i j| * ‖u j‖ ^ 2 := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (by positivity)
  calc
    _ ≤ ∑ i, B * ∑ j, |A i j| * ‖u j‖ ^ 2 := Finset.sum_le_sum fun i _ => hpoint i
    _ = B * ∑ j, (∑ i, |A i j|) * ‖u j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ B * ∑ j, B * ‖u j‖ ^ 2 := by
      gcongr with j
      exact hcol j
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The finite Schur estimate in norm form, without a nonzero-vector premise. -/
theorem sqrt_sum_sq_norm_le {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ι → κ → ℝ) (u : κ → E) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, |A i j| ≤ B) (hcol : ∀ j, ∑ i, |A i j| ≤ B) :
    Real.sqrt (∑ i, ‖∑ j, A i j • u j‖ ^ 2) ≤
      B * Real.sqrt (∑ j, ‖u j‖ ^ 2) := by
  have h := Real.sqrt_le_sqrt (sum_sq_norm_le A u hB hrow hcol)
  rwa [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB] at h

end Riesz2.FiniteSchurBounds
