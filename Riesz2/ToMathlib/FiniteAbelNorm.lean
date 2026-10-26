/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

/-!
# Finite summation by parts in a real normed space

The endpoint term is retained for every length, including zero. The norm
estimate applies in particular to Gaussian linear forms regarded as L² vectors.
-/

public section

open scoped BigOperators

namespace Riesz2.FiniteAbel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Summation by parts against prefix sums, with the endpoint at `R`.
This is the finite algebra used in the proof of Lemma 5.5. -/
theorem sum_eq_prefix_sums (a : ℕ → ℝ) (z : ℕ → V) (R : ℕ) :
    (∑ k ∈ Finset.range R, a k • z k) =
      a R • (∑ k ∈ Finset.range R, z k) +
        ∑ k ∈ Finset.range R, (a k - a (k + 1)) • (∑ t ∈ Finset.range (k + 1), z t) := by
  let S := fun r => ∑ k ∈ Finset.range r, z k
  have hS (r : ℕ) : S (r + 1) = S r + z r := Finset.sum_range_succ z r
  change (∑ k ∈ Finset.range R, a k • z k) =
    a R • S R + ∑ k ∈ Finset.range R, (a k - a (k + 1)) • S (k + 1)
  induction R with
  | zero => simp [S]
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hS]
    simp only [smul_add, sub_smul]
    abel

/-- Minkowski's bound after finite summation by parts. No moment or
summability hypothesis is needed for a finite sequence in a normed space. -/
theorem norm_sum_le_prefix_sums (a : ℕ → ℝ) (z : ℕ → V) (R : ℕ) :
    ‖∑ k ∈ Finset.range R, a k • z k‖ ≤
      |a R| * ‖∑ k ∈ Finset.range R, z k‖ +
        ∑ k ∈ Finset.range R,
          |a k - a (k + 1)| * ‖∑ t ∈ Finset.range (k + 1), z t‖ := by
  rw [sum_eq_prefix_sums]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_smul _ _).le.trans_eq (by rw [Real.norm_eq_abs])
  · calc ‖∑ k ∈ Finset.range R, (a k - a (k + 1)) •
          (∑ t ∈ Finset.range (k + 1), z t)‖ ≤
        ∑ k ∈ Finset.range R, ‖(a k - a (k + 1)) •
          (∑ t ∈ Finset.range (k + 1), z t)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs]

end Riesz2.FiniteAbel
