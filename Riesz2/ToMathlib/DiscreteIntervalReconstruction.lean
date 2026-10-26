/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-!
# Triangular reconstruction from discrete second differences

Finite summation by parts for a sequence in a commutative ring on a natural-number interval.
No decay, convergence, or sign hypotheses are involved.
-/

@[expose] public section

open scoped BigOperators

namespace Riesz2

variable {R : Type*} [CommRing R]

/-- Discrete integration by parts with a triangular weight, retaining both boundary terms. -/
theorem triangular_second_difference_sum (v : ℕ → R) {d m : ℕ} (hdm : d ≤ m) :
    (∑ r ∈ Finset.Icc (d + 1) m,
      ((r : R) - d) * (v (r - 1) + v (r + 1) - 2 * v r)) =
      v d - v m + ((m : R) - d) * (v (m + 1) - v m) := by
  induction m, hdm using Nat.le_induction with
  | base => simp
  | succ m hdm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- Reconstruct a sequence from its interior curvatures and its last first difference.
The last coefficient is independent of any choice of continuation past `m`. -/
theorem triangular_reconstruction (v q : ℕ → R) {d m : ℕ} (hdm : d ≤ m)
    (hcurv : ∀ r, d < r → r < m → q r = v (r - 1) + v (r + 1) - 2 * v r)
    (hend : q m = v (m - 1) - v m) :
    v d - v m = ∑ r ∈ Finset.Icc (d + 1) m, ((r : R) - d) * q r := by
  by_cases hdm' : d = m
  · subst d
    simp
  have hlt : d < m := lt_of_le_of_ne hdm hdm'
  have hsum := triangular_second_difference_sum v hdm
  have hmodify :
      (∑ r ∈ Finset.Icc (d + 1) m, ((r : R) - d) * q r) =
        (∑ r ∈ Finset.Icc (d + 1) m,
          ((r : R) - d) * (v (r - 1) + v (r + 1) - 2 * v r)) -
        ((m : R) - d) * (v (m + 1) - v m) := by
    have hsplit (F : ℕ → R) : (∑ r ∈ Finset.Icc (d + 1) m, F r) =
        (∑ r ∈ Finset.Icc (d + 1) (m - 1), F r) + F m := by
      have hm : 1 ≤ m := by omega
      simpa only [Nat.sub_add_cancel hm] using
        Finset.sum_Icc_succ_top (a := d + 1) (b := m - 1) (by omega) F
    rw [hsplit, hsplit]
    rw [hend]
    have hint : (∑ r ∈ Finset.Icc (d + 1) (m - 1), ((r : R) - d) * q r) =
        ∑ r ∈ Finset.Icc (d + 1) (m - 1),
          ((r : R) - d) * (v (r - 1) + v (r + 1) - 2 * v r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hcurv r (by have := (Finset.mem_Icc.mp hr).1; omega)
        (by have := (Finset.mem_Icc.mp hr).2; omega)]
    rw [hint]
    ring
  rw [hmodify, hsum]
  ring

/-- Finite summation by parts against a cosine-type recurrence. Both endpoint
terms are retained, so it also applies before taking a conditionally convergent limit. -/
theorem cosine_second_difference_sum (v c : ℕ → R) (t : R) (hc0 : c 0 = 1)
    (hc1 : c 1 = t) (hrec : ∀ n, c (n + 2) + c n = 2 * t * c (n + 1)) (M : ℕ) :
    (2 * v 1 - 2 * v 0) +
        2 * (∑ r ∈ Finset.range M, (v (r + 2) + v r - 2 * v (r + 1)) * c (r + 1)) =
      (2 * t - 2) * (v 0 + 2 * (∑ r ∈ Finset.range M, v (r + 1) * c (r + 1))) +
        2 * (v (M + 1) * c M - v M * c (M + 1)) := by
  induction M with
  | zero => simp [hc0, hc1]; ring
  | succ M ih =>
    simp only [Finset.sum_range_succ]
    have hrecM := hrec M
    simp only [show M + 1 + 1 = M + 2 by omega]
    linear_combination ih + 2 * v (M + 1) * hrecM

end Riesz2
