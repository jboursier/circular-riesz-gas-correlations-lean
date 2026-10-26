/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-!
# Endpoint cancellation in finite interval forces

A pinned coordinate variation changes its two adjacent gaps with opposite
signs. Summing interval derivatives cancels every interior contribution
and leaves exactly two endpoints. The algebra works in any finite
commutative group, including even cycles and intervals of any length.
-/

public section
open scoped BigOperators

namespace Riesz2.FiniteIntervalForce

/-- Pairing a coefficient function with a translated unit mass evaluates
the coefficient at the translated label. -/
theorem sum_mul_single_translate {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h : G → ℝ) (u v : G) :
    (∑ i : G, h i * (Pi.single v 1 : G → ℝ) (i + u)) = h (v - u) := by
  classical
  rw [Finset.sum_eq_single (v - u)]
  · simp
  · intro i _ hi
    have he : i + u ≠ v := by intro he; apply hi; rw [← he]; abel
    simp [he]
  · simp

/-- A finite family of interval derivatives paired with a pinned
variation has only the two endpoint terms. This is the deterministic
cancellation needed before estimating exterior forces in Appendix C. It does not assume estimates on those forces. -/
theorem sum_pinned_intervals {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h : G → ℝ) (j e : G) (r : ℕ) :
    (∑ i : G, h i * ∑ a ∈ Finset.range r,
      ((Pi.single j 1 : G → ℝ) (i + a • e) -
        (Pi.single (j + e) 1 : G → ℝ) (i + a • e))) =
      h (j + e - r • e) - h (j + e) := by
  classical
  simp_rw [Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib, sum_mul_single_translate]
  have he (a : ℕ) : j - a • e = j + e - (a + 1) • e := by
    rw [add_nsmul, one_nsmul]
    abel
  simp_rw [he]
  simpa only [Finset.sum_sub_distrib, zero_nsmul, sub_zero] using
    Finset.sum_range_sub (fun a : ℕ => h (j + e - a • e)) r

end Riesz2.FiniteIntervalForce
