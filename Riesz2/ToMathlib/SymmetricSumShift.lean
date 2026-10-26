/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Endpoint terms for symmetric integer sums

Finite identities needed before passing to a renormalized limit.
-/

public section

open scoped BigOperators

namespace Riesz2

variable {R : Type*} [AddCommGroup R]

/-- Increasing a symmetric integer interval adds its two endpoints. -/
theorem sum_symmetric_succ (f : ℤ → R) (M : ℕ) :
    (∑ l ∈ Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ), f l) =
      f (-((M + 1 : ℕ) : ℤ)) +
        (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f l) + f ((M + 1 : ℕ) : ℤ) := by
  have heq : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
      insert (-((M + 1 : ℕ) : ℤ))
        (insert ((M + 1 : ℕ) : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [heq, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp)]
  abel

/-- A unit translation of a symmetric sum retains exactly two boundary terms. -/
theorem sum_symmetric_shift (f : ℤ → R) (M : ℕ) :
    (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f (l + 1)) =
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f l) + f ((M : ℤ) + 1) - f (-(M : ℤ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_symmetric_succ, sum_symmetric_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one,
      show -((M : ℤ) + 1) + 1 = -(M : ℤ) by ring]
    abel

end Riesz2
