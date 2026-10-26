/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Quadratic forms of finite sums of rank-one matrices

Pure finite algebra over a commutative ring. Positivity is not required.
-/

@[expose] public section

open scoped BigOperators

namespace Riesz2

/-- Expand the quadratic form of a finite sum of weighted rank-one matrices. -/
theorem sum_quadratic_rankOne {R ι κ : Type*} [CommRing R] [Fintype ι]
    (t : Finset κ) (c : κ → R) (v : κ → ι → R) (u : ι → R) :
    (∑ i, ∑ j, u i * (∑ k ∈ t, c k * v k i * v k j) * u j) =
      ∑ k ∈ t, c k * (∑ i, v k i * u i) ^ 2 := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ k ∈ t, u i * (c k * v k i * v k j) * u j) =
        ∑ i, ∑ k ∈ t, ∑ j, u i * (c k * v k i * v k j) * u j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k ∈ t, ∑ i, ∑ j, u i * (c k * v k i * v k j) * u j := Finset.sum_comm
    _ = ∑ k ∈ t, c k * (∑ i, v k i * u i) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Riesz2
