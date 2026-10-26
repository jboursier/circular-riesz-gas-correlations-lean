/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.TruncatedCoercivity

/-!
# Squared cyclic interval sums of a centered indicator

Counting the total mass and maximum overlap gives the interval convolution
estimate used in the proof of Lemma 6.5.
-/

public section
noncomputable section

open Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2

/-- Every coordinate occurs exactly `r` times in the family of cyclic
interval sums, even when `r` is larger than the period. -/
theorem sum_cyclicGapSum (N : ℕ+) (r : ℕ) (y : Fin (N : ℕ) → ℝ) :
    (∑ i, cyclicGapSum N i r y) = (r : ℝ) * ∑ j, y j := by
  unfold cyclicGapSum
  rw [sum_comm]
  have hs (a : ℕ) :
      (∑ i : Fin (N : ℕ), y ⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩) = ∑ j, y j := by
    apply Fintype.sum_equiv (Equiv.addRight (a : Fin (N : ℕ)))
    intro i
    congr 1
    apply Fin.ext
    simp [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
  simp_rw [hs]
  simp [nsmul_eq_mul]

/-- The overlap of an interval and an arbitrary set is bounded by the
smaller of their cardinalities. The interval length is at most the period. -/
theorem cyclicGapSum_indicator_le (N : ℕ+) (I : Finset (Fin (N : ℕ)))
    (i : Fin (N : ℕ)) {r : ℕ} (hr : r ≤ (N : ℕ)) :
    0 ≤ cyclicGapSum N i r (fun j => if j ∈ I then 1 else 0) ∧
      cyclicGapSum N i r (fun j => if j ∈ I then 1 else 0) ≤ min (I.card : ℝ) (r : ℝ) := by
  classical
  rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N i hr]
  refine ⟨sum_nonneg (fun j _ => by split_ifs <;> norm_num), le_min ?_ ?_⟩
  · apply (sum_le_univ_sum_of_nonneg (fun j => by split_ifs <;> norm_num)).trans_eq
    simp
  · calc
      _ ≤ ∑ _j ∈ cyclicIndexInterval N i r, (1 : ℝ) :=
        sum_le_sum fun j _ => by split_ifs <;> norm_num
      _ = _ := by simp [card_cyclicIndexInterval N i hr]

/-- Squared interval sums of a centered indicator have the sharp overlap
bound `min(|I|,r) |I| r`. Subtracting the exact mean can only reduce energy. -/
theorem sum_sq_cyclicGapSum_centered_indicator_le (N : ℕ+)
    (I : Finset (Fin (N : ℕ))) {r : ℕ} (hr : r ≤ (N : ℕ)) (α : ℝ) :
    (∑ i, (cyclicGapSum N i r
      (fun j => α * ((if j ∈ I then 1 else 0) - (I.card : ℝ) / (N : ℝ)))) ^ 2) ≤
      α ^ 2 * (min (I.card : ℝ) (r : ℝ) * (I.card : ℝ) * (r : ℝ)) := by
  classical
  let A := fun i => cyclicGapSum N i r (fun j => if j ∈ I then 1 else 0)
  let b : ℝ := (r : ℝ) * (I.card : ℝ) / (N : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsum : (∑ i, A i) = (r : ℝ) * (I.card : ℝ) := by
    simpa [A] using sum_cyclicGapSum N r (fun j => if j ∈ I then 1 else 0)
  have hsq : (∑ i, A i ^ 2) ≤ min (I.card : ℝ) (r : ℝ) * (I.card : ℝ) * (r : ℝ) := by
    calc
      _ ≤ ∑ i, min (I.card : ℝ) (r : ℝ) * A i := by
        apply sum_le_sum
        intro i _
        have hh := cyclicGapSum_indicator_le N I i hr
        nlinarith
      _ = _ := by rw [← mul_sum, hsum]; ring
  have hcenter : (∑ i, (A i - b) ^ 2) ≤ ∑ i, A i ^ 2 := by
    have he : (∑ i, (A i - b) ^ 2) = (∑ i, A i ^ 2) -
        2 * b * (∑ i, A i) + (N : ℝ) * b ^ 2 := by
      have hterm (i) : (A i - b) ^ 2 = A i ^ 2 - (2 * b) * A i + b ^ 2 := by ring
      simp_rw [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum]
      simp [mul_assoc]
    rw [he, hsum]
    have hb : (N : ℝ) * b = (r : ℝ) * (I.card : ℝ) := by dsimp [b]; field_simp
    nlinarith [mul_nonneg hN.le (sq_nonneg b), congrArg (fun x : ℝ => x * b) hb]
  have hterm (i : Fin (N : ℕ)) :
      cyclicGapSum N i r (fun j => α * ((if j ∈ I then 1 else 0) -
        (I.card : ℝ) / (N : ℝ))) = α * (A i - b) := by
    simp only [cyclicGapSum, mul_sub, sum_sub_distrib, ← mul_sum,
      sum_const, card_range, nsmul_eq_mul, A, b]
    ring
  simp_rw [hterm, mul_pow, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (hcenter.trans hsq) (sq_nonneg α)

end Riesz2
