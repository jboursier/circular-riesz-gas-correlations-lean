/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.CyclicIndexInterval
public import Riesz1.Frozen.CyclicIndexDistance
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-!
# Counting cyclic intervals containing a pair

The intervals are the literal intervals. Lengths at most half the cycle
have a triangular pair count, including coincident and antipodal labels.
-/

public section

open scoped BigOperators Fin.NatCast

namespace Riesz2

/-- Membership in a cyclic interval is a bound on the forward residue. -/
theorem mem_cyclicIndexInterval_iff (N : ℕ+) (i a : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) : a ∈ cyclicIndexInterval N i r ↔ (a - i).val < r := by
  constructor
  · intro h
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp h
    have ht := Finset.mem_range.mp ht
    have hadd : i + (↑t : Fin (N : ℕ)) = a := by
      simpa only [Fin.ext_iff, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod] using
        congrArg Fin.val heq
    have hsub : a - i = (↑t : Fin (N : ℕ)) := by rw [← hadd]; abel
    rw [hsub, Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le ht hr)]
    exact ht
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(a - i).val, Finset.mem_range.mpr h, ?_⟩
    have heq : (⟨(i.val + (a - i).val) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)) =
        i + ↑(a - i).val := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
    rw [heq, Fin.cast_val_eq_self]
    abel

private theorem sum_fin_ite_Ico (N : ℕ+) (a b : ℕ) (hb : b ≤ (N : ℕ)) :
    (∑ j : Fin (N : ℕ), if a ≤ j.val ∧ j.val < b then (1 : ℝ) else 0) = (b - a : ℕ) := by
  rw [← Finset.sum_filter]
  have h := Finset.sum_bij (s := Finset.univ.filter (fun j : Fin (N : ℕ) => a ≤ j.val ∧ j.val < b))
    (t := Finset.Ico a b) (f := fun _ => (1 : ℝ)) (g := fun _ => (1 : ℝ))
    (fun j _ => j.val) ?_ ?_ ?_ (fun _ _ => rfl)
  · simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] using h
  · intro j hj
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2
  · intro j _ k _ h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hj'.2 hb⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩

/-- The number of starts of length-`r` cyclic intervals containing two fixed labels.
This is the finite counting step in Subsection 2.5. -/
theorem cyclicIndexInterval_pair_count (N : ℕ+) {r : ℕ} (hr : 2 * r ≤ (N : ℕ))
    (a b : Fin (N : ℕ)) :
    (∑ i : Fin (N : ℕ),
      (if a ∈ cyclicIndexInterval N i r then (1 : ℝ) else 0) *
        (if b ∈ cyclicIndexInterval N i r then (1 : ℝ) else 0)) =
      ((r - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) := by
  have hrN : r ≤ (N : ℕ) := by omega
  simp_rw [mem_cyclicIndexInterval_iff N _ _ hrN]
  let q := (b - a).val
  have hq : q < (N : ℕ) := (b - a).isLt
  have htrans :
      (∑ i : Fin (N : ℕ), (if (a - i).val < r then (1 : ℝ) else 0) *
        (if (b - i).val < r then (1 : ℝ) else 0)) =
      ∑ j : Fin (N : ℕ), (if j.val < r then (1 : ℝ) else 0) *
        (if (j.val + q) % (N : ℕ) < r then (1 : ℝ) else 0) := by
    apply Fintype.sum_equiv (Equiv.subLeft a)
    intro i
    have heq : (a - i) + (b - a) = b - i := by abel
    simp only [Equiv.subLeft_apply, ← Fin.val_add, heq, q]
  rw [htrans]
  have hterm (j : Fin (N : ℕ)) :
      (if j.val < r then (1 : ℝ) else 0) *
        (if (j.val + q) % (N : ℕ) < r then (1 : ℝ) else 0) =
      (if 0 ≤ j.val ∧ j.val < r - q then (1 : ℝ) else 0) +
        (if (N : ℕ) - q ≤ j.val ∧ j.val < r then (1 : ℝ) else 0) := by
    have hj := j.isLt
    by_cases hwrap : j.val + q < (N : ℕ)
    · rw [Nat.mod_eq_of_lt hwrap]
      split_ifs <;> norm_num at * <;> omega
    · have hmod : (j.val + q) % (N : ℕ) = j.val + q - (N : ℕ) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      split_ifs <;> norm_num at * <;> omega
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, sum_fin_ite_Ico N 0 (r - q) (by omega),
    sum_fin_ite_Ico N ((N : ℕ) - q) r hrN]
  have hdist : Riesz1.cyclicIndexDistance N a b = min q ((N : ℕ) - q) := by
    dsimp [q]
    simp only [Riesz1.cyclicIndexDistance, Nat.dist, Fin.val_sub]
    have ha := a.isLt
    have hb := b.isLt
    by_cases hab : a.val ≤ b.val
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  rw [hdist, ← Nat.cast_add]
  congr 1
  omega

end Riesz2
