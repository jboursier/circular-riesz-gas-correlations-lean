/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DerivativeCommutators
public import Riesz2.ToMathlib.FiniteSchurBounds
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Derivative commutators and inverse rows, part 2

Row estimates used in the proof of Lemma 5.11, from the interval split
and inverse-row theorem in `DerivativeCommutators`. The coefficients are
explicit and follow from `PeriodizedMatrixBounds`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast Matrix ENNReal
open Finset

attribute [local instance] Classical.propDecidable

namespace Riesz2.DerivativeCommutators

/-- In the endpoint count of the proof of Lemma 5.11, changing a column
can change an interval indicator only at one of its two endpoints. -/
theorem interval_indicator_change_endpoints (N : ℕ+) {l : ℕ}
    (hl : 0 < l) (hlN : l < (N : ℕ)) (i b : Fin (N : ℕ))
    (h : (b + 1 ∈ cyclicIndexInterval N i l) ≠
      (b ∈ cyclicIndexInterval N i l)) :
    i = b + 1 ∨ i = b + 1 - (l : Fin (N : ℕ)) := by
  have hlle : l ≤ (N : ℕ) := hlN.le
  have hmem := mem_cyclicIndexInterval_iff N i b hlle
  have hmem' := mem_cyclicIndexInterval_iff N i (b + 1) hlle
  have hv : (b + 1 - i).val = ((b - i).val + 1) % (N : ℕ) := by
    have heq : b + 1 - i = (b - i) + 1 := by abel
    rw [heq, Fin.val_add]
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < (N : ℕ))]
  have hz := (b - i).isLt
  have hedge : (b - i).val + 1 = (N : ℕ) ∨ (b - i).val + 1 = l := by
    by_contra hn
    push Not at hn
    have hlt : (b - i).val + 1 < (N : ℕ) := by omega
    have hequiv : (b + 1 ∈ cyclicIndexInterval N i l) ↔
        (b ∈ cyclicIndexInterval N i l) := by
      rw [hmem', hmem, hv, Nat.mod_eq_of_lt hlt]
      omega
    exact h (propext hequiv)
  rcases hedge with hedge | hedge
  · left
    have heq : b + 1 - i = 0 := by
      apply Fin.ext
      simp only [hv, hedge, Nat.mod_self, Fin.val_zero]
    exact (sub_eq_zero.mp heq).symm
  · right
    have heq : b + 1 - i = (l : Fin (N : ℕ)) := by
      apply Fin.ext
      rw [hv, hedge, Fin.val_natCast, Nat.mod_eq_of_lt hlN]
    calc i = b + 1 - (b + 1 - i) := by abel
      _ = b + 1 - (l : Fin (N : ℕ)) := by rw [heq]

/-- At most two starts of intervals of a fixed length change their indicator
across a column edge. This is the endpoint cancellation in the proof of Lemma 5.11. -/
theorem sum_interval_indicator_increment_le_two (N : ℕ+) {l : ℕ}
    (hl : 0 < l) (hlN : l < (N : ℕ)) (b : Fin (N : ℕ)) :
    (∑ i : Fin (N : ℕ),
      |(if b + 1 ∈ cyclicIndexInterval N i l then (1 : ℝ) else 0) -
        (if b ∈ cyclicIndexInterval N i l then (1 : ℝ) else 0)|) ≤ 2 := by
  have hterm (i : Fin (N : ℕ)) :
      |(if b + 1 ∈ cyclicIndexInterval N i l then (1 : ℝ) else 0) -
        (if b ∈ cyclicIndexInterval N i l then (1 : ℝ) else 0)| ≤
      (if i = b + 1 then (1 : ℝ) else 0) +
        (if i = b + 1 - (l : Fin (N : ℕ)) then (1 : ℝ) else 0) := by
    by_cases heq : (b + 1 ∈ cyclicIndexInterval N i l) =
        (b ∈ cyclicIndexInterval N i l)
    · simp only [heq, sub_self, abs_zero]
      positivity
    · have hi := interval_indicator_change_endpoints N hl hlN i b heq
      rcases hi with hi | hi <;> simp only [hi, ↓reduceIte] <;> split_ifs <;> norm_num
  calc
    _ ≤ ∑ i : Fin (N : ℕ),
        ((if i = b + 1 then (1 : ℝ) else 0) +
          (if i = b + 1 - (l : Fin (N : ℕ)) then (1 : ℝ) else 0)) :=
      sum_le_sum fun i _ => hterm i
    _ = 2 := by simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]; norm_num

/-- The scale for a discarded entry, including both the radius cutoff and
the distance between its two labels. -/
theorem discarded_entry_length_scale (N : ℕ+) (i₀ k : Fin (N : ℕ))
    (r : Fin ((N : ℕ) / 2)) {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 4)
    (hdis : ¬ IsRetained N i₀ η k r) (a b : Fin (N : ℕ))
    (ha : a ∈ cyclicIndexInterval N k (r.val + 1))
    (hb : b ∈ cyclicIndexInterval N k (r.val + 1)) :
    (rowCutoff N i₀ η a + (Riesz1.cyclicIndexDistance N a b : ℝ)) / 4 ≤
      ((r.val + 1 : ℕ) : ℝ) := by
  have hlen := discarded_interval_length_lower N i₀ k r hη hdis a ha
  have hdist := distance_lt_interval_length N k (by have := r.isLt; omega) a b ha hb
  have hdist' : (Riesz1.cyclicIndexDistance N a b : ℝ) < ((r.val + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hdist
  have hpos : (0 : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by positivity
  have hlen' : η * weightRadius N a i₀ < ((r.val + 1 : ℕ) : ℝ) * (1 + η) :=
    (div_lt_iff₀ (by linarith)).mp hlen
  have hcut : rowCutoff N i₀ η a ≤ ((r.val + 1 : ℕ) : ℝ) := by
    apply max_le
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le r.val)
    · nlinarith
  linarith

/-- The same lower length scale holds when an interval contains either side
of a column edge. The neighboring distance costs only an absolute factor. -/
theorem discarded_edge_length_scale (N : ℕ+) (i₀ k : Fin (N : ℕ))
    (r : Fin ((N : ℕ) / 2)) {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 4)
    (hdis : ¬ IsRetained N i₀ η k r) (a b : Fin (N : ℕ))
    (ha : a ∈ cyclicIndexInterval N k (r.val + 1))
    (hb : b ∈ cyclicIndexInterval N k (r.val + 1) ∨
      b + 1 ∈ cyclicIndexInterval N k (r.val + 1)) :
    (rowCutoff N i₀ η a + (Riesz1.cyclicIndexDistance N a b : ℝ)) / 4 ≤
      ((r.val + 1 : ℕ) : ℝ) := by
  rcases hb with hb | hb
  · exact discarded_entry_length_scale N i₀ k r hη hη' hdis a b ha hb
  · have hlen := discarded_interval_length_lower N i₀ k r hη hdis a ha
    have hd := distance_lt_interval_length N k (by have := r.isLt; omega) a (b + 1) ha hb
    have htri := cyclicIndexDistance_triangle a (b + 1) b
    have hedge : Riesz1.cyclicIndexDistance N (b + 1) b ≤ 1 := by
      have hN := N.pos
      have hval := b.isLt
      unfold Riesz1.cyclicIndexDistance Nat.dist
      have hN2 : 1 < (N : ℕ) := by have := r.isLt; omega
      simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hN2]
      by_cases hm : b.val + 1 < (N : ℕ)
      · simp only [Nat.mod_eq_of_lt hm]
        omega
      · have heq : b.val + 1 = (N : ℕ) := by omega
        rw [heq, Nat.mod_self]
        omega
    have hd' : (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ ((r.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show Riesz1.cyclicIndexDistance N a b ≤ r.val + 1 by omega)
    have hlen' := (div_lt_iff₀ (by linarith : 0 < 1 + η)).mp hlen
    have hpos : (0 : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by positivity
    have hcut : rowCutoff N i₀ η a ≤ ((r.val + 1 : ℕ) : ℝ) := by
      apply max_le
      · exact_mod_cast Nat.succ_le_succ (Nat.zero_le r.val)
      · nlinarith
    linarith

/-- Internal power-tail estimate over the permitted interval lengths. -/
theorem interval_length_power_tail {p R : ℝ} (hp : 1 < p) (hR : 1 ≤ R) (K : ℕ) :
    (∑ r : Fin K, if R ≤ ((r.val + 1 : ℕ) : ℝ) then
      ((r.val + 1 : ℕ) : ℝ) ^ (-p) else 0) ≤
      (1 + 1 / (p - 1)) * R ^ (1 - p) := by
  have hs : Summable (fun k : ℕ =>
      if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-p) else 0) := by
    apply Summable.of_nonneg_of_le _ _ (summable_one_add_rpow_neg hp)
    · intro k; split_ifs <;> positivity
    · intro k; split_ifs
      · exact le_rfl
      · positivity
  calc
    _ = (∑ k ∈ range K,
        if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-p) else 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro r _
      simp only [Nat.cast_add, Nat.cast_one, add_comm (r.val : ℝ) 1]
    _ ≤ (∑' k : ℕ, if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-p) else 0) :=
      hs.sum_le_tsum _ (fun k _ => by split_ifs <;> positivity)
    _ ≤ _ := tsum_tail_indicator_le hp hR

/-- Internal conversion from the positive cutoff used in a power tail to
the row-distance scale. -/
theorem cutoff_power_bound {v p : ℝ} (hv : 0 < v) (hp : 0 ≤ p) :
    (max 1 (v / 4)) ^ (-p) ≤ 4 ^ p * v ^ (-p) := by
  calc
    _ ≤ (v / 4) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right _ _) (by linarith)
    _ = 4 ^ p * v ^ (-p) := by
      rw [Real.div_rpow hv.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) p, div_inv_eq_mul]
      ring_nf

/-- Fixed-length entry estimate for the discarded intervals in
the proof of Lemma 5.11. The amplitude is the original coefficient upper bound. -/
theorem discarded_slice_entry_bound (N : ℕ+) (i₀ a b : Fin (N : ℕ))
    {η s A : ℝ} (hη : 0 < η) (hη' : η < 1 / 4) (hA : 0 ≤ A)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hα : ∀ k r, 0 ≤ α k r ∧ α k r ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2)) (r : Fin ((N : ℕ) / 2)) :
    (∑ k : Fin (N : ℕ), if IsRetained N i₀ η k r then 0 else
      α k r * (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) ≤
    A * (if max 1 ((rowCutoff N i₀ η a +
        (Riesz1.cyclicIndexDistance N a b : ℝ)) / 4) ≤ ((r.val + 1 : ℕ) : ℝ)
      then ((r.val + 1 : ℕ) : ℝ) ^ (-s - 1) else 0) := by
  let l : ℝ := ((r.val + 1 : ℕ) : ℝ)
  have hl : 0 < l := by dsimp [l]; positivity
  split_ifs with hscale
  · calc
      _ ≤ ∑ k : Fin (N : ℕ), A * l ^ (-s - 2) *
          (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
            (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
        apply sum_le_sum
        intro k _
        split_ifs <;> simp only [mul_one, mul_zero] <;>
          first | exact (hα k r).2 | positivity
      _ = A * l ^ (-s - 2) *
          ((r.val + 1 - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) := by
        rw [← cyclicIndexInterval_pair_count N (by have := r.isLt; omega) a b, mul_sum]
        apply sum_congr rfl
        intro k _
        ring_nf
      _ ≤ A * l ^ (-s - 2) * l := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [l]
        exact_mod_cast Nat.sub_le (r.val + 1) _
      _ = A * l ^ (-s - 1) := by
        rw [mul_assoc, ← Real.rpow_add_one hl.ne']
        congr 1
        ring_nf
  · rw [mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro k _
    by_cases hret : IsRetained N i₀ η k r
    · simp only [hret, ↓reduceIte]
    · by_cases ha : a ∈ cyclicIndexInterval N k (r.val + 1)
      · by_cases hb : b ∈ cyclicIndexInterval N k (r.val + 1)
        · have hlen := discarded_entry_length_scale N i₀ k r hη hη' hret a b ha hb
          have h1 : (1 : ℝ) ≤ ((r.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r.val
          exact False.elim (hscale (max_le h1 hlen))
        · simp only [hret, ha, hb, ↓reduceIte, mul_zero]
      · simp only [hret, ha, ↓reduceIte, mul_zero, zero_mul]

/-- The first pointwise assertion of the proof of Lemma 5.11, with an
explicit uniform constant and the original interval coefficient amplitude. -/
theorem discarded_entry_bound (N : ℕ+) (i₀ a b : Fin (N : ℕ))
    {η s A : ℝ} (hη : 0 < η) (hη' : η < 1 / 4) (hs : 0 < s) (hA : 0 ≤ A)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hα : ∀ k r, 0 ≤ α k r ∧ α k r ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2))
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hM : ∀ a b, M a b = ∑ k, ∑ r, α k r *
      (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) :
    |discardedMatrix N i₀ η α M a b| ≤
      ((1 + 1 / s) * 4 ^ s) * A *
        (rowCutoff N i₀ η a + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s) := by
  rw [discardedMatrix_entries N i₀ η α M hM]
  rw [abs_of_nonneg (by
    apply sum_nonneg; intro k _; apply sum_nonneg; intro r _
    have hk := (hα k r).1
    split_ifs <;> first | exact le_rfl | positivity)]
  rw [sum_comm]
  let R := max 1 ((rowCutoff N i₀ η a +
    (Riesz1.cyclicIndexDistance N a b : ℝ)) / 4)
  have hR : 1 ≤ R := le_max_left _ _
  calc
    _ ≤ ∑ r, A * (if R ≤ ((r.val + 1 : ℕ) : ℝ) then
          ((r.val + 1 : ℕ) : ℝ) ^ (-s - 1) else 0) :=
      sum_le_sum fun r _ => discarded_slice_entry_bound N i₀ a b hη hη' hA α hα r
    _ = A * ∑ r : Fin ((N : ℕ) / 2),
        (if R ≤ ((r.val + 1 : ℕ) : ℝ) then
          ((r.val + 1 : ℕ) : ℝ) ^ (-(s + 1)) else 0) := by
      have he : -s - 1 = -(s + 1) := by ring_nf
      simp only [he, mul_sum]
    _ ≤ A * ((1 + 1 / ((s + 1) - 1)) * R ^ (1 - (s + 1))) :=
      mul_le_mul_of_nonneg_left (interval_length_power_tail (by linarith) hR _) hA
    _ = A * (1 + 1 / s) * R ^ (-s) := by ring_nf
    _ ≤ A * (1 + 1 / s) * (4 ^ s *
        (rowCutoff N i₀ η a + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd0 : (0 : ℝ) ≤ (Riesz1.cyclicIndexDistance N a b : ℝ) := Nat.cast_nonneg _
      have hc := one_le_rowCutoff N i₀ η a
      exact cutoff_power_bound (by linarith) hs.le
    _ = _ := by ring_nf

/-- Fixed-length endpoint estimate for the proof of Lemma 5.11. The set of
retained intervals stays fixed while the column indicator changes. -/
theorem discarded_slice_increment_bound (N : ℕ+) (i₀ a b : Fin (N : ℕ))
    {η s A : ℝ} (hη : 0 < η) (hη' : η < 1 / 4) (hA : 0 ≤ A)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hα : ∀ k r, 0 ≤ α k r ∧ α k r ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2)) (r : Fin ((N : ℕ) / 2)) :
    (∑ k : Fin (N : ℕ), |if IsRetained N i₀ η k r then 0 else
      α k r * (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        ((if b + 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) -
          (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0))|) ≤
    2 * A * (if max 1 ((rowCutoff N i₀ η a +
        (Riesz1.cyclicIndexDistance N a b : ℝ)) / 4) ≤ ((r.val + 1 : ℕ) : ℝ)
      then ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2) else 0) := by
  let l : ℝ := ((r.val + 1 : ℕ) : ℝ)
  have hl : 0 < l := by dsimp [l]; positivity
  split_ifs with hscale
  · calc
      _ ≤ ∑ k : Fin (N : ℕ), A * l ^ (-s - 2) *
          |(if b + 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) -
            (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)| := by
        apply sum_le_sum
        intro k _
        have hk := (hα k r).1
        have hk' := (hα k r).2
        split_ifs <;> simp only [mul_one, mul_zero, zero_mul, sub_self,
          sub_zero, zero_sub, abs_zero, abs_mul, abs_one, abs_neg, abs_of_nonneg hk, mul_one] <;>
          first | exact hk' | exact le_rfl | positivity
      _ = A * l ^ (-s - 2) * ∑ k : Fin (N : ℕ),
          |(if b + 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) -
            (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)| := by
        rw [mul_sum]
      _ ≤ A * l ^ (-s - 2) * 2 :=
        mul_le_mul_of_nonneg_left
          (sum_interval_indicator_increment_le_two N (by omega)
            (by have := r.isLt; omega) b) (by positivity)
      _ = _ := by dsimp [l]; ring_nf
  · rw [mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro k _
    by_cases hret : IsRetained N i₀ η k r
    · simp only [hret, ↓reduceIte, abs_zero]
    · by_cases ha : a ∈ cyclicIndexInterval N k (r.val + 1)
      · have hedge : b ∉ cyclicIndexInterval N k (r.val + 1) ∧
            b + 1 ∉ cyclicIndexInterval N k (r.val + 1) := by
          constructor <;> intro hb
          · have hlen := discarded_edge_length_scale N i₀ k r hη hη' hret a b ha (Or.inl hb)
            exact hscale (max_le (by dsimp [l] at hl; exact_mod_cast Nat.succ_pos r.val) hlen)
          · have hlen := discarded_edge_length_scale N i₀ k r hη hη' hret a b ha (Or.inr hb)
            exact hscale (max_le (by exact_mod_cast Nat.succ_pos r.val) hlen)
        simp only [hret, ha, hedge.1, hedge.2, ↓reduceIte, sub_self, mul_zero, abs_zero]
      · simp only [hret, ha, ↓reduceIte, mul_zero, zero_mul, abs_zero]

/-- The second pointwise assertion of the proof of Lemma 5.11, with
an explicit constant independent of the retention parameter. -/
theorem discarded_increment_bound (N : ℕ+) (i₀ a b : Fin (N : ℕ))
    {η s A : ℝ} (hη : 0 < η) (hη' : η < 1 / 4) (hs : 0 < s) (hA : 0 ≤ A)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hα : ∀ k r, 0 ≤ α k r ∧ α k r ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2))
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hM : ∀ a b, M a b = ∑ k, ∑ r, α k r *
      (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) :
    |discardedMatrix N i₀ η α M a (b + 1) - discardedMatrix N i₀ η α M a b| ≤
      (2 * (1 + 1 / (s + 1)) * 4 ^ (s + 1)) * A *
        (rowCutoff N i₀ η a + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-1 - s) := by
  rw [discardedMatrix_entries N i₀ η α M hM,
    discardedMatrix_entries N i₀ η α M hM, ← sum_sub_distrib]
  have hterm (k : Fin (N : ℕ)) :
      (∑ r, if IsRetained N i₀ η k r then 0 else α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b + 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) -
      (∑ r, if IsRetained N i₀ η k r then 0 else α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) =
      ∑ r, if IsRetained N i₀ η k r then 0 else α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        ((if b + 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) -
          (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    split_ifs <;> ring_nf
  simp_rw [hterm]
  rw [sum_comm]
  let R := max 1 ((rowCutoff N i₀ η a +
    (Riesz1.cyclicIndexDistance N a b : ℝ)) / 4)
  have hR : 1 ≤ R := le_max_left _ _
  calc
    _ ≤ ∑ r, ∑ k, |if IsRetained N i₀ η k r then 0 else α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        ((if b + 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) -
          (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0))| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ r, 2 * A * (if R ≤ ((r.val + 1 : ℕ) : ℝ) then
        ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2) else 0) :=
      sum_le_sum fun r _ => discarded_slice_increment_bound N i₀ a b hη hη' hA α hα r
    _ = (2 * A) * ∑ r : Fin ((N : ℕ) / 2),
        (if R ≤ ((r.val + 1 : ℕ) : ℝ) then
          ((r.val + 1 : ℕ) : ℝ) ^ (-(s + 2)) else 0) := by
      have he : -s - 2 = -(s + 2) := by ring_nf
      simp only [he, mul_sum]
    _ ≤ (2 * A) * ((1 + 1 / ((s + 2) - 1)) * R ^ (1 - (s + 2))) :=
      mul_le_mul_of_nonneg_left (interval_length_power_tail (by linarith) hR _) (by positivity)
    _ = (2 * A) * (1 + 1 / (s + 1)) * R ^ (-(s + 1)) := by ring_nf
    _ ≤ (2 * A) * (1 + 1 / (s + 1)) * (4 ^ (s + 1) *
        (rowCutoff N i₀ η a + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-(s + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd0 : (0 : ℝ) ≤ (Riesz1.cyclicIndexDistance N a b : ℝ) := Nat.cast_nonneg _
      have hc := one_le_rowCutoff N i₀ η a
      exact cutoff_power_bound (by linarith) (by linarith)
    _ = _ := by ring_nf

/-- Finite shell summation for the shifted scale in the proof of Lemma 5.11. -/
theorem sum_row_scale_rpow_le (N : ℕ+) (a : Fin (N : ℕ))
    {p L : ℝ} (hp : 1 < p) (hL : 1 ≤ L) :
    (∑ b : Fin (N : ℕ), (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-p)) ≤
      (2 * (2 + 1 / (p - 1))) * L ^ (1 - p) := by
  have hL0 : 0 < L := by linarith
  have hnear := sum_weightRadius_le_range N a (t := 0) hL
  simp only [neg_zero, Real.rpow_zero, sum_const, nsmul_eq_mul, mul_one,
    card_range] at hnear
  have hfloor : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL0.le
  have hcount : ((univ.filter (fun b : Fin (N : ℕ) => weightRadius N b a ≤ L)).card : ℝ) ≤
      2 * L := hnear.trans (by gcongr)
  have htail := sum_weightRadius_tail_le N a hp hL
  have hpoint (b : Fin (N : ℕ)) :
      (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-p) ≤
      (if weightRadius N b a ≤ L then L ^ (-p) else 0) +
        (if L ≤ weightRadius N b a then weightRadius N b a ^ (-p) else 0) := by
    have hd0 : (0 : ℝ) ≤ (Riesz1.cyclicIndexDistance N a b : ℝ) := Nat.cast_nonneg _
    have hr : weightRadius N b a = 1 + (Riesz1.cyclicIndexDistance N a b : ℝ) :=
      weightRadius_eq_comm N b a
    by_cases h : weightRadius N b a ≤ L
    · calc
        _ ≤ L ^ (-p) := Real.rpow_le_rpow_of_nonpos hL0 (by linarith) (by linarith)
        _ ≤ _ := by
          simp only [h, ↓reduceIte]
          split_ifs
          · exact le_add_of_nonneg_right (Real.rpow_nonneg
              (by linarith [one_le_weightRadius N b a]) _)
          · simp only [add_zero, le_refl]
    · have h' : L ≤ weightRadius N b a := le_of_lt (lt_of_not_ge h)
      simp only [h, h', ↓reduceIte, zero_add]
      exact Real.rpow_le_rpow_of_nonpos (by linarith [one_le_weightRadius N b a])
        (by rw [hr]; linarith) (by linarith)
  calc
    _ ≤ (∑ b : Fin (N : ℕ), if weightRadius N b a ≤ L then L ^ (-p) else 0) +
        (∑ b : Fin (N : ℕ), if L ≤ weightRadius N b a then weightRadius N b a ^ (-p) else 0) := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun b _ => hpoint b
    _ = ((univ.filter (fun b : Fin (N : ℕ) => weightRadius N b a ≤ L)).card : ℝ) * L ^ (-p) +
        (∑ b ∈ univ.filter (fun b => L ≤ weightRadius N b a), weightRadius N b a ^ (-p)) := by
      rw [← sum_filter, ← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (2 * L) * L ^ (-p) + 2 * (1 + 1 / (p - 1)) * L ^ (1 - p) :=
      add_le_add (mul_le_mul_of_nonneg_right hcount (by positivity)) htail
    _ = _ := by
      have heq : L * L ^ (-p) = L ^ (1 - p) := by
        rw [show 1 - p = 1 + (-p) by ring_nf, Real.rpow_add hL0, Real.rpow_one]
      calc
        _ = 2 * (L * L ^ (-p)) + 2 * (1 + 1 / (p - 1)) * L ^ (1 - p) := by ring_nf
        _ = _ := by rw [heq]; ring_nf

/-- Internal counting-measure norm estimate from the pointwise row decay.
-/
theorem row_norm_of_decay {q δ L B : ℝ} (hq : 1 ≤ q) (hδ : 1 < δ * q)
    (hL : 1 ≤ L) (hB : 0 ≤ B) (N : ℕ+) (a : Fin (N : ℕ))
    (v : Fin (N : ℕ) → ℝ)
    (hv : ∀ b, |v b| ≤ B * (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-δ)) :
    ‖WithLp.toLp (ENNReal.ofReal q) v‖ ≤
      B * (2 * (2 + 1 / (δ * q - 1))) ^ (1 / q) * L ^ (1 / q - δ) := by
  have hq0 : 0 < q := by linarith
  have hL0 : 0 < L := by linarith
  let D := 2 * (2 + 1 / (δ * q - 1))
  have hD : 0 < D := by dsimp [D]; positivity
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hq0.le] using hq0)]
  simp only [ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs]
  have hsum : (∑ b, |v b| ^ q) ≤ B ^ q * (D * L ^ (1 - δ * q)) := by
    calc
      _ ≤ ∑ b : Fin (N : ℕ),
          (B * (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-δ)) ^ q :=
        sum_le_sum fun b _ => Real.rpow_le_rpow (abs_nonneg _) (hv b) hq0.le
      _ = B ^ q * ∑ b : Fin (N : ℕ),
          (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-(δ * q)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        have hd : 0 ≤ (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) := by positivity
        rw [Real.mul_rpow hB (by positivity), ← Real.rpow_mul hd]
        congr 2
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_row_scale_rpow_le N a hδ hL) (by positivity)
  calc
    _ ≤ (B ^ q * (D * L ^ (1 - δ * q))) ^ (1 / q) :=
      Real.rpow_le_rpow (sum_nonneg fun b _ => by positivity) hsum (by positivity)
    _ = B * D ^ (1 / q) * L ^ (1 / q - δ) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hD.le (by positivity), ← Real.rpow_mul hB,
        ← Real.rpow_mul hL0.le]
      have hcancel : q * (1 / q) = 1 := by field_simp
      have hexp : (1 - δ * q) * (1 / q) = 1 / q - δ := by field_simp
      rw [hcancel, hexp, Real.rpow_one]
      ring_nf

/-- The four assertions of the proof of Lemma 5.11. The amplitude `A`
is the upper coefficient amplitude `C₀ n^(κ₀ ε)` from the matrix assumptions.
The uniform constant precedes the cycle, amplitude, and retention parameter. -/
theorem diff_tail (s : Riesz1.RieszExponent) :
    let q := 2 / s.val
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (η A : ℝ), 0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) →
      ∀ (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      (∀ a b, M a b = ∑ k, ∑ r, α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) →
      ∀ a : Fin (N : ℕ),
      let T := discardedMatrix N i₀ η α M
      let L := rowCutoff N i₀ η a
      (∀ b, |T a b| ≤ C * A * (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val) ∧
        |T a (b + 1) - T a b| ≤ C * A *
          (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-1 - s.val)) ∧
      (∑ b, |T a b| ^ q) ^ (1 / q) ≤ C * A * L ^ (-s.val / 2) ∧
      (∑ b, |cyclicTranslation N 1 (T a) b - T a b| ^ q) ^ (1 / q) ≤
        C * A * L ^ (-1 - s.val / 2) := by
  let q := 2 / s.val
  let E := (1 + 1 / s.val) * 4 ^ s.val
  let F := 2 * (1 + 1 / (s.val + 1)) * 4 ^ (s.val + 1)
  let U := E * (2 * (2 + 1 / (s.val * q - 1))) ^ (1 / q)
  let V := F * (2 * (2 + 1 / ((s.val + 1) * q - 1))) ^ (1 / q)
  have hs := s.property.1
  have hs1 := s.property.2
  have hq : 1 ≤ q := by dsimp [q]; rw [le_div_iff₀ hs]; linarith
  have hq0 : 0 < q := by linarith
  have hsq : s.val * q = 2 := by dsimp [q]; field_simp
  have hsq' : 1 < (s.val + 1) * q := by nlinarith
  have hE : 0 < E := by dsimp [E]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hU : 0 < U := by dsimp [U]; rw [hsq]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have heU : 1 / q - s.val = -s.val / 2 := by dsimp [q]; field_simp; ring_nf
  have heV : 1 / q - (s.val + 1) = -1 - s.val / 2 := by dsimp [q]; field_simp; ring_nf
  refine ⟨E + F + U + V, by positivity, ?_⟩
  intro N hN i₀ η A hη hη' hA α hα M hM a
  let T := discardedMatrix N i₀ η α M
  let L := rowCutoff N i₀ η a
  have hL : 1 ≤ L := one_le_rowCutoff N i₀ η a
  have hentry (b : Fin (N : ℕ)) := discarded_entry_bound N i₀ a b hη hη' hs hA α hα M hM
  have hincr (b : Fin (N : ℕ)) := discarded_increment_bound N i₀ a b hη hη' hs hA α hα M hM
  have hnorm := row_norm_of_decay hq (by rw [hsq]; norm_num) hL
    (mul_nonneg hE.le hA) N a (T a) hentry
  have hdiff := row_norm_of_decay hq hsq' hL (mul_nonneg hF.le hA) N a
    (fun b => T a (b + 1) - T a b) (fun b => by
      simpa only [show -(s.val + 1) = -1 - s.val by ring_nf] using hincr b)
  have hnorm' : ‖WithLp.toLp (ENNReal.ofReal q) (T a)‖ ≤ U * A * L ^ (-s.val / 2) := by
    rw [heU] at hnorm
    exact hnorm.trans_eq (by dsimp [U]; ring_nf)
  have hdiff' : ‖WithLp.toLp (ENNReal.ofReal q) (fun b => T a (b + 1) - T a b)‖ ≤
      V * A * L ^ (-1 - s.val / 2) := by
    rw [heV] at hdiff
    exact hdiff.trans_eq (by dsimp [V]; ring_nf)
  let p := ENNReal.ofReal q
  let : Fact (1 ≤ p) := ⟨by
    exact_mod_cast (show ENNReal.ofReal 1 ≤ ENNReal.ofReal q from ENNReal.ofReal_le_ofReal hq)⟩
  have hp : 0 < p.toReal := by simpa only [p, ENNReal.toReal_ofReal hq0.le] using hq0
  have hpower (v : Fin (N : ℕ) → ℝ) :
      (∑ b, |v b| ^ q) ^ (1 / q) = ‖WithLp.toLp p v‖ := by
    rw [PiLp.norm_eq_sum hp]
    simp only [p, ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs]
  have hlabel : Riesz1.labelOf N 1 = (1 : Fin (N : ℕ)) := by
    have h := Riesz1.labelOf_natCast N (1 : Fin (N : ℕ))
    simpa only [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < (N : ℕ)), Nat.cast_one] using h
  have hshift : ‖WithLp.toLp p (fun b => cyclicTranslation N 1 (T a) b - T a b)‖ =
      ‖WithLp.toLp p (fun b => T a (b + 1) - T a b)‖ := by
    change ‖WithLp.toLp p (fun b => cyclicTranslation N 1 (T a) b) - WithLp.toLp p (T a)‖ = _
    simp only [cyclicTranslation, hlabel]
    rw [← norm_neg_shift_sub hp N 1 (T a)]
    change ‖WithLp.toLp p (fun b => T a (b - -1) - T a b)‖ = _
    simp only [sub_neg_eq_add]
  refine ⟨fun b => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (hentry b).trans (by dsimp [E] at *; gcongr; linarith)
  · exact (hincr b).trans (by dsimp [F] at *; gcongr; linarith)
  · rw [hpower]
    exact hnorm'.trans (by gcongr; linarith)
  · rw [hpower, hshift]
    exact hdiff'.trans (by gcongr; linarith)

/-- Lemma 5.11, equation (5.39): conversion of negative
powers from the length cutoff to `1 + η r_i`, uniformly for the four exponents. -/
theorem cutoff_decay_paper_scale (N : ℕ+) (i₀ a : Fin (N : ℕ))
    {η e d : ℝ} (hη : 0 ≤ η) (he : 0 ≤ e) (he2 : e ≤ 2) (hd : 0 ≤ d) :
    (rowCutoff N i₀ η a + d) ^ (-e) ≤
      9 * (paperRowScale N i₀ η a + d) ^ (-e) := by
  have hL := one_le_rowCutoff N i₀ η a
  have hR := rowCutoff_le_paperRowScale N i₀ hη a
  have h3 := paperRowScale_le_three_rowCutoff N i₀ η a
  have hR0 : 0 < paperRowScale N i₀ η a + d := by linarith
  calc
    _ ≤ ((paperRowScale N i₀ η a + d) / 3) ^ (-e) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    _ = 3 ^ e * (paperRowScale N i₀ η a + d) ^ (-e) := by
      rw [Real.div_rpow hR0.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), neg_neg, mul_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc (3 : ℝ) ^ e ≤ 3 ^ (2 : ℝ) :=
             Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
           _ = 9 := by norm_num

/-- Lemma 5.11, equation (5.39) and its following row-norm
display, with the literal scale `1 + η r_i`. The constant precedes all geometric data. -/
theorem diff_tail_paper_scale (s : Riesz1.RieszExponent) :
    let q := 2 / s.val
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (η A : ℝ), 0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) →
      ∀ (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      (∀ a b, M a b = ∑ k, ∑ r, α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) →
      ∀ a : Fin (N : ℕ),
      let T := discardedMatrix N i₀ η α M
      let R := paperRowScale N i₀ η a
      (∀ b, |T a b| ≤ C * A * (R + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val) ∧
        |T a (b + 1) - T a b| ≤ C * A *
          (R + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-1 - s.val)) ∧
      (∑ b, |T a b| ^ q) ^ (1 / q) ≤ C * A * R ^ (-s.val / 2) ∧
      (∑ b, |cyclicTranslation N 1 (T a) b - T a b| ^ q) ^ (1 / q) ≤
        C * A * R ^ (-1 - s.val / 2) := by
  obtain ⟨C, hC, htail⟩ := diff_tail s
  refine ⟨9 * C, by positivity, ?_⟩
  intro N hN i₀ η A hη hη' hA α hα M hM a
  have hr := htail N hN i₀ η A hη hη' hA α hα M hM a
  have hconvert {e d : ℝ} (he : 0 ≤ e) (he2 : e ≤ 2) (hd : 0 ≤ d) :
      C * A * (rowCutoff N i₀ η a + d) ^ (-e) ≤
        (9 * C) * A * (paperRowScale N i₀ η a + d) ^ (-e) := by
    calc
      _ ≤ C * A * (9 * (paperRowScale N i₀ η a + d) ^ (-e)) :=
        mul_le_mul_of_nonneg_left (cutoff_decay_paper_scale N i₀ a hη.le he he2 hd)
          (mul_nonneg hC.le hA)
      _ = _ := by ring
  have hs := s.property
  refine ⟨fun b => ⟨(hr.1 b).1.trans (hconvert hs.1.le (by linarith) (by positivity)), ?_⟩,
    ?_, ?_⟩
  · have h := hconvert (e := 1 + s.val) (d := (Riesz1.cyclicIndexDistance N a b : ℝ))
      (by linarith) (by linarith) (by positivity)
    rw [show -(1 + s.val) = -1 - s.val by ring] at h
    exact (hr.1 b).2.trans h
  · have h := hconvert (e := s.val / 2) (d := 0) (by linarith) (by linarith) le_rfl
    simp only [add_zero] at h
    rw [show -(s.val / 2) = -s.val / 2 by ring] at h
    exact hr.2.1.trans h
  · have h := hconvert (e := 1 + s.val / 2) (d := 0) (by linarith) (by linarith) le_rfl
    simp only [add_zero] at h
    rw [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] at h
    exact hr.2.2.trans h

/-- Internal row-action estimate used in the proof of Lemma 5.11.
The inverse includes its constant mode and no zero-sum premise is used. -/
theorem discarded_action_bound (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (η A : ℝ), 0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) →
      ∀ (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      (∀ a b, M a b = ∑ k, ∑ r, α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) →
      ∀ (u : Fin (N : ℕ) → ℝ) (a : Fin (N : ℕ)),
      |(discardedMatrix N i₀ η α M *ᵥ u) a| ≤
        C * A / (η * weightRadius N a i₀) *
          (∑ b, |(rieszMatrix sh N hN *ᵥ u) b| ^ p) ^ (1 / p) := by
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let p := (1 - s.val / 2)⁻¹
  let q := 2 / s.val
  obtain ⟨B, hB, htail⟩ := diff_tail_paper_scale s
  let qp := ENNReal.ofReal q
  have hq : 1 ≤ q := by
    dsimp [q]; rw [le_div_iff₀ s.property.1]; linarith [s.property.2]
  have hq0 : 0 < q := by linarith
  let : Fact (1 ≤ qp) := ⟨by
    exact_mod_cast (show ENNReal.ofReal 1 ≤ ENNReal.ofReal q from ENNReal.ofReal_le_ofReal hq)⟩
  have hqp : 0 < qp.toReal := by simpa only [qp, ENNReal.toReal_ofReal hq0.le] using hq0
  obtain ⟨D, hD, hinv⟩ := inverse_row_optimized hz sh hqp
  have hpq : q.HolderConjugate p := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · dsimp [q]; rw [lt_div_iff₀ s.property.1]; linarith [s.property.2]
    · dsimp [p, q]; field_simp; ring_nf
  refine ⟨2 * D * B, by positivity, ?_⟩
  intro N hN i₀ η A hη hη' hA α hα M hM u a
  let H := rieszMatrix sh N hN
  let T := discardedMatrix N i₀ η α M
  let L := paperRowScale N i₀ η a
  have hr := htail N hN i₀ η A hη hη' hA α hα M hM a
  have hL0 : 0 < L := by
    dsimp [L, paperRowScale]
    have := one_le_weightRadius N a i₀
    positivity
  have hBA : 0 ≤ B * A := mul_nonneg hB.le hA
  have hnorm (v : Fin (N : ℕ) → ℝ) :
      ‖WithLp.toLp qp v‖ = (∑ j, |v j| ^ q) ^ (1 / q) := by
    rw [PiLp.norm_eq_sum hqp]
    simp only [qp, ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs]
  have hlabel : Riesz1.labelOf N 1 = (1 : Fin (N : ℕ)) := by
    have h := Riesz1.labelOf_natCast N (1 : Fin (N : ℕ))
    simpa only [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < (N : ℕ)), Nat.cast_one] using h
  have hback : ‖WithLp.toLp qp (fun j => T a (j - 1)) - WithLp.toLp qp (T a)‖ ≤
      B * A * L ^ (-1 - s.val / 2) := by
    change ‖WithLp.toLp qp (fun j => T a (j - 1) - T a j)‖ ≤ _
    rw [hnorm]
    simpa only [cyclicTranslation, hlabel] using hr.2.2
  have hb0 := hinv N hN (B * A * L ^ (-s.val / 2))
    (B * A * L ^ (-1 - s.val / 2)) (T a) (by positivity) (by positivity)
    (by rw [hnorm]; exact hr.2.1) hback
  rw [hnorm] at hb0
  have hinter : (B * A * L ^ (-s.val / 2)) ^ sh.val *
      (B * A * L ^ (-1 - s.val / 2)) ^ (1 - sh.val) = B * A * L ^ (-1 : ℝ) := by
    rw [Real.mul_rpow hBA (by positivity), Real.mul_rpow hBA (by positivity),
      ← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le]
    calc
      _ = ((B * A) ^ sh.val * (B * A) ^ (1 - sh.val)) *
          (L ^ ((-s.val / 2) * sh.val) * L ^ ((-1 - s.val / 2) * (1 - sh.val))) := by ring
      _ = _ := by
        rw [← Real.rpow_add' hBA (by ring_nf; norm_num), ← Real.rpow_add hL0,
          show sh.val + (1 - sh.val) = 1 by ring, Real.rpow_one,
          show (-s.val / 2) * sh.val + (-1 - s.val / 2) * (1 - sh.val) = -1 by
            dsimp [sh]; ring]
  -- The two terms of the paper's inverse-row display are kept before absorption.
  have hbdisplay : (∑ j, |(T a ᵥ* H⁻¹) j| ^ q) ^ (1 / q) ≤
      D * (B * A) * ((N : ℝ) ^ (s.val / 2 - 1) * L ^ (-s.val / 2) + L ^ (-1 : ℝ)) := by
    rw [hinter] at hb0
    exact hb0.trans_eq (by dsimp [sh]; ring)
  have hmass : (N : ℝ) ^ (s.val / 2 - 1) * L ^ (-s.val / 2) ≤ L ^ (-1 : ℝ) := by
    calc
      _ ≤ L ^ (s.val / 2 - 1) * L ^ (-s.val / 2) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hL0
          (paperRowScale_le_cycle N hN i₀ hη' a) (by linarith [s.property.2])) (by positivity)
      _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring
  have hb : (∑ j, |(T a ᵥ* H⁻¹) j| ^ q) ^ (1 / q) ≤
      2 * D * (B * A) * L ^ (-1 : ℝ) :=
    hbdisplay.trans (by nlinarith [mul_nonneg (mul_nonneg hD.le hBA) (sub_nonneg.mpr hmass)])
  have hH : IsUnit H := (sampledRieszKernel_posDef sh N hN).isUnit
  have hid : (T *ᵥ u) a = (T a ᵥ* H⁻¹) ⬝ᵥ (H *ᵥ u) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det H).mp hH)]
    simp only [Matrix.one_mulVec]
    rfl
  have hholder : |(T *ᵥ u) a| ≤
      (∑ b, |(T a ᵥ* H⁻¹) b| ^ q) ^ (1 / q) *
        (∑ b, |(H *ᵥ u) b| ^ p) ^ (1 / p) := by
    rw [hid]
    apply (abs_sum_le_sum_abs _ _).trans
    simpa only [abs_mul, abs_abs] using Real.inner_le_Lp_mul_Lq univ
      (fun b => |(T a ᵥ* H⁻¹) b|) (fun b => |(H *ᵥ u) b|) hpq
  have hr0 : 0 < weightRadius N a i₀ := lt_of_lt_of_le zero_lt_one (one_le_weightRadius N a i₀)
  have hcut : η * weightRadius N a i₀ ≤ L := by dsimp [L, paperRowScale]; linarith
  have hscale : 2 * D * (B * A) * L ^ (-1 : ℝ) ≤
      (2 * D * B) * A / (η * weightRadius N a i₀) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_div_iff₀ hL0 (mul_pos hη hr0)]
    nlinarith [mul_nonneg (mul_nonneg hD.le (mul_nonneg hB.le hA))
      (by linarith : 0 ≤ L - η * weightRadius N a i₀)]
  exact hholder.trans (mul_le_mul_of_nonneg_right (hb.trans hscale) (by positivity))

/-- Deterministic weighted estimate underlying the proof of Lemma 5.11.
The random-variable assertion follows by Cauchy–Schwarz under the measure. -/
theorem diff_long_pointwise (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (γ : ℝ) (_hγ : 1 / 2 ≤ γ) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let t := γ / 2 + 1 / 4
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (η A : ℝ), 0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) →
      ∀ (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      (∀ a b, M a b = ∑ k, ∑ r, α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) →
      ∀ u : Fin (N : ℕ) → ℝ,
      |∑ a, weightRadius N a i₀ ^ (2 * t) * u a *
        (discardedMatrix N i₀ η α M *ᵥ u) a| ≤
      C * A * η⁻¹ * Real.sqrt (Real.log (2 * (N : ℝ))) *
        Real.sqrt (∑ a, (weightRadius N a i₀ ^ γ * u a) ^ 2) *
        (∑ b, |(rieszMatrix sh N hN *ᵥ u) b| ^ p) ^ (1 / p) := by
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let p := (1 - s.val / 2)⁻¹
  let t := γ / 2 + 1 / 4
  obtain ⟨B, hB, haction⟩ := discarded_action_bound hz s
  let D := 2 * (1 + 1 / Real.log 2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B * Real.sqrt D, by positivity, ?_⟩
  intro N hN i₀ η A hη hη' hA α hα M hM u
  let V := (∑ b, |(rieszMatrix sh N hN *ᵥ u) b| ^ p) ^ (1 / p)
  have hV : 0 ≤ V := Real.rpow_nonneg (sum_nonneg fun b _ => by positivity) _
  have hrows (a : Fin (N : ℕ)) := haction N hN i₀ η A hη hη' hA α hα M hM u a
  have hsum : (∑ a, weightRadius N a i₀ ^ (2 * t - 1) * |u a|) ≤
      Real.sqrt (D * Real.log (2 * (N : ℝ))) *
        Real.sqrt (∑ a, (weightRadius N a i₀ ^ γ * u a) ^ 2) := by
    have heq (a : Fin (N : ℕ)) : weightRadius N a i₀ ^ (2 * t - 1) * |u a| =
        weightRadius N a i₀ ^ (-(1 / 2 : ℝ)) * (weightRadius N a i₀ ^ γ * |u a|) := by
      rw [← mul_assoc, ← Real.rpow_add (by linarith [one_le_weightRadius N a i₀])]
      congr 2
      dsimp [t]
      ring_nf
    simp_rw [heq]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ
      (fun a => weightRadius N a i₀ ^ (-(1 / 2 : ℝ)))
      (fun a => weightRadius N a i₀ ^ γ * |u a|)
    have hpow (a : Fin (N : ℕ)) : (weightRadius N a i₀ ^ (-(1 / 2 : ℝ))) ^ 2 =
        weightRadius N a i₀ ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [one_le_weightRadius N a i₀])]
      norm_num
    have hu (a : Fin (N : ℕ)) : (weightRadius N a i₀ ^ γ * |u a|) ^ 2 =
        (weightRadius N a i₀ ^ γ * u a) ^ 2 := by rw [mul_pow, sq_abs, ← mul_pow]
    simp only [hpow, hu] at hcs
    apply hcs.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    have hrange (a : Fin (N : ℕ)) : weightRadius N a i₀ ≤ (N : ℝ) := by
      have hi := a.isLt
      have hj := i₀.isLt
      dsimp [weightRadius, Riesz1.cyclicIndexDistance, Nat.dist]
      norm_cast
      omega
    have hb := sum_weightRadius_le_of_one N i₀ (R := (N : ℝ)) (by exact_mod_cast N.pos)
    simpa only [show univ.filter (fun a => weightRadius N a i₀ ≤ (N : ℝ)) = univ from
      filter_eq_self.mpr (fun a _ => hrange a)] using hb
  calc
    _ ≤ ∑ a, weightRadius N a i₀ ^ (2 * t) * |u a| *
        |(discardedMatrix N i₀ η α M *ᵥ u) a| := by
      apply (abs_sum_le_sum_abs _ _).trans_eq
      apply sum_congr rfl
      intro a _
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg
        (le_trans zero_le_one (one_le_weightRadius N a i₀)) _)]
    _ ≤ ∑ a, weightRadius N a i₀ ^ (2 * t) * |u a| *
        (B * A / (η * weightRadius N a i₀) * V) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrows a)
        (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (one_le_weightRadius N a i₀)) _)
          (abs_nonneg _))
    _ = (B * A * η⁻¹ * V) * ∑ a, weightRadius N a i₀ ^ (2 * t - 1) * |u a| := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      rw [Real.rpow_sub_one (by linarith [one_le_weightRadius N a i₀])]
      ring_nf
    _ ≤ (B * A * η⁻¹ * V) * (Real.sqrt (D * Real.log (2 * (N : ℝ))) *
        Real.sqrt (∑ a, (weightRadius N a i₀ ^ γ * u a) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [Real.sqrt_mul hD.le]; dsimp [V, sh, p]; ring_nf

/-- See the proof of Lemma 5.11 in the paper: the long-interval contribution for measurable
random vectors with finite displayed norms. Absolute integrability is included
in the conclusion. The coefficient amplitude is the original `C₀ n^(κ₀ ε)`. -/
theorem diff_long (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (γ : ℝ) (hγ : 1 / 2 ≤ γ) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let t := γ / 2 + 1 / 4
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X] (ν : MeasureTheory.Measure X)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ)) (η A : ℝ),
      0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → X → ℝ),
      (∀ k r, Measurable (α k r)) →
      ∀ (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      (∀ a b, Measurable (fun x => M x a b)) →
      (∀ᵐ x ∂ν, (∀ k r, 0 ≤ α k r x ∧ α k r x ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) ∧
        ∀ a b, M x a b = ∑ k, ∑ r, α k r x *
          (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
          (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) →
      ∀ (u : X → Fin (N : ℕ) → ℝ), (∀ a, Measurable (fun x => u x a)) →
      let U := fun x => Real.sqrt (∑ a, (weightRadius N a i₀ ^ γ * u x a) ^ 2)
      let V := fun x => (∑ b, |(rieszMatrix sh N hN *ᵥ u x) b| ^ p) ^ (1 / p)
      let E := fun x => ∑ a, weightRadius N a i₀ ^ (2 * t) * u x a *
        (discardedMatrix N i₀ η (fun k r => α k r x) (M x) *ᵥ u x) a
      MeasureTheory.MemLp U 2 ν → MeasureTheory.MemLp V 2 ν →
      MeasureTheory.Integrable E ν ∧
      |∫ x, E x ∂ν| ≤ C * A * η⁻¹ * Real.sqrt (Real.log (2 * (N : ℝ))) *
        Real.sqrt (∫ x, U x ^ 2 ∂ν) * Real.sqrt (∫ x, V x ^ 2 ∂ν) := by
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let p := (1 - s.val / 2)⁻¹
  let t := γ / 2 + 1 / 4
  obtain ⟨C, hC, hpoint⟩ := diff_long_pointwise hz s γ hγ
  refine ⟨C, hC, ?_⟩
  intro X _ ν N hN i₀ η A hη hη' hA α hα M hM hcoeff u hu U V E hU hV
  let K := C * A * η⁻¹ * Real.sqrt (Real.log (2 * (N : ℝ)))
  have hU' : MeasureTheory.MemLp U 2 ν := hU
  have hV' : MeasureTheory.MemLp V 2 ν := hV
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : Measurable E := by
    apply Finset.measurable_sum
    intro a _
    apply (measurable_const.mul (hu a)).mul
    change Measurable (fun x => ∑ b, discardedMatrix N i₀ η (fun k r => α k r x) (M x) a b * u x b)
    apply Finset.measurable_sum
    intro b _
    exact (measurable_discardedMatrix N i₀ η α M hα hM a b).mul (hu b)
  have hbound : ∀ᵐ x ∂ν, |E x| ≤ K * U x * V x := by
    filter_upwards [hcoeff] with x hx
    exact hpoint N hN i₀ η A hη hη' hA (fun k r => α k r x) hx.1 (M x) hx.2 (u x)
  have hprod : MeasureTheory.Integrable (fun x => K * U x * V x) ν := by
    simpa only [Pi.mul_apply, mul_assoc] using (hU'.integrable_mul hV').const_mul K
  have hint : MeasureTheory.Integrable E ν := by
    apply hprod.mono' hE.aestronglyMeasurable
    exact hbound
  have htwo : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (f := U) (g := V) htwo
    (MeasureTheory.ae_of_all ν (fun x => Real.sqrt_nonneg _))
    (MeasureTheory.ae_of_all ν (fun x => Real.rpow_nonneg (sum_nonneg fun b _ => by positivity) _))
    (by simpa only [ENNReal.ofReal_ofNat] using hU')
    (by simpa only [ENNReal.ofReal_ofNat] using hV')
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x, |E x| ∂ν := by simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm E
    _ ≤ ∫ x, K * U x * V x ∂ν :=
      MeasureTheory.integral_mono_ae hint.abs hprod hbound
    _ = K * ∫ x, U x * V x ∂ν := by simp only [mul_assoc, MeasureTheory.integral_const_mul]
    _ ≤ K * (Real.sqrt (∫ x, U x ^ 2 ∂ν) * Real.sqrt (∫ x, V x ^ 2 ∂ν)) :=
      mul_le_mul_of_nonneg_left hcs hK
    _ = _ := by dsimp [K]; ring_nf

/-- Mean-value power comparison on the comparable radii of a retained
interval, as used in the proof of Lemma 5.11. -/
theorem retained_power_difference (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x y : ℝ}, 0 < x → 0 < y → x / 2 ≤ y → y ≤ 2 * x →
      |x ^ t - y ^ t| ≤ C * x ^ (t - 1) * |x - y| := by
  have hf : ContDiffOn ℝ 1 (fun z : ℝ => z ^ t) (Set.Icc (1 / 2 : ℝ) 2) := by
    intro z hz
    exact (Real.contDiffAt_rpow_const_of_ne (by linarith [hz.1] : z ≠ 0)).contDiffWithinAt
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _)
    isCompact_Icc
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro x y hx hy hxy hyx
  have hz : y / x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    constructor
    · rw [le_div_iff₀ hx]; linarith
    · rw [div_le_iff₀ hx]; linarith
  have hnorm := hK.norm_sub_le (by constructor <;> norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2) hz
  simp only [Real.one_rpow, Real.norm_eq_abs] at hnorm
  have heq : y = x * (y / x) := by field_simp
  have hid : x ^ t - y ^ t = x ^ t * (1 - (y / x) ^ t) := by
    conv_lhs => rhs; rw [heq, Real.mul_rpow hx.le (div_pos hy hx).le]
    ring_nf
  have hzsub : |1 - y / x| = |x - y| / x := by
    rw [← div_self hx.ne', ← sub_div, abs_div, abs_of_pos hx]
  rw [hid, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  calc
    _ ≤ x ^ t * ((K : ℝ) * |1 - y / x|) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (K : ℝ) * x ^ (t - 1) * |x - y| := by
      rw [hzsub, Real.rpow_sub_one hx.ne']
      ring_nf
    _ ≤ _ := by gcongr; linarith

/-- Internal normalization of the retained power commutator. -/
theorem retained_normalized_weight_bound (t g h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x y : ℝ}, 0 < x → 0 < y → x / 2 ≤ y → y ≤ 2 * x →
      (x ^ t - y ^ t) ^ 2 / (x ^ g * y ^ h) ≤
        C * x ^ (2 * t - 2 - g - h) * (x - y) ^ 2 := by
  obtain ⟨B, hB, hdiff⟩ := retained_power_difference t
  refine ⟨B ^ 2 * 2 ^ h, by positivity, ?_⟩
  intro x y hx hy hxy hyx
  have hden : x ^ g * x ^ h ≤ 2 ^ h * (x ^ g * y ^ h) := by
    have hb : x ^ h ≤ (2 * y) ^ h := Real.rpow_le_rpow hx.le (by linarith) hh
    rw [Real.mul_rpow (by norm_num) hy.le] at hb
    nlinarith [mul_nonneg (Real.rpow_pos_of_pos hx g).le (sub_nonneg.mpr hb)]
  have hpow : x ^ (2 * t - 2 - g - h) * x ^ g * x ^ h = x ^ (2 * (t - 1)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring_nf
  have hdiff' : (x ^ t - y ^ t) ^ 2 ≤ B ^ 2 * x ^ (2 * (t - 1)) * (x - y) ^ 2 := by
    have hs := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr (hdiff hx hy hxy hyx)
    have hxp : (x ^ (t - 1)) ^ 2 = x ^ (2 * (t - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      congr 1
      ring_nf
    simpa only [sq_abs, mul_pow, hxp] using hs
  rw [div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hx g) (Real.rpow_pos_of_pos hy h))]
  apply hdiff'.trans
  calc
    _ = B ^ 2 * x ^ (2 * t - 2 - g - h) * (x - y) ^ 2 * (x ^ g * x ^ h) := by
      rw [← hpow]
      ring_nf
    _ ≤ B ^ 2 * x ^ (2 * t - 2 - g - h) * (x - y) ^ 2 *
        (2 ^ h * (x ^ g * y ^ h)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring_nf

/-- Lemma 5.11, Step 1: the positive entry-distance power sum, including
the empty range when the retention radius is smaller than one. -/
theorem retained_distance_power_sum {s R : ℝ} (hs : s < 1) (hR : 0 < R) (K : ℕ) :
    (∑ r : Fin K, if ((r.val + 1 : ℕ) : ℝ) ≤ R then
      ((r.val + 1 : ℕ) : ℝ) ^ (2 - s) else 0) ≤ R ^ (3 - s) := by
  let S := univ.filter (fun r : Fin K => ((r.val + 1 : ℕ) : ℝ) ≤ R)
  have hcard : (S.card : ℝ) ≤ R := by
    have hsub : S.card ≤ (range ⌊R⌋₊).card := by
      apply card_le_card_of_injOn (fun r : Fin K => r.val)
      · intro r hr
        have hr' := (mem_filter.mp hr).2
        apply mem_range.mpr
        have hb : r.val + 1 ≤ ⌊R⌋₊ := Nat.le_floor hr'
        change r.val < ⌊R⌋₊
        omega
      · intro r _ q _ heq
        exact Fin.ext heq
    have hsub' : (S.card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by
      exact_mod_cast (show S.card ≤ ⌊R⌋₊ by simpa only [card_range] using hsub)
    exact hsub'.trans (Nat.floor_le hR.le)
  calc
    _ = ∑ r ∈ S, ((r.val + 1 : ℕ) : ℝ) ^ (2 - s) := by rw [sum_filter]
    _ ≤ ∑ _r ∈ S, R ^ (2 - s) := by
      apply sum_le_sum
      intro r hr
      exact Real.rpow_le_rpow (by positivity) (mem_filter.mp hr).2 (by linarith)
    _ = (S.card : ℝ) * R ^ (2 - s) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ R * R ^ (2 - s) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = R ^ (3 - s) := by
      conv_lhs => lhs; rw [← Real.rpow_one R]
      rw [← Real.rpow_add hR]
      congr 1
      ring_nf

/-- Lemma 5.11, Step 1: a retained matrix has nonnegative entries. -/
theorem retainedMatrix_entry_nonneg (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hα : ∀ k r, 0 ≤ α k r) (a b : Fin (N : ℕ)) :
    0 ≤ retainedMatrix N i₀ η α a b := by
  apply sum_nonneg; intro k _; apply sum_nonneg; intro r _
  have := hα k r
  split_ifs <;> positivity

/-- Lemma 5.11, Step 1: counting intervals through both entries gives
`C A (1+d)⁻ˢ`, before any commutator summation. -/
theorem retained_entry_decay (N : ℕ+) (i₀ a b : Fin (N : ℕ))
    {s η A : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hα : ∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2)) :
    retainedMatrix N i₀ η α a b ≤
      (1 + 1 / s) * A * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s) := by
  let D := Riesz1.cyclicIndexDistance N a b
  let R : ℝ := 1 + D
  have hR : 1 ≤ R := by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) D; linarith
  have hslice (r : Fin ((N : ℕ) / 2)) :
      (∑ k, if IsRetained N i₀ η k r then α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) else 0) ≤
      A * (if R ≤ ((r.val + 1 : ℕ) : ℝ) then ((r.val + 1 : ℕ) : ℝ) ^ (-s - 1) else 0) := by
    let l : ℝ := ((r.val + 1 : ℕ) : ℝ)
    have hl : 0 < l := by dsimp [l]; positivity
    by_cases hlen : R ≤ l
    · simp only [show R ≤ ((r.val + 1 : ℕ) : ℝ) from hlen, ↓reduceIte]
      calc
        _ ≤ ∑ k : Fin (N : ℕ), (A * l ^ (-s - 2)) *
            (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
            (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
          apply sum_le_sum; intro k _
          split_ifs <;> first | simpa only [mul_one] using (hα k r).2 | positivity | simp only [mul_zero, zero_mul, le_refl]
        _ = (A * l ^ (-s - 2)) * ((r.val + 1 - D : ℕ) : ℝ) := by
          simp_rw [mul_assoc]
          rw [← mul_sum, ← mul_sum, cyclicIndexInterval_pair_count N (by have := r.isLt; omega) a b]
        _ ≤ (A * l ^ (-s - 2)) * l := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp [l]
          exact_mod_cast (Nat.sub_le (r.val + 1) D)
        _ = _ := by
          change A * l ^ (-s - 2) * l = A * l ^ (-s - 1)
          rw [mul_assoc, ← Real.rpow_add_one hl.ne']
          congr 2
          ring
    · have hzero (k : Fin (N : ℕ)) :
          (if IsRetained N i₀ η k r then α k r *
            (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
            (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) else 0) = 0 := by
        split_ifs with hret ha hb
        · have hd := distance_lt_interval_length N k (by have := r.isLt; omega) a b ha hb
          have hd' : 1 + D ≤ r.val + 1 := by dsimp [D]; omega
          have : R ≤ l := by dsimp [R, l]; exact_mod_cast hd'
          exact (hlen this).elim
        all_goals ring
      simp only [hzero, sum_const_zero, show ¬ R ≤ ((r.val + 1 : ℕ) : ℝ) from hlen,
        ↓reduceIte, mul_zero, le_refl]
  calc
    _ = ∑ r, ∑ k, if IsRetained N i₀ η k r then α k r *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) else 0 := sum_comm
    _ ≤ ∑ r, A * (if R ≤ ((r.val + 1 : ℕ) : ℝ) then
        ((r.val + 1 : ℕ) : ℝ) ^ (-s - 1) else 0) := sum_le_sum fun r _ => hslice r
    _ = A * ∑ r : Fin ((N : ℕ) / 2), if R ≤ ((r.val + 1 : ℕ) : ℝ) then
        ((r.val + 1 : ℕ) : ℝ) ^ (-(s + 1)) else 0 := by rw [mul_sum]; congr 1; ring_nf
    _ ≤ A * ((1 + 1 / ((s + 1) - 1)) * R ^ (1 - (s + 1))) :=
      mul_le_mul_of_nonneg_left (interval_length_power_tail (by linarith) hR _) hA
    _ = _ := by dsimp [R, D]; ring_nf

/-- Lemma 5.11, Step 1: the entrywise normalized commutator retains
the squared entry distance in the mean-value bound. -/
theorem retained_normalized_entry_bound {s t g h : ℝ} (hs : 0 < s) (hh : 0 ≤ h)
    (hexp : 2 * t - 2 - g - h = s - 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ)) (η A : ℝ),
      0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2)) →
      ∀ a b : Fin (N : ℕ),
      |retainedMatrix N i₀ η α a b *
        (weightRadius N a i₀ ^ t - weightRadius N b i₀ ^ t) ^ 2 /
          (weightRadius N a i₀ ^ g * weightRadius N b i₀ ^ h)| ≤
      C * A * weightRadius N a i₀ ^ (s - 3) *
        (if (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ η * weightRadius N a i₀ then
          (Riesz1.cyclicIndexDistance N a b : ℝ) ^ 2 *
            (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s) else 0) := by
  obtain ⟨B, hB, hweight⟩ := retained_normalized_weight_bound t g h hh
  refine ⟨B * (1 + 1 / s), by positivity, ?_⟩
  intro N i₀ η A hη hη' hA α hα a b
  have hx : 0 < weightRadius N a i₀ := by linarith [one_le_weightRadius N a i₀]
  have hy : 0 < weightRadius N b i₀ := by linarith [one_le_weightRadius N b i₀]
  have hmat := retainedMatrix_entry_nonneg N i₀ η α (fun k r => (hα k r).1) a b
  rw [mul_div_assoc, abs_of_nonneg (mul_nonneg hmat (by positivity))]
  split_ifs with hd
  · have hw := weightRadius_lipschitz N i₀ a b
    have hcomp := hw
    rw [abs_sub_le_iff] at hcomp
    have hb := hweight hx hy (by nlinarith) (by nlinarith)
    rw [hexp] at hb
    have hsq : (weightRadius N a i₀ - weightRadius N b i₀) ^ 2 ≤
        (Riesz1.cyclicIndexDistance N a b : ℝ) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hw
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg hB.le (Real.rpow_pos_of_pos hx _).le))
    have hm := retained_entry_decay N i₀ a b (η := η) hs hA α hα
    exact (mul_le_mul hm hb' (by positivity) (by positivity)).trans_eq (by ring)
  · have hz : retainedMatrix N i₀ η α a b = 0 := by
      apply sum_eq_zero; intro k _; apply sum_eq_zero; intro r _
      split_ifs with hret ha hb
      · exact (hd (retained_interval_comparability N i₀ k r hret a b ha hb).1).elim
      all_goals ring
    rw [hz, zero_mul, mul_zero]

/-- Lemma 5.11, Step 1: sum `d^(2-s)` over entry-distance shells.
The diagonal vanishes and at most two labels occur at each positive distance. -/
theorem retained_distance_shell_sum (N : ℕ+) (a : Fin (N : ℕ))
    {s R : ℝ} (hs : s < 1) (hR : 0 < R) :
    (∑ b : Fin (N : ℕ), if 0 < Riesz1.cyclicIndexDistance N a b ∧
        (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ R then
        (Riesz1.cyclicIndexDistance N a b : ℝ) ^ (2 - s) else 0) ≤ 2 * R ^ (3 - s) := by
  let f : ℕ → ℝ := fun k => if 0 < k ∧ (k : ℝ) ≤ R then (k : ℝ) ^ (2 - s) else 0
  have hmap : ∀ b ∈ (univ : Finset (Fin (N : ℕ))),
      Riesz1.cyclicIndexDistance N a b ∈ range ((N : ℕ) + 1) := by
    intro b _
    have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) a b
    rw [mem_range]; omega
  change (∑ b, f (Riesz1.cyclicIndexDistance N a b)) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ k ∈ range ((N : ℕ) + 1), 2 * f k := by
      apply sum_le_sum; intro k _
      rw [sum_congr rfl (fun b hb => congrArg f (mem_filter.mp hb).2), sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by dsimp [f]; split_ifs <;> positivity)
      exact_mod_cast (card_cyclicShell_le_two a k)
    _ = 2 * ∑ r : Fin (N : ℕ), if ((r.val + 1 : ℕ) : ℝ) ≤ R then
        ((r.val + 1 : ℕ) : ℝ) ^ (2 - s) else 0 := by
      rw [← mul_sum, sum_range_succ', ← Fin.sum_univ_eq_sum_range]
      simp only [f, Nat.succ_pos, true_and, Nat.cast_zero,
        lt_self_iff_false, false_and, ↓reduceIte, add_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left (retained_distance_power_sum hs hR _) (by norm_num)

/-- Lemma 5.11, Step 1: Schur row sums by entry distances. -/
theorem retained_kernel_row_bound {s t g h : ℝ} (hs0 : 0 < s) (hs : s < 1) (hh : 0 ≤ h)
    (hexp : 2 * t - 2 - g - h = s - 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ)) (η A : ℝ),
      0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s - 2)) →
      ∀ a : Fin (N : ℕ),
      (∑ b, |retainedMatrix N i₀ η α a b *
        (weightRadius N a i₀ ^ t - weightRadius N b i₀ ^ t) ^ 2 /
          (weightRadius N a i₀ ^ g * weightRadius N b i₀ ^ h)|) ≤ C * A * η ^ (3 - s) := by
  obtain ⟨B, hB, hentry⟩ := retained_normalized_entry_bound hs0 hh hexp
  refine ⟨2 * B, by positivity, ?_⟩
  intro N i₀ η A hη hη' hA α hα a
  let R := weightRadius N a i₀
  have hR : 0 < R := by dsimp [R]; linarith [one_le_weightRadius N a i₀]
  have hpower (b : Fin (N : ℕ)) :
      (if (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ η * R then
        (Riesz1.cyclicIndexDistance N a b : ℝ) ^ 2 *
          (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s) else 0) ≤
      (if 0 < Riesz1.cyclicIndexDistance N a b ∧
        (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ η * R then
        (Riesz1.cyclicIndexDistance N a b : ℝ) ^ (2 - s) else 0) := by
    by_cases hz : Riesz1.cyclicIndexDistance N a b = 0
    · simp [hz]
    · have hd : (0 : ℝ) < Riesz1.cyclicIndexDistance N a b := by exact_mod_cast (Nat.pos_of_ne_zero hz)
      simp only [Nat.pos_of_ne_zero hz, true_and]
      split_ifs
      · calc
          _ ≤ (Riesz1.cyclicIndexDistance N a b : ℝ) ^ 2 *
              (Riesz1.cyclicIndexDistance N a b : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd (by linarith) (by linarith)) (sq_nonneg _)
          _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_add hd]; norm_num [sub_eq_add_neg]
      · exact le_rfl
  calc
    _ ≤ ∑ b, B * A * R ^ (s - 3) *
        (if 0 < Riesz1.cyclicIndexDistance N a b ∧
          (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ η * R then
          (Riesz1.cyclicIndexDistance N a b : ℝ) ^ (2 - s) else 0) := by
      apply sum_le_sum; intro b _
      exact (hentry N i₀ η A hη hη' hA α hα a b).trans
        (mul_le_mul_of_nonneg_left (hpower b) (by positivity))
    _ ≤ B * A * R ^ (s - 3) * (2 * (η * R) ^ (3 - s)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (retained_distance_shell_sum N a hs (mul_pos hη hR)) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hη.le hR.le]
      have hc : R ^ (s - 3) * R ^ (3 - s) = 1 := by
        rw [← Real.rpow_add hR, show s - 3 + (3 - s) = 0 by ring, Real.rpow_zero]
      calc _ = 2 * B * A * η ^ (3 - s) * (R ^ (s - 3) * R ^ (3 - s)) := by ring
           _ = _ := by rw [hc, mul_one]

/-- The estimate in the proof of Lemma 5.11, with the coefficient
amplitude made explicit and a constant independent of `η`. -/
theorem diff_short_bound (s : Riesz1.RieszExponent) (γ : ℝ) (hγ : 1 / 2 ≤ γ) :
    let t := γ / 2 + 1 / 4
    let a := 3 / 2 - s.val
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ)) (η A : ℝ),
      0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) →
      ∀ u : Fin (N : ℕ) → ℝ,
      |(1 / 2 : ℝ) * ∑ i, ∑ j, retainedMatrix N i₀ η α i j *
        (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 * u i * u j| ≤
      C * A * η ^ (3 - s.val) *
        Real.sqrt (∑ i, (weightRadius N i i₀ ^ γ * u i) ^ 2) *
        Real.sqrt (∑ i, (weightRadius N i i₀ ^ a * u i) ^ 2) := by
  let t := γ / 2 + 1 / 4
  let a := 3 / 2 - s.val
  obtain ⟨B, hB, hrow⟩ := retained_kernel_row_bound (t := t) (g := γ) (h := a)
    s.property.1 s.property.2 (by dsimp [a]; linarith [s.property.2]) (by dsimp [t, a]; ring_nf)
  obtain ⟨D, hD, hcol⟩ := retained_kernel_row_bound (t := t) (g := a) (h := γ)
    s.property.1 s.property.2 (by linarith) (by dsimp [t, a]; ring_nf)
  refine ⟨B + D, by positivity, ?_⟩
  intro N i₀ η A hη hη' hA α hα u
  let E := fun i j => retainedMatrix N i₀ η α i j *
    (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 /
      (weightRadius N i i₀ ^ γ * weightRadius N j i₀ ^ a)
  let v := fun i => weightRadius N i i₀ ^ γ * u i
  let w := fun i => weightRadius N i i₀ ^ a * u i
  let K := (B + D) * A * η ^ (3 - s.val)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hr (i : Fin (N : ℕ)) : ∑ j, |E i j| ≤ K := by
    apply (hrow N i₀ η A hη hη' hA α hα i).trans
    dsimp [K]
    gcongr
    linarith
  have hc (j : Fin (N : ℕ)) : ∑ i, |E i j| ≤ K := by
    have hb := hcol N i₀ η A hη hη' hA α hα j
    have heq (i : Fin (N : ℕ)) : E i j =
        retainedMatrix N i₀ η α j i *
          (weightRadius N j i₀ ^ t - weightRadius N i i₀ ^ t) ^ 2 /
            (weightRadius N j i₀ ^ a * weightRadius N i i₀ ^ γ) := by
      dsimp [E]
      rw [retainedMatrix_symm N i₀ η α i j, sub_sq_comm, mul_comm (weightRadius N i i₀ ^ γ)]
    simp only [heq]
    apply hb.trans
    dsimp [K]
    gcongr
    linarith
  have hschur := FiniteSchurBounds.sqrt_sum_sq_norm_le E w hK hr hc
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at hschur
  have hid : (∑ i, ∑ j, retainedMatrix N i₀ η α i j *
      (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 * u i * u j) =
      ∑ i, v i * ∑ j, E i j * w j := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    dsimp [E, v, w]
    have hi := (Real.rpow_pos_of_pos (by linarith [one_le_weightRadius N i i₀] : 0 < weightRadius N i i₀) γ).ne'
    have hj := (Real.rpow_pos_of_pos (by linarith [one_le_weightRadius N j i₀] : 0 < weightRadius N j i₀) a).ne'
    field_simp
  have hcs : |∑ i, v i * ∑ j, E i j * w j| ≤
      Real.sqrt (∑ i, v i ^ 2) * Real.sqrt (∑ i, (∑ j, E i j * w j) ^ 2) := by
    apply (abs_sum_le_sum_abs _ _).trans
    simpa only [abs_mul, sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt univ
      (fun i => |v i|) (fun i => |∑ j, E i j * w j|)
  calc
    _ = (1 / 2 : ℝ) * |∑ i, v i * ∑ j, E i j * w j| := by rw [hid, abs_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (∑ i, v i ^ 2) * (K * Real.sqrt (∑ i, w i ^ 2))) := by
      exact mul_le_mul_of_nonneg_left (hcs.trans
        (mul_le_mul_of_nonneg_left hschur (Real.sqrt_nonneg _))) (by norm_num)
    _ ≤ K * Real.sqrt (∑ i, v i ^ 2) * Real.sqrt (∑ i, w i ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg (∑ i, v i ^ 2)))
        (Real.sqrt_nonneg (∑ i, w i ^ 2))]
    _ = _ := by dsimp [K, v, w, a]

/-- See the proof of Lemma 5.11 in the paper, including both the exact commutator
identity and its uniform estimate. The original coefficient amplitude is `A`. -/
theorem diff_short (s : Riesz1.RieszExponent) (γ : ℝ) (hγ : 1 / 2 ≤ γ) :
    let t := γ / 2 + 1 / 4
    let a := 3 / 2 - s.val
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ)) (η A : ℝ),
      0 < η → η < 1 / 4 → 0 ≤ A →
      ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ),
      (∀ k r, 0 ≤ α k r ∧ α k r ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) →
      ∀ (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) (u : Fin (N : ℕ) → ℝ),
      let R := retainedMatrix N i₀ η α
      let T := discardedMatrix N i₀ η α M
      (∑ i, weightRadius N i i₀ ^ (2 * t) * u i * (M *ᵥ u) i) =
        (∑ i, (weightRadius N i i₀ ^ t * u i) *
          (R *ᵥ (fun j => weightRadius N j i₀ ^ t * u j)) i) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, R i j *
          (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 * u i * u j) +
        (∑ i, weightRadius N i i₀ ^ (2 * t) * u i * (T *ᵥ u) i) ∧
      |(1 / 2 : ℝ) * ∑ i, ∑ j, R i j *
        (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 * u i * u j| ≤
      C * A * η ^ (3 - s.val) *
        Real.sqrt (∑ i, (weightRadius N i i₀ ^ γ * u i) ^ 2) *
        Real.sqrt (∑ i, (weightRadius N i i₀ ^ a * u i) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := diff_short_bound s γ hγ
  refine ⟨C, hC, ?_⟩
  intro N i₀ η A hη hη' hA α hα M u
  exact ⟨retained_commutator_identity N i₀ η (γ / 2 + 1 / 4) α M u,
    hbound N i₀ η A hη hη' hA α hα u⟩

/-- Bridge from `PeriodizedMatrixBounds` to all four row
conclusions of the proof of Lemma 5.11. The measurable interval
coefficients are supplied once, independently of the retention parameter. -/
theorem diff_tail_periodized (s : Riesz1.RieszExponent) :
    let q := 2 / s.val
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X] {ν : MeasureTheory.Measure X}
      (n N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (C₀ κ γ ε : ℝ), 0 ≤ C₀ →
      ∀ (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      PeriodizedMatrixBounds (ν := ν) s n N hN K C₀ κ γ ε M →
      ∃ α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → X → ℝ,
      (∀ k r, Measurable (α k r)) ∧ ∀ᵐ x ∂ν,
      (∀ k r, 0 ≤ α k r x ∧ α k r x ≤
        C₀ * (n : ℝ) ^ (κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) ∧
      (∀ a b, M x a b = ∑ k, ∑ r, α k r x *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) ∧
      ∀ (i₀ : Fin (N : ℕ)) (η : ℝ), 0 < η → η < 1 / 4 →
      ∀ a : Fin (N : ℕ),
      let T := discardedMatrix N i₀ η (fun k r => α k r x) (M x)
      let L := rowCutoff N i₀ η a
      let A := C₀ * (n : ℝ) ^ (κ * ε)
      (∀ b, |T a b| ≤ C * A * (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val) ∧
        |T a (b + 1) - T a b| ≤ C * A *
          (L + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-1 - s.val)) ∧
      (∑ b, |T a b| ^ q) ^ (1 / q) ≤ C * A * L ^ (-s.val / 2) ∧
      (∑ b, |cyclicTranslation N 1 (T a) b - T a b| ^ q) ^ (1 / q) ≤
        C * A * L ^ (-1 - s.val / 2) := by
  obtain ⟨C, hC, htail⟩ := diff_tail s
  refine ⟨C, hC, ?_⟩
  intro X _ ν n N hN K C₀ κ γ ε hC₀ M hM
  obtain ⟨α, hmeas, hcoeff⟩ := periodized_interval_entries s n N hN K C₀ κ γ ε M hM
  refine ⟨α, hmeas, ?_⟩
  filter_upwards [hcoeff] with x hx
  have ha : ∀ k r, 0 ≤ α k r x ∧ α k r x ≤
      C₀ * (n : ℝ) ^ (κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) :=
    fun k r => ⟨(hx.1 k r).1, (hx.1 k r).2.1⟩
  refine ⟨ha, hx.2, ?_⟩
  intro i₀ η hη hη' a
  exact htail N hN i₀ η (C₀ * (n : ℝ) ^ (κ * ε)) hη hη' (by positivity)
    (fun k r => α k r x) ha (M x) hx.2 a

end Riesz2.DerivativeCommutators
