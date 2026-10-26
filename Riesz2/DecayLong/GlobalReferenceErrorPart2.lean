/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalReferenceError
public import Riesz2.DecayLong.GlobalResolventKernel

/-!
# Quantitative endpoint estimates for the global reference error

Continuation of the proof of Lemma 5.13. All intervals,
coefficients and reference matrices use the definitions literally.
-/

public section

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators Fin.NatCast MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2
namespace GlobalReferenceErrorInternal

/-- Cyclic distance is the smaller forward or backward residue. -/
theorem distance_eq_min (N : ℕ+) (i j : Fin (N : ℕ)) :
    Riesz1.cyclicIndexDistance N i j = min (j - i).val ((N : ℕ) - (j - i).val) := by
  simp only [Riesz1.cyclicIndexDistance, Nat.dist, Fin.val_sub]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i.val ≤ j.val
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- An endpoint at length at most half the period has exactly that distance. -/
theorem distance_add_length (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : 2 * r ≤ (N : ℕ)) :
    Riesz1.cyclicIndexDistance N i (i + (r : Fin (N : ℕ))) = r := by
  rw [distance_eq_min, add_sub_cancel_left, Fin.val_natCast,
    Nat.mod_eq_of_lt (by have := N.pos; omega : r < (N : ℕ)), min_eq_left (by omega)]

/-- Distance from the excluded right endpoint to a point of the interval. -/
theorem distance_endpoint_le (N : ℕ+) (i j : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ))
    (hj : j ∈ cyclicIndexInterval N (i - (r : Fin (N : ℕ))) r) :
    Riesz1.cyclicIndexDistance N i j ≤ r := by
  have hj' := (mem_cyclicIndexInterval_iff N _ _ hr).mp hj
  have heq : j - (i - (r : Fin (N : ℕ))) = (j - i) + (r : Fin (N : ℕ)) := by abel
  rw [heq, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod] at hj'
  rw [distance_eq_min]
  have hv := (j - i).isLt
  by_cases hw : (j - i).val + r < (N : ℕ)
  · rw [Nat.mod_eq_of_lt hw] at hj'
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hj'
    omega

/-- Distance from the included left endpoint to a point of the interval. -/
theorem distance_start_le (N : ℕ+) (i j : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) (hj : j ∈ cyclicIndexInterval N i r) :
    Riesz1.cyclicIndexDistance N i j ≤ r := by
  have hj' := (mem_cyclicIndexInterval_iff N _ _ hr).mp hj
  rw [distance_eq_min]
  omega

/-- A coefficient at length `d` obeys a bound in the regularized distance. -/
theorem length_power_le {t : ℝ} (ht : 0 ≤ t) {r d : ℕ} (hr : 1 ≤ r)
    (hd : d ≤ r) :
    (r : ℝ) ^ (-t) ≤ 2 ^ t * (1 + (d : ℝ)) ^ (-t) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hdR : (d : ℝ) ≤ r := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hle : (1 + (d : ℝ)) / 2 ≤ r := by linarith
  calc
    (r : ℝ) ^ (-t) ≤ ((1 + (d : ℝ)) / 2) ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (neg_nonpos.mpr ht)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp

/-- The finite length tail needed after one endpoint cancellation. -/
theorem length_tail_le {t : ℝ} (ht : 1 < t) (L d : ℕ) :
    (∑ r : Fin L, if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-t) else 0) ≤
      (1 + 1 / (t - 1)) * 2 ^ (t - 1) * (1 + (d : ℝ)) ^ (1 - t) := by
  let R : ℝ := max 1 ((1 + (d : ℝ)) / 2)
  let g : ℕ → ℝ := fun k => if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0
  have hg0 (k : ℕ) : 0 ≤ g k := by dsimp [g]; split_ifs <;> positivity
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 (fun k => by
    dsimp [g]; split_ifs
    · exact le_rfl
    · positivity) (summable_one_add_rpow_neg ht)
  have hterm (r : Fin L) :
      (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-t) else 0) ≤ g r.val := by
    by_cases hd : d ≤ r.val + 1
    · have hdR : (d : ℝ) ≤ (r.val : ℝ) + 1 := by exact_mod_cast hd
      have hR : R ≤ 1 + (r.val : ℝ) := by
        dsimp [R]
        apply max_le <;> linarith [(Nat.cast_nonneg r.val : (0 : ℝ) ≤ r.val)]
      simp only [hd, ↓reduceIte, Nat.cast_add, Nat.cast_one, g]
      rw [ite_eq_left hR, add_comm]
    · simp only [hd, ↓reduceIte]
      exact hg0 _
  calc
    _ ≤ ∑ r : Fin L, g r.val := Finset.sum_le_sum fun r _ => hterm r
    _ = ∑ k ∈ Finset.range L, g k := Fin.sum_univ_eq_sum_range _ _
    _ ≤ ∑' k, g k := hgs.sum_le_tsum _ fun k _ => hg0 k
    _ ≤ (1 + 1 / (t - 1)) * R ^ (1 - t) := tsum_tail_indicator_le ht (le_max_left _ _)
    _ ≤ (1 + 1 / (t - 1)) * (((1 + (d : ℝ)) / 2) ^ (1 - t)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right _ _) (by linarith)
      · positivity
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num),
        show 1 - t = -(t - 1) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_eq_mul_inv, inv_inv]
      ring

/-- A single prescribed positive interval length contributes at most once. -/
theorem length_delta_sum_le (L d : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (∑ r : Fin L, if d = r.val + 1 then A else 0) ≤ A := by
  classical
  by_cases hd : 1 ≤ d ∧ d ≤ L
  · let r : Fin L := ⟨d - 1, by omega⟩
    have he : ∀ k : Fin L, d = k.val + 1 ↔ k = r := by
      intro k
      simp only [Fin.ext_iff, r]
      omega
    simp_rw [he]
    simp
  · have he : ∀ k : Fin L, ¬d = k.val + 1 := by intro k; have := k.isLt; omega
    simp only [he, ↓reduceIte, Finset.sum_const_zero]
    exact hA

/-- Quantitative first differences of an interval matrix. This internal lemma
allows arbitrary dependence of the coefficient on the start label. -/
theorem interval_first_difference_bound (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {t A : ℝ} (ht : 1 < t) (hA : 0 ≤ A)
    (a : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (ha : ∀ k r, |a k r| ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-t))
    (i j : Fin (N : ℕ)) :
    let T := fun i j => ∑ k, ∑ r, a k r *
      (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)
    |T i j - T (i - 1) j| ≤
      (2 * A * (1 + 1 / (t - 1)) * 2 ^ (t - 1)) *
        (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (1 - t) := by
  dsimp only
  rw [interval_matrix_first_difference N hN]
  let d := Riesz1.cyclicIndexDistance N i j
  have hterm (r : Fin ((N : ℕ) / 2)) :
      |a i r * (if j ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) -
        a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
          (if j ∈ cyclicIndexInterval N (i - ((r.val + 1 : ℕ) : Fin (N : ℕ)))
            (r.val + 1) then 1 else 0)| ≤
      2 * A * (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-t) else 0) := by
    have hr := r.isLt
    have hbound (k : Fin (N : ℕ)) (hh : j ∈ cyclicIndexInterval N k (r.val + 1) → d ≤ r.val + 1) :
        |a k r * (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)| ≤
          A * (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-t) else 0) := by
      by_cases hj : j ∈ cyclicIndexInterval N k (r.val + 1)
      · simpa only [hj, hh hj, ↓reduceIte, mul_one] using ha k r
      · simp only [hj, ↓reduceIte, mul_zero, abs_zero]
        split_ifs <;> positivity
    have h1 := hbound i (distance_start_le N i j (by omega))
    have h2 := hbound (i - ((r.val + 1 : ℕ) : Fin (N : ℕ)))
      (distance_endpoint_le N i j (by omega))
    exact (abs_sub _ _).trans (by linarith)
  calc
    _ ≤ ∑ r, |a i r * (if j ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) -
        a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
          (if j ∈ cyclicIndexInterval N (i - ((r.val + 1 : ℕ) : Fin (N : ℕ)))
            (r.val + 1) then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), 2 * A *
        (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-t) else 0) :=
      Finset.sum_le_sum fun r _ => hterm r
    _ = 2 * A * ∑ r : Fin ((N : ℕ) / 2),
        (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-t) else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * A * ((1 + 1 / (t - 1)) * 2 ^ (t - 1) * (1 + (d : ℝ)) ^ (1 - t)) :=
      mul_le_mul_of_nonneg_left (length_tail_le ht _ _) (by positivity)
    _ = _ := by ring

/-- Quantitative mixed differences of an interval matrix. The diagonal is
bounded by the summable coefficient series. Off the diagonal an endpoint pair
prescribes a unique length, including the antipodal length. -/
theorem interval_mixed_difference_bound (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {t A : ℝ} (ht : 1 < t) (hA : 0 ≤ A)
    (a : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (ha : ∀ k r, |a k r| ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-t))
    (i j : Fin (N : ℕ)) :
    let T := fun i j => ∑ k, ∑ r, a k r *
      (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)
    |(T i j - T (i - 1) j) - (T i (j - 1) - T (i - 1) (j - 1))| ≤
      (2 * A * ((∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)) + 2 ^ t)) *
        (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-t) := by
  dsimp only
  rw [interval_matrix_mixed_difference N hN]
  let d := Riesz1.cyclicIndexDistance N i j
  have hS : 0 ≤ ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t) := tsum_nonneg fun _ => by positivity
  have h2 : 0 ≤ (2 : ℝ) ^ t := by positivity
  by_cases hij : i = j
  · subst j
    have he (r : Fin ((N : ℕ) / 2)) :
        i ≠ i + ((r.val + 1 : ℕ) : Fin (N : ℕ)) ∧
        i ≠ i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) := by
      have hr := r.isLt
      have hz : ((r.val + 1 : ℕ) : Fin (N : ℕ)) ≠ 0 := by
        intro hh
        have hv := congrArg Fin.val hh
        rw [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
        omega
      constructor
      · intro hh
        apply hz
        have := add_left_cancel (hh.symm.trans (add_zero i).symm)
        exact this
      · intro hh
        apply hz
        have := sub_eq_self.mp hh.symm
        exact this
    simp only [he, ↓reduceIte, sub_zero, zero_sub, mul_one,
      mul_neg, sub_neg_eq_add, cyclicIndexDistance_self, Nat.cast_zero, add_zero,
      Real.one_rpow]
    calc
      _ ≤ ∑ r : Fin ((N : ℕ) / 2), |a i r + a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Fin ((N : ℕ) / 2), 2 * A * ((r.val + 1 : ℕ) : ℝ) ^ (-t) := by
        apply Finset.sum_le_sum
        intro r _
        exact (abs_add_le _ _).trans (by linarith [ha i r, ha (i - ↑(r.val + 1)) r])
      _ = 2 * A * ∑ k ∈ Finset.range ((N : ℕ) / 2), (1 + (k : ℝ)) ^ (-t) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Nat.cast_add, Nat.cast_one]
        rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((k : ℝ) + 1) ^ (-t))]
        simp only [add_comm]
      _ ≤ 2 * A * (∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)) :=
        mul_le_mul_of_nonneg_left (sum_range_one_add_rpow_le_tsum ht _) (by positivity)
      _ ≤ _ := by nlinarith
  · have hji : j ≠ i := Ne.symm hij
    simp only [hji, ↓reduceIte, zero_sub, mul_neg, sub_zero]
    let C := 2 * A * 2 ^ t * (1 + (d : ℝ)) ^ (-t)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hterm (r : Fin ((N : ℕ) / 2)) :
        |-(a i r * (if j = i + ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)) -
          a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
            (if j = i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)| ≤
        (if d = r.val + 1 then C else 0) := by
      have hr := r.isLt
      have hp (hh : j = i + ((r.val + 1 : ℕ) : Fin (N : ℕ))) : d = r.val + 1 := by
        dsimp [d]
        rw [hh]
        exact distance_add_length N i (by omega)
      have hm (hh : j = i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) : d = r.val + 1 := by
        dsimp [d]
        have hs : Riesz1.cyclicIndexDistance N i j = Riesz1.cyclicIndexDistance N j i := by
          simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
        rw [hs]
        have hi : i = j + ((r.val + 1 : ℕ) : Fin (N : ℕ)) := by rw [hh]; abel
        rw [hi]
        exact distance_add_length N j (by omega)
      have hcoef (k : Fin (N : ℕ)) (hd : d = r.val + 1) :
          |a k r| ≤ A * 2 ^ t * (1 + (d : ℝ)) ^ (-t) := by
        calc _ ≤ _ := ha k r
             _ ≤ A * (2 ^ t * (1 + (d : ℝ)) ^ (-t)) :=
                mul_le_mul_of_nonneg_left (length_power_le (by linarith : 0 ≤ t)
                  (by omega) hd.le) hA
             _ = _ := by ring
      by_cases hd : d = r.val + 1
      · rw [ite_eq_left hd]
        have h1 : |a i r * (if j = i + ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)| ≤
            A * 2 ^ t * (1 + (d : ℝ)) ^ (-t) := by
          split_ifs
          · simpa only [mul_one] using hcoef i hd
          · simp only [mul_zero, abs_zero]; positivity
        have h2' : |a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
            (if j = i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)| ≤
            A * 2 ^ t * (1 + (d : ℝ)) ^ (-t) := by
          split_ifs
          · simpa only [mul_one] using hcoef (i - ↑(r.val + 1)) hd
          · simp only [mul_zero, abs_zero]; positivity
        exact (abs_sub _ _).trans (by rw [abs_neg]; dsimp [C]; linarith)
      · have hnp : j ≠ i + ((r.val + 1 : ℕ) : Fin (N : ℕ)) := fun hh => hd (hp hh)
        have hnm : j ≠ i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) := fun hh => hd (hm hh)
        simp only [hd, hnp, hnm, ↓reduceIte, mul_zero, neg_zero, sub_zero, abs_zero, le_refl]
    calc
      _ ≤ ∑ r : Fin ((N : ℕ) / 2),
          |-(a i r * (if j = i + ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)) -
            a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
              (if j = i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Fin ((N : ℕ) / 2), if d = r.val + 1 then C else 0 :=
        Finset.sum_le_sum fun r _ => hterm r
      _ ≤ C := length_delta_sum_le _ _ _ hC
      _ ≤ _ := by
        dsimp [C]
        have hh := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * A) hS)
          (Real.rpow_nonneg (by positivity : 0 ≤ 1 + (d : ℝ)) (-t))
        nlinarith

/-- The reference written with the same length indices as the matrix-field assumptions. The antipodal half weight is retained. -/
theorem reference_fin_lengths (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (i j : Fin (N : ℕ)) :
    referenceIntervalMatrix s N hN K i j =
      ∑ k, ∑ r : Fin ((N : ℕ) / 2),
        (if K ≤ r.val + 1 then
          (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0) *
        (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
  classical
  unfold referenceIntervalMatrix
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_filter]
  rw [Finset.sum_range_succ']
  simp only [show ¬1 ≤ (0 : ℕ) by omega, false_and, ↓reduceIte, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    (if K ≤ r + 1 then
      (1 - if 2 * (r + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) *
    (if i ∈ cyclicIndexInterval N k (r + 1) then 1 else 0) *
    (if j ∈ cyclicIndexInterval N k (r + 1) then 1 else 0))]
  apply Finset.sum_congr rfl
  intro r _
  simp only [show 1 ≤ r + 1 by omega, true_and]
  split_ifs <;> first | rfl | simp_all only [mul_zero, zero_mul]

/-- Absolute coefficient envelope of the reference, uniform in the period and
cutoff. The statement uses the curvature. -/
theorem reference_coefficient_bound (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ)
      (r : Fin ((N : ℕ) / 2)),
      |(if K ≤ r.val + 1 then
        (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0)| ≤
        C * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
  obtain ⟨c, C, hc, hC, hb⟩ := sampledSecondDifference_bounds s
  refine ⟨C, hC, ?_⟩
  intro N hN K r
  have hr := r.isLt
  have hz : (↑(r.val + 1) : Fin (N : ℕ)) ≠ 0 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hd : Riesz1.cyclicIndexDistance N (↑(r.val + 1)) 0 = r.val + 1 := by
    rw [show Riesz1.cyclicIndexDistance N (↑(r.val + 1)) 0 =
      Riesz1.cyclicIndexDistance N 0 (↑(r.val + 1)) by
        simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]]
    simpa only [zero_add] using distance_add_length N 0 (r := r.val + 1) (by omega)
  have hh := (hb N hN _ hz).2
  rw [hd] at hh
  have hp := (sampledSecondDifference_pos s N hN hz).le
  split_ifs <;> rw [abs_of_nonneg (by positivity)] <;> nlinarith

/-- Applying an absolute coefficient envelope to an arbitrary interval matrix
also bounds every entry by the diagonal coefficient sum. -/
theorem interval_entry_bound (N : ℕ+) {t A : ℝ} (ht : 2 < t) (hA : 0 ≤ A)
    (a : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (ha : ∀ k r, |a k r| ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-t))
    (i j : Fin (N : ℕ)) :
    |∑ k, ∑ r, a k r *
      (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)| ≤
      A * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(t - 1)) := by
  classical
  rw [Finset.sum_comm]
  have hlen (r : Fin ((N : ℕ) / 2)) :
      (∑ k : Fin (N : ℕ), |a k r *
        (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)|) ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-(t - 1)) := by
    have hr := r.isLt
    calc
      _ ≤ ∑ k : Fin (N : ℕ),
          (A * ((r.val + 1 : ℕ) : ℝ) ^ (-t)) *
          (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
          (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
        apply Finset.sum_le_sum
        intro k _
        split_ifs
        · simpa only [mul_one] using ha k r
        · simp only [mul_zero, abs_zero]; positivity
        · norm_num only [mul_one, mul_zero, zero_mul, abs_zero]
        · norm_num only [mul_one, mul_zero, zero_mul, abs_zero]
      _ = (A * ((r.val + 1 : ℕ) : ℝ) ^ (-t)) * (r.val + 1) := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, ← Finset.mul_sum, cyclicIndexInterval_pair_count N (by omega) i i,
          cyclicIndexDistance_self, Nat.sub_zero, Nat.cast_add, Nat.cast_one]
      _ = _ := by
        rw [show (-(t - 1)) = -t + 1 by ring,
          Real.rpow_add_one (by positivity : ((r.val + 1 : ℕ) : ℝ) ≠ 0)]
        push_cast
        ring
  calc
    _ ≤ ∑ r : Fin ((N : ℕ) / 2),
        ∑ k : Fin (N : ℕ), |a k r *
          (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
          (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun r _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), A * ((r.val + 1 : ℕ) : ℝ) ^ (-(t - 1)) :=
      Finset.sum_le_sum fun r _ => hlen r
    _ = A * ∑ k ∈ Finset.range ((N : ℕ) / 2), (1 + (k : ℝ)) ^ (-(t - 1)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((k : ℝ) + 1) ^ (-(t - 1))) ]
      simp only [add_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_range_one_add_rpow_le_tsum (by linarith) _) hA

/-- Finite Euclidean Schur bound, with no symmetry assumption. -/
theorem schur_norm_le {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hr : ∀ i, ∑ j, |E i j| ≤ B)
    (hc : ∀ j, ∑ i, |E i j| ≤ B) : ‖E‖ ≤ B := by
  have hquad (u : Fin n → ℝ) :
      ∑ i, (E *ᵥ u) i ^ 2 ≤ B ^ 2 * ∑ j, u j ^ 2 := by
    have hrow (i : Fin n) : (E *ᵥ u) i ^ 2 ≤ B * ∑ j, |E i j| * u j ^ 2 := by
      have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (Finset.univ : Finset (Fin n))
        (f := fun j => |E i j|) (g := fun j => |E i j| * u j ^ 2)
        (r := fun j => E i j * u j)
        (fun j _ => abs_nonneg _) (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun j _ => by rw [mul_pow, ← mul_assoc, ← sq, sq_abs])
      exact h.trans (mul_le_mul_of_nonneg_right (hr i)
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
    calc
      _ ≤ ∑ i, B * ∑ j, |E i j| * u j ^ 2 := Finset.sum_le_sum fun i _ => hrow i
      _ = B * ∑ j, (∑ i, |E i j|) * u j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ ≤ B * ∑ j, B * u j ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) E‖ ≤ B
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  have hh : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) E u‖ ^ 2 ≤ (B * ‖u‖) ^ 2 := by
    rw [mul_pow]
    simp only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
      Real.norm_eq_abs, sq_abs]
    exact hquad u.ofLp
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) E u), norm_nonneg u, mul_nonneg hB (norm_nonneg u)]

/-- A common cyclic interval of length at most half the period is longer than
its endpoint distance. This includes coincident labels and wraparound. -/
theorem distance_lt_length_of_mem (N : ℕ+) {r : ℕ} (hr : 2 * r ≤ (N : ℕ))
    (k i j : Fin (N : ℕ)) (hi : i ∈ cyclicIndexInterval N k r)
    (hj : j ∈ cyclicIndexInterval N k r) : Riesz1.cyclicIndexDistance N i j < r := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (N : ℕ))))
    (f := fun k => (if i ∈ cyclicIndexInterval N k r then (1 : ℝ) else 0) *
      (if j ∈ cyclicIndexInterval N k r then 1 else 0))
    (fun l _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
  rw [ite_eq_left hi, ite_eq_left hj, one_mul, cyclicIndexInterval_pair_count N hr i j] at hh
  have hn : 1 ≤ r - Riesz1.cyclicIndexDistance N i j := by exact_mod_cast hh
  omega

/-- Removing intervals shorter than `K` leaves entries at distance at least
`K` unchanged. This is the support assertion in the proof of Lemma 5.13. -/
theorem reference_cutoff_support (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (i j : Fin (N : ℕ))
    (hd : K ≤ Riesz1.cyclicIndexDistance N i j) :
    referenceIntervalMatrix s N hN K i j = referenceIntervalMatrix s N hN 1 i j := by
  classical
  rw [reference_fin_lengths, reference_fin_lengths]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro r _
  have hr := r.isLt
  rw [ite_eq_left (by omega : 1 ≤ r.val + 1)]
  by_cases hk : K ≤ r.val + 1
  · rw [ite_eq_left hk]
  · have hn : ¬ (i ∈ cyclicIndexInterval N k (r.val + 1) ∧
        j ∈ cyclicIndexInterval N k (r.val + 1)) := by
      rintro ⟨hi, hj⟩
      have := distance_lt_length_of_mem N (by omega) k i j hi hj
      omega
    rw [ite_eq_right hk]
    by_cases hi : i ∈ cyclicIndexInterval N k (r.val + 1)
    · have hj : j ∉ cyclicIndexInterval N k (r.val + 1) := fun hj => hn ⟨hi, hj⟩
      simp only [hi, hj, ↓reduceIte, mul_one, mul_zero]
    · simp only [hi, ↓reduceIte, mul_zero, zero_mul]

/-- Explicit cutoff comparison used internally in the reference-error proof.
The coefficient-envelope hypothesis is discharged by `reference_coefficient_bound`. -/
theorem reference_cutoff_bound (s : Riesz1.RieszExponent) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (r : Fin ((N : ℕ) / 2)),
      |(if K ≤ r.val + 1 then
        (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0)| ≤
        C * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2))
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (hK : 1 ≤ K) (i j : Fin (N : ℕ)) :
    |referenceIntervalMatrix s N hN K i j - sampledRieszKernel s N hN (j - i)| ≤
      (2 * C * (∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1))) *
        (K : ℝ) ^ (1 + s.val / 2) *
        (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2) := by
  let q := 1 + s.val / 2
  let D : ℝ := 1 + (Riesz1.cyclicIndexDistance N i j : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith [s.property.1]
  have hS : 0 ≤ ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1) := tsum_nonneg fun _ => by positivity
  rw [← referenceIntervalMatrix_full s N hN i j]
  by_cases hd : K ≤ Riesz1.cyclicIndexDistance N i j
  · rw [reference_cutoff_support s N hN K i j hd, sub_self, abs_zero]
    positivity
  · have hDK : D ≤ (K : ℝ) := by dsimp [D]; exact_mod_cast (by omega : 1 + Riesz1.cyclicIndexDistance N i j ≤ K)
    have hfactor : 1 ≤ (K : ℝ) ^ q * D ^ (-q) := by
      calc
        1 = D ^ q * D ^ (-q) := by rw [← Real.rpow_add hD]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hD.le hDK hq) (by positivity)
    have hn (K : ℕ) : |referenceIntervalMatrix s N hN K i j| ≤
        C * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1) := by
      rw [reference_fin_lengths]
      have hh := interval_entry_bound N (t := s.val + 2) (by linarith [s.property.1]) hC
        (fun _ r => if K ≤ r.val + 1 then
          (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0)
        (fun k r => by simpa only [show -(s.val + 2) = -s.val - 2 by ring] using hb N hN K r) i j
      simpa only [show -(s.val + 2 - 1) = -s.val - 1 by ring] using hh
    calc
      _ ≤ |referenceIntervalMatrix s N hN K i j| + |referenceIntervalMatrix s N hN 1 i j| := abs_sub _ _
      _ ≤ 2 * C * (∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)) := by linarith [hn K, hn 1]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hfactor (by positivity :
          0 ≤ 2 * C * (∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)))
        simpa only [mul_one, mul_assoc, show -q = -1 - s.val / 2 by dsimp [q]; ring] using hh

/-- Symmetry of an interval matrix, also for signed coefficients. -/
theorem interval_matrix_symm (N : ℕ+)
    (a : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (i j : Fin (N : ℕ)) :
    (∑ k, ∑ r, a k r *
      (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) =
    ∑ k, ∑ r, a k r *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Subtracting twice the full reference gives a signed interval matrix with
an explicit coefficient envelope. This follows from the matrix field assumptions. -/
theorem error_interval_representation {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ) (_hC : 0 ≤ C)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    {R : ℝ} (_hR : 0 ≤ R)
    (hb : ∀ r : Fin ((m : ℕ) / 2),
      |(1 - if 2 * (r.val + 1) = (m : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s m hm (↑(r.val + 1) : Fin (m : ℕ))| ≤
      R * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) :
    ∀ᵐ x ∂ν, ∃ e : Fin (m : ℕ) → Fin ((m : ℕ) / 2) → ℝ,
      (∀ k r, |e k r| ≤ (C * (n : ℝ) ^ (κ * ε) + 2 * R) *
        ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) ∧
      ∀ i j, (M x - (2 : ℝ) • rieszMatrix s m hm) i j =
        ∑ k, ∑ r, e k r *
          (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
          (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) := by
  obtain ⟨a, _, ha⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  filter_upwards [ha] with x hx
  let b : Fin ((m : ℕ) / 2) → ℝ := fun r =>
    (1 - if 2 * (r.val + 1) = (m : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s m hm (↑(r.val + 1) : Fin (m : ℕ))
  refine ⟨fun k r => a k r x - 2 * b r, ?_, ?_⟩
  · intro k r
    have hh := (abs_sub (a k r x) (2 * b r)).trans
      (add_le_add (show |a k r x| ≤ C * (n : ℝ) ^ (κ * ε) *
        ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) by
          rw [abs_of_nonneg (hx.1 k r).1]; exact (hx.1 k r).2.1)
        (show |2 * b r| ≤ 2 * (R * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) by
          rw [abs_mul, abs_of_pos two_pos]; exact mul_le_mul_of_nonneg_left (hb r) two_pos.le))
    nlinarith
  · intro i j
    change M x i j - 2 * sampledRieszKernel s m hm (j - i) = _
    rw [hx.2 i j, ← referenceIntervalMatrix_full s m hm i j, reference_fin_lengths]
    simp only [show ∀ r : Fin ((m : ℕ) / 2), 1 ≤ r.val + 1 by intro r; omega, ↓reduceIte,
      sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [b, sub_mul, Finset.sum_sub_distrib, mul_assoc, one_mul]

/-- Raising the prescribed floor cutoff to a nonnegative power preserves the
explicit polynomial loss. -/
theorem cutoff_power_le (n : ℕ+) (ε q : ℝ) (hq : 0 ≤ q) (M₀ : ℕ) :
    (((⌊(n : ℝ) ^ ε⌋₊ ^ M₀ : ℕ) : ℝ)) ^ q ≤
      (n : ℝ) ^ (((M₀ : ℝ) * q) * ε) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hfloor := Nat.floor_le (show 0 ≤ (n : ℝ) ^ ε by positivity)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg ⌊(n : ℝ) ^ ε⌋₊) hfloor M₀
  rw [Nat.cast_pow]
  calc
    _ ≤ (((n : ℝ) ^ ε) ^ M₀) ^ q := Real.rpow_le_rpow (by positivity) hpow hq
    _ = _ := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_mul hn.le]
      congr 1
      ring

end GlobalReferenceErrorInternal
/-- The quantitative entry and difference clauses of the proof of Lemma 5.13, with all cutoff and coefficient losses explicit.
No scalar-form hypothesis is needed for these deterministic estimates. -/
theorem global_reference_error_estimates (s : Riesz1.RieszExponent) :
    ∃ R : ℝ, 0 < R ∧ ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (K : ℕ) (_hK : 1 ≤ K) (C : ℝ) (_hC : 0 ≤ C) (κ γ ε : ℝ)
      {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
      PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
      let q := 1 + s.val / 2
      let t := s.val + 2
      let S := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)
      let U := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)
      let A := C * (n : ℝ) ^ (κ * ε) + 2 * R
      let P := C * (n : ℝ) ^ (κ * ε) + 4 * R * S * (K : ℝ) ^ q
      let F := 2 * A * (1 + 1 / (t - 1)) * 2 ^ (t - 1)
      let G := 2 * A * (U + 2 ^ t)
      let B := P * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q))
      ∀ᵐ x ∂ν,
        let E := M x - (2 : ℝ) • rieszMatrix s m hm
        (∀ i j, |E i j| ≤ P * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-q)) ∧
        (∀ i j, |E i j - E (i - 1) j| + |E i j - E i (j - 1)| ≤
          2 * F * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) ∧
        (∀ i j, |(E i j - E (i - 1) j) - (E i (j - 1) - E (i - 1) (j - 1))| ≤
          G * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val)) ∧
        (∀ i, ∑ j, |E i j| ≤ B) ∧ (∀ j, ∑ i, |E i j| ≤ B) ∧ ‖E‖ ≤ B := by
  obtain ⟨R, hR, hb⟩ := GlobalReferenceErrorInternal.reference_coefficient_bound s
  refine ⟨R, hR, ?_⟩
  intro n m hm K hK C hC κ γ ε α _ ν M hM
  let q := 1 + s.val / 2
  let t := s.val + 2
  let S := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)
  let U := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)
  let A := C * (n : ℝ) ^ (κ * ε) + 2 * R
  let P := C * (n : ℝ) ^ (κ * ε) + 4 * R * S * (K : ℝ) ^ q
  let F := 2 * A * (1 + 1 / (t - 1)) * 2 ^ (t - 1)
  let G := 2 * A * (U + 2 ^ t)
  let B := P * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q))
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := mul_nonneg hP (mul_nonneg two_pos.le (tsum_nonneg fun _ => by positivity))
  have hrep := GlobalReferenceErrorInternal.error_interval_representation s n m hm K C κ γ ε
    hC M hM hR.le (fun r => by simpa only [show 1 ≤ r.val + 1 by omega, ↓reduceIte] using hb m hm 1 r)
  have hcomp := periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε hC M hM
  filter_upwards [hrep, hcomp] with x hx hcx
  let E := M x - (2 : ℝ) • rieszMatrix s m hm
  obtain ⟨e, he, hre⟩ := hx
  have hentry (i j : Fin (m : ℕ)) :
      |E i j| ≤ P * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-q) := by
    have hr := GlobalReferenceErrorInternal.reference_cutoff_bound s hR.le hb m hm K hK i j
    have hc := hcx i j
    have hh : |E i j| ≤
        |M x i j - 2 * referenceIntervalMatrix s m hm K i j| +
          2 * |referenceIntervalMatrix s m hm K i j - sampledRieszKernel s m hm (j - i)| := by
      change |M x i j - 2 * sampledRieszKernel s m hm (j - i)| ≤ _
      have ht := abs_add_le (M x i j - 2 * referenceIntervalMatrix s m hm K i j)
        (2 * (referenceIntervalMatrix s m hm K i j - sampledRieszKernel s m hm (j - i)))
      rw [show M x i j - 2 * referenceIntervalMatrix s m hm K i j +
        2 * (referenceIntervalMatrix s m hm K i j - sampledRieszKernel s m hm (j - i)) =
          M x i j - 2 * sampledRieszKernel s m hm (j - i) by ring,
        abs_mul, show |(2 : ℝ)| = 2 by norm_num] at ht
      exact ht
    change |M x i j - 2 * referenceIntervalMatrix s m hm K i j| ≤ _ at hc
    have hh' := hh.trans (add_le_add hc (mul_le_mul_of_nonneg_left hr two_pos.le))
    dsimp only [P, q, S] at *
    rw [show -(1 + s.val / 2) = -1 - s.val / 2 by ring]
    nlinarith
  have hsymm (i j : Fin (m : ℕ)) : E i j = E j i := by
    dsimp only [E]
    rw [hre i j, hre j i]
    exact GlobalReferenceErrorInternal.interval_matrix_symm m e i j
  have hfirst (i j : Fin (m : ℕ)) :
      |E i j - E (i - 1) j| ≤ F * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val) := by
    dsimp only [E]
    simp_rw [hre]
    have hh := GlobalReferenceErrorInternal.interval_first_difference_bound m hm
      (t := t) (by dsimp [t]; linarith [s.property.1]) hA e
      (fun k r => by simpa only [t, show -(s.val + 2) = -s.val - 2 by ring] using he k r) i j
    simpa only [show 1 - t = -1 - s.val by dsimp [t]; ring] using hh
  have hmixed (i j : Fin (m : ℕ)) :
      |(E i j - E (i - 1) j) - (E i (j - 1) - E (i - 1) (j - 1))| ≤
        G * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val) := by
    dsimp only [E]
    simp_rw [hre]
    have hh := GlobalReferenceErrorInternal.interval_mixed_difference_bound m hm
      (t := t) (by dsimp [t]; linarith [s.property.1]) hA e
      (fun k r => by simpa only [t, show -(s.val + 2) = -s.val - 2 by ring] using he k r) i j
    simpa only [G, U, show -t = -2 - s.val by dsimp [t]; ring] using hh
  have hrs := GlobalReferenceErrorInternal.row_column_sums_of_decay m q
    (by dsimp [q]; linarith [s.property.1]) P hP E hentry
  refine ⟨hentry, ?_, hmixed, hrs.1, hrs.2,
    GlobalReferenceErrorInternal.schur_norm_le E hB hrs.1 hrs.2⟩
  intro i j
  have hi := hfirst i j
  have hj := hfirst j i
  rw [hsymm j i, hsymm (j - 1) i] at hj
  have hd : Riesz1.cyclicIndexDistance m j i = Riesz1.cyclicIndexDistance m i j := by
    simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
  rw [hd] at hj
  linarith

/-- Backward-difference form of the proof of Lemma 5.13. The loss exponent is
chosen before ε and the input prefactor. The estimates hold for arbitrary
measures, and hence for every conservative scalar probability space of Assumptions 5.2. They are independent of β. All configuration-dependent conclusions
use the almost-everywhere convention of the matrix assumptions. -/
theorem global_error_backward_differences (s : Riesz1.RieszExponent)
    (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (_hγₛ : 0 ≤ γₛ) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ε : ℝ), 0 < ε → ∀ (Cₛ : ℝ), 1 ≤ Cₛ →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (_hn : 2 ≤ (n : ℕ)) (_hnm : (n : ℕ) ≤ (m : ℕ))
        (_hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
          (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
        ∃ a B : ℝ, 0 < a ∧ a ≤ 1 ∧ 1 ≤ B ∧ a⁻¹ + B ≤ C * (n : ℝ) ^ (κ * ε) ∧
          ∀ᵐ x ∂ν,
            let E := M x - (2 : ℝ) • rieszMatrix s m hm
            (∀ i j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε) *
              (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)) ∧
            (∀ i j, |E i j - E (i - 1) j| + |E i j - E i (j - 1)| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) ∧
            (∀ i j, |(E i j - E (i - 1) j) - (E i (j - 1) - E (i - 1) (j - 1))| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val)) ∧
            (∀ i, ∑ j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            (∀ j, ∑ i, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            a • (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) ≤ M x ∧ ‖E‖ ≤ B := by
  obtain ⟨R, hR, hest⟩ := global_reference_error_estimates s
  let q := 1 + s.val / 2
  let t := s.val + 2
  let κ := κₛ + (M₀ : ℝ) * q + 1
  have hq : 0 < q := by dsimp [q]; linarith [s.property.1]
  have ht : 1 < t := by dsimp [t]; linarith [s.property.1]
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, ?_⟩
  intro ε hε Cₛ hCₛ
  let S := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)
  let U := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)
  let Z := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q)
  let D := Cₛ + 4 * R * S
  let J := Cₛ + 2 * R
  let F := 2 * (1 + 1 / (t - 1)) * 2 ^ (t - 1)
  let G := 2 * (U + 2 ^ t)
  let C := 1 + D + 2 * F * J + G * J + D * Z + Cₛ + 1
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hU : 0 ≤ U := tsum_nonneg fun _ => by positivity
  have hZ : 0 ≤ Z := mul_nonneg two_pos.le (tsum_nonneg fun _ => by positivity)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hFJ : 0 ≤ 2 * F * J := by positivity
  have hGJ : 0 ≤ G * J := by positivity
  have hDZ : 0 ≤ D * Z := by positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith only [hD, hFJ, hGJ, hDZ, hCₛ]
  have hCD : D ≤ C := by dsimp [C]; linarith only [hFJ, hGJ, hDZ, hCₛ]
  have hCF : 2 * F * J ≤ C := by dsimp [C]; linarith only [hD, hGJ, hDZ, hCₛ]
  have hCG : G * J ≤ C := by dsimp [C]; linarith only [hD, hFJ, hDZ, hCₛ]
  have hCZ : D * Z ≤ C := by dsimp [C]; linarith only [hD, hFJ, hGJ, hCₛ]
  have hCA : Cₛ + 1 + D * Z ≤ C := by dsimp [C]; linarith only [hD, hFJ, hGJ]
  refine ⟨C, hC1, ?_⟩
  intro n m hm hn _ _ K hK _ α _ ν M hM
  let L := (n : ℝ) ^ (κ * ε)
  let W := (n : ℝ) ^ (κₛ * ε)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ (n : ℕ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hL : 1 ≤ L := Real.one_le_rpow hn1 (mul_nonneg hκ.le hε.le)
  have hW : 1 ≤ W := Real.one_le_rpow hn1 (mul_nonneg hκₛ hε.le)
  have hWL : W ≤ L := Real.rpow_le_rpow_of_exponent_le hn1
    (mul_le_mul_of_nonneg_right (by dsimp [κ]; linarith only [mul_nonneg (Nat.cast_nonneg M₀) hq.le]) hε.le)
  have hKL : (K : ℝ) ^ q ≤ L := by
    have hh := GlobalReferenceErrorInternal.cutoff_power_le n ε q hq.le M₀
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (by dsimp [κ]; linarith) hε.le))
  have hPJ : Cₛ * W + 2 * R ≤ J * L := by
    have h1 := mul_le_mul_of_nonneg_left hWL (by linarith only [hCₛ] : 0 ≤ Cₛ)
    have h2 := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * R)
    dsimp [J]
    nlinarith only [h1, h2]
  have hPD : Cₛ * W + 4 * R * S * (K : ℝ) ^ q ≤ D * L := by
    have h1 := mul_le_mul_of_nonneg_left hWL (by linarith only [hCₛ] : 0 ≤ Cₛ)
    have h2 := mul_le_mul_of_nonneg_left hKL (by positivity : 0 ≤ 4 * R * S)
    dsimp [D]
    nlinarith only [h1, h2]
  let a := Cₛ⁻¹ * (n : ℝ) ^ (-κₛ * ε)
  let B := max 1 (D * Z * L)
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : a = (Cₛ * W)⁻¹ := by
    dsimp [a, W]
    rw [show -κₛ * ε = -(κₛ * ε) by ring, Real.rpow_neg hn0.le, _root_.mul_inv_rev, mul_comm]
  have ha1 : a ≤ 1 := by
    rw [hae]
    apply inv_le_one_of_one_le₀
    nlinarith only [hCₛ, hW, mul_nonneg (sub_nonneg.mpr hCₛ) (sub_nonneg.mpr hW)]
  have hB1 : 1 ≤ B := le_max_left _ _
  have haL : a⁻¹ ≤ Cₛ * L := by
    rw [hae, inv_inv]
    exact mul_le_mul_of_nonneg_left hWL (by linarith only [hL, hCₛ])
  have hBL : B ≤ (1 + D * Z) * L := by
    apply max_le
    · have hp := mul_nonneg hDZ (show 0 ≤ L by linarith only [hL])
      nlinarith only [hL, hp]
    · nlinarith only [hL]
  have hab : a⁻¹ + B ≤ C * L := by
    calc _ ≤ Cₛ * L + (1 + D * Z) * L := add_le_add haL hBL
         _ = (Cₛ + 1 + D * Z) * L := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hCA (by linarith only [hL, hCₛ])
  refine ⟨a, B, ha, ha1, hB1, hab, ?_⟩
  have he := hest n m hm K hK Cₛ (by linarith only [hL, hCₛ]) κₛ γₛ ε ν M hM
  have hc := periodizedMatrixBounds_coercive s n m hm K Cₛ κₛ γₛ ε M hM
  filter_upwards [he, hc] with x hx hcx
  let E := M x - (2 : ℝ) • rieszMatrix s m hm
  have hentry (i j : Fin (m : ℕ)) : |E i j| ≤ C * L *
      (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2) := by
    have hh := hx.1 i j
    change |E i j| ≤ (Cₛ * W + 4 * R * S * (K : ℝ) ^ q) *
      (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-q) at hh
    rw [show -q = -1 - s.val / 2 by dsimp [q]; ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hPD.trans
      (mul_le_mul_of_nonneg_right hCD (by linarith only [hL, hCₛ]))) (by positivity))
  have hfirst (i j : Fin (m : ℕ)) :
      |E i j - E (i - 1) j| + |E i j - E i (j - 1)| ≤ C * L *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val) := by
    have hh := hx.2.1 i j
    have hfc : 2 * (2 * (Cₛ * W + 2 * R) * (1 + 1 / (t - 1)) * 2 ^ (t - 1)) ≤ C * L := by
      calc
        _ = (2 * F) * (Cₛ * W + 2 * R) := by dsimp [F]; ring
        _ ≤ (2 * F) * (J * L) := mul_le_mul_of_nonneg_left hPJ (by positivity)
        _ = (2 * F * J) * L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCF (by linarith only [hL, hCₛ])
    exact hh.trans (mul_le_mul_of_nonneg_right hfc (by positivity))
  have hmixed (i j : Fin (m : ℕ)) :
      |(E i j - E (i - 1) j) - (E i (j - 1) - E (i - 1) (j - 1))| ≤ C * L *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val) := by
    have hh := hx.2.2.1 i j
    have hgc : 2 * (Cₛ * W + 2 * R) * (U + 2 ^ t) ≤ C * L := by
      calc
        _ = G * (Cₛ * W + 2 * R) := by dsimp [G]; ring
        _ ≤ G * (J * L) := mul_le_mul_of_nonneg_left hPJ hG
        _ = (G * J) * L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCG (by linarith only [hL, hCₛ])
    exact hh.trans (mul_le_mul_of_nonneg_right hgc (by positivity))
  have hbound : (Cₛ * W + 4 * R * S * (K : ℝ) ^ q) * Z ≤ D * Z * L := by
    have hh := mul_le_mul_of_nonneg_right hPD hZ
    nlinarith only [hh]
  have hboundC : (Cₛ * W + 4 * R * S * (K : ℝ) ^ q) * Z ≤ C * L :=
    hbound.trans (mul_le_mul_of_nonneg_right hCZ (by linarith only [hL, hCₛ]))
  exact ⟨hentry, hfirst, hmixed, fun i => (hx.2.2.2.1 i).trans hboundC,
    (fun j => (hx.2.2.2.2.1 j).trans hboundC), hcx,
    hx.2.2.2.2.2.trans (hbound.trans (le_max_right _ _))⟩

namespace GlobalReferenceErrorInternal

/-- Simultaneous cyclic translation preserves distance. -/
theorem distance_translate (N : ℕ+) (i j t : Fin (N : ℕ)) :
    Riesz1.cyclicIndexDistance N (i + t) (j + t) = Riesz1.cyclicIndexDistance N i j := by
  rw [distance_eq_min, distance_eq_min]
  have hh : j + t - (i + t) = j - i := by abel
  rw [hh]

/-- Moving one endpoint one step changes a regularized power envelope by at
most `2^q`. This converts the proved backward estimates to forward ones. -/
theorem forward_distance_power (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i j : Fin (N : ℕ)) {q : ℝ} (hq : 0 ≤ q) :
    (1 + (Riesz1.cyclicIndexDistance N (i + 1) j : ℝ)) ^ (-q) ≤
      2 ^ q * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-q) := by
  have ht := cyclicIndexDistance_triangle i (i + 1) j
  have hs : Riesz1.cyclicIndexDistance N i (i + 1) = 1 := by
    simpa only [Nat.cast_one] using distance_add_length N i (r := 1) (by omega)
  rw [hs] at ht
  have htR : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤
      1 + (Riesz1.cyclicIndexDistance N (i + 1) j : ℝ) := by exact_mod_cast ht
  have hnonneg : 0 ≤ (Riesz1.cyclicIndexDistance N (i + 1) j : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) / 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [htR, hnonneg]) (neg_nonpos.mpr hq)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp

end GlobalReferenceErrorInternal

/-- See the proof of Lemma 5.13 in the paper, with cyclic forward differences. Constants precede the sizes and
the field, and the loss exponent precedes ε and the input prefactor. The
estimate is independent of β and valid for every measure, so it applies to
all scalar probability spaces of Assumptions 5.2. -/
theorem global_error_differences (s : Riesz1.RieszExponent)
    (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (_hγₛ : 0 ≤ γₛ) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ε : ℝ), 0 < ε → ∀ (Cₛ : ℝ), 1 ≤ Cₛ →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (_hn : 2 ≤ (n : ℕ)) (_hnm : (n : ℕ) ≤ (m : ℕ))
        (_hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
          (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
        ∃ a B : ℝ, 0 < a ∧ a ≤ 1 ∧ 1 ≤ B ∧ a⁻¹ + B ≤ C * (n : ℝ) ^ (κ * ε) ∧
          ∀ᵐ x ∂ν,
            let E := M x - (2 : ℝ) • rieszMatrix s m hm
            (∀ i j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε) *
              (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)) ∧
            (∀ i j, |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) ∧
            (∀ i j, |(E i j - E (i + 1) j) - (E i (j + 1) - E (i + 1) (j + 1))| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val)) ∧
            (∀ i, ∑ j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            (∀ j, ∑ i, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            a • (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) ≤ M x ∧ ‖E‖ ≤ B := by
  obtain ⟨κ, hκ, hb⟩ := global_error_backward_differences s κₛ γₛ hκₛ _hγₛ M₀
  refine ⟨κ, hκ, ?_⟩
  intro ε hε Cₛ hCₛ
  obtain ⟨C, hC, hb⟩ := hb ε hε Cₛ hCₛ
  let F := (2 : ℝ) ^ (1 + s.val)
  let C' := 2 * F * C
  have hF : 1 ≤ F := Real.one_le_rpow (by norm_num) (by linarith [s.property.1])
  have hCC : C ≤ C' := by
    dsimp [C']
    nlinarith only [hC, hF, mul_nonneg (sub_nonneg.mpr hF) (show 0 ≤ C by linarith only [hC])]
  refine ⟨C', hC.trans hCC, ?_⟩
  intro n m hm hn hnm hmn K hK hKm α _ ν M hM
  obtain ⟨a, B, ha, ha1, hB1, hab, he⟩ := hb n m hm hn hnm hmn hK hKm ν M hM
  let L := (n : ℝ) ^ (κ * ε)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hloss : C * L ≤ C' * L := mul_le_mul_of_nonneg_right hCC hL
  refine ⟨a, B, ha, ha1, hB1, hab.trans hloss, ?_⟩
  filter_upwards [he] with x hx
  let E := M x - (2 : ℝ) • rieszMatrix s m hm
  refine ⟨fun i j => (hx.1 i j).trans (mul_le_mul_of_nonneg_right hloss (by positivity)),
    ?_, ?_, fun i => (hx.2.2.2.1 i).trans hloss,
    fun j => (hx.2.2.2.2.1 j).trans hloss, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2⟩
  · intro i j
    have hi := hx.2.1 (i + 1) j
    have hj := hx.2.1 i (j + 1)
    simp only [add_sub_cancel_right] at hi hj
    have hpi := GlobalReferenceErrorInternal.forward_distance_power m hm i j
      (q := 1 + s.val) (by linarith [s.property.1])
    have hpj := GlobalReferenceErrorInternal.forward_distance_power m hm j i
      (q := 1 + s.val) (by linarith [s.property.1])
    have hdist (u v : Fin (m : ℕ)) : Riesz1.cyclicIndexDistance m u v =
        Riesz1.cyclicIndexDistance m v u := by simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
    rw [hdist (j + 1) i, hdist j i] at hpj
    rw [show -(1 + s.val) = -1 - s.val by ring] at hpi hpj
    have hci := mul_le_mul_of_nonneg_left hpi (show 0 ≤ C * L by positivity)
    have hcj := mul_le_mul_of_nonneg_left hpj (show 0 ≤ C * L by positivity)
    change |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤ _
    rw [abs_sub_comm (E i j) (E (i + 1) j), abs_sub_comm (E i j) (E i (j + 1))]
    have h1 : |E (i + 1) j - E i j| ≤ C * L *
        (F * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) :=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hi.trans hci)
    have h2 : |E i (j + 1) - E i j| ≤ C * L *
        (F * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hj.trans hcj)
    dsimp [C']
    nlinarith only [h1, h2]
  · intro i j
    have hh := hx.2.2.1 (i + 1) (j + 1)
    simp only [add_sub_cancel_right, GlobalReferenceErrorInternal.distance_translate] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hloss
      (show 0 ≤ (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val) by positivity))
    convert hh' using 1
    congr 1
    ring

end Riesz2
