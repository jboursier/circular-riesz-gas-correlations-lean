/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ExteriorForces
public import Riesz2.ToMathlib.FiniteAbelNorm
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exterior reference forces

The interval expansion used in the proof of Lemma 5.5: a row uses `r`
intervals of length `r`, while a neighboring row difference uses two.
-/

@[expose] public section

noncomputable section

open scoped BigOperators MatrixOrder Fin.NatCast
open Matrix MeasureTheory ProbabilityTheory

namespace Riesz2.ExteriorForces

/-- Power-tail estimate with a positive integer lower endpoint, used for both
interval rows and neighboring row increments in the proof of Lemma 5.5. -/
theorem finite_power_tail {p : ℝ} (hp : 0 < p) {d : ℕ} (hd : 1 ≤ d)
    (S : Finset ℕ) (hS : ∀ r ∈ S, d ≤ r) :
    (∑ r ∈ S, (r : ℝ) ^ (-1 - p)) ≤ (1 + 1 / p) * (d : ℝ) ^ (-p) := by
  let f : ℕ → ℝ := fun r => if d ≤ r then (r : ℝ) ^ (-1 - p) else 0
  let g : ℕ → ℝ := fun k => if (d : ℝ) ≤ 1 + (k : ℝ) then
    (1 + (k : ℝ)) ^ (-(1 + p)) else 0
  have heq (k : ℕ) : f (k + 1) = g k := by
    dsimp [f, g]
    have hc : (d ≤ k + 1) ↔ (d : ℝ) ≤ 1 + (k : ℝ) := by norm_cast; omega
    by_cases h : d ≤ k + 1
    · simp only [h, hc.mp h, ↓reduceIte]
      congr 1 <;> push_cast <;> ring
    · simp only [h, show ¬(d : ℝ) ≤ 1 + (k : ℝ) from fun h' => h (hc.mpr h'), ↓reduceIte]
  have hg0 (k : ℕ) : 0 ≤ g k := by dsimp [g]; split_ifs <;> positivity
  have hgs : Summable g := by
    apply Summable.of_nonneg_of_le hg0 _ (summable_one_add_rpow_neg (by linarith : 1 < 1 + p))
    intro k
    dsimp [g]
    split_ifs
    · exact le_rfl
    · positivity
  have hfs : Summable f := (summable_nat_add_iff 1).mp (by simpa only [heq] using hgs)
  have hsum : (∑' r, f r) = ∑' k, g k := by
    rw [← hfs.sum_add_tsum_nat_add 1]
    simp only [Finset.sum_range_one, f, show ¬d ≤ 0 by omega, ↓reduceIte, zero_add]
    exact tsum_congr heq
  have h := tsum_tail_indicator_le (t := 1 + p) (by linarith)
    (R := (d : ℝ)) (by exact_mod_cast hd)
  have hexp : 1 - (1 + p) = -p := by ring
  have hden : 1 + p - 1 = p := by ring
  rw [hexp, hden] at h
  calc
    (∑ r ∈ S, (r : ℝ) ^ (-1 - p)) = ∑ r ∈ S, f r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [f, hS r hr, ↓reduceIte]
    _ ≤ ∑' r, f r := hfs.sum_le_tsum _ (fun r _ => by dsimp [f]; split_ifs <;> positivity)
    _ = ∑' k, g k := hsum
    _ ≤ _ := h

private theorem same_interval_distance_lt (N : ℕ+) {r : ℕ}
    (hr : 2 * r ≤ (N : ℕ)) (a i j : Fin (N : ℕ))
    (hi : i ∈ cyclicIndexInterval N a r) (hj : j ∈ cyclicIndexInterval N a r) :
    Riesz1.cyclicIndexDistance N i j < r := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b : Fin (N : ℕ) =>
      (if i ∈ cyclicIndexInterval N b r then (1 : ℝ) else 0) *
      (if j ∈ cyclicIndexInterval N b r then (1 : ℝ) else 0))
    (fun b _ => by positivity) (Finset.mem_univ a)
  rw [cyclicIndexInterval_pair_count N hr] at h
  simp only [hi, hj, ↓reduceIte, one_mul] at h
  by_contra hnot
  have hz : r - Riesz1.cyclicIndexDistance N i j = 0 := by omega
  simp only [hz, Nat.cast_zero] at h
  linarith

private theorem exterior_distance_ge_depth (N : ℕ+) {n : ℕ} (_hn : n ≤ (N : ℕ))
    (i j : Fin (N : ℕ)) (hi : i.val < n) (hj : n ≤ j.val) :
    min (i.val + 1) (n - i.val) ≤ Riesz1.cyclicIndexDistance N i j := by
  have hjN := j.isLt
  simp only [Riesz1.cyclicIndexDistance, Nat.dist]
  omega

section IntervalAlgebra

variable {V : Type*} [NormedAddCommGroup V]

private theorem interval_row_eq (N : ℕ+) {r : ℕ} (hr : r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (S : Fin (N : ℕ) → V) :
    (∑ a : Fin (N : ℕ), if i ∈ cyclicIndexInterval N a r then S a else 0) =
      ∑ t ∈ Finset.range r, S (i - (t : Fin (N : ℕ))) := by
  simp_rw [mem_cyclicIndexInterval_iff N _ _ hr]
  have heq : (∑ a : Fin (N : ℕ), if (i - a).val < r then S a else 0) =
      ∑ t : Fin (N : ℕ), if t.val < r then S (i - t) else 0 := by
    apply Fintype.sum_equiv (Equiv.subLeft i)
    intro a
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [heq, ← Finset.sum_filter]
  apply Finset.sum_bij (fun t _ => t.val)
  · intro t ht
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
  · intro t _ u _ h
    exact Fin.ext h
  · intro t ht
    exact ⟨⟨t, lt_of_lt_of_le (Finset.mem_range.mp ht) hr⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ht⟩, rfl⟩
  · intro t _
    simp only [Fin.cast_val_eq_self]

/-- The neighboring row difference in the interval representation retains
exactly two intervals. This avoids taking differences of the truncated kernel. -/
theorem interval_row_increment (N : ℕ+) {r : ℕ} (hr : r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (S : Fin (N : ℕ) → V) :
    (∑ a : Fin (N : ℕ), if i + 1 ∈ cyclicIndexInterval N a r then S a else 0) -
      (∑ a : Fin (N : ℕ), if i ∈ cyclicIndexInterval N a r then S a else 0) =
        S (i + 1) - S (i + 1 - (r : Fin (N : ℕ))) := by
  rw [interval_row_eq N hr, interval_row_eq N hr]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have hshift : i + 1 - ((r : Fin (N : ℕ)) + 1) = i - (r : Fin (N : ℕ)) := by abel
    rw [hshift]
    have h := ih (by omega)
    calc
      _ = ((∑ t ∈ Finset.range r, S (i + 1 - (t : Fin (N : ℕ)))) -
          ∑ t ∈ Finset.range r, S (i - (t : Fin (N : ℕ)))) +
            S (i + 1 - (r : Fin (N : ℕ))) - S (i - (r : Fin (N : ℕ))) := by abel
      _ = _ := by rw [h]; abel

private theorem short_interval_row_zero (N : ℕ+) {n r : ℕ} (hn : n ≤ (N : ℕ))
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ)) (hi : i.val < n)
    (hdepth : r < min (i.val + 1) (n - i.val))
    (z : Fin (N : ℕ) → V) (hz : ∀ j, j.val < n → z j = 0) :
    (∑ a : Fin (N : ℕ), if i ∈ cyclicIndexInterval N a r then
      ∑ j ∈ cyclicIndexInterval N a r, z j else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with hia
  · apply Finset.sum_eq_zero
    intro j hj
    apply hz
    by_contra hjn
    have hdist := same_interval_distance_lt N hr a i j hia hj
    have hlow := exterior_distance_ge_depth N hn i j hi (by omega)
    omega
  · rfl

private theorem interval_row_norm_le (N : ℕ+) {r : ℕ} (hr : r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (S : Fin (N : ℕ) → V) {A : ℝ}
    (hS : ∀ a, ‖S a‖ ≤ A) :
    ‖∑ a : Fin (N : ℕ), if i ∈ cyclicIndexInterval N a r then S a else 0‖ ≤
      (r : ℝ) * A := by
  rw [interval_row_eq N hr]
  calc
    _ ≤ ∑ t ∈ Finset.range r, ‖S (i - (t : Fin (N : ℕ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ Finset.range r, A := Finset.sum_le_sum fun t _ => hS _
    _ = _ := by simp

private theorem interval_increment_norm_le (N : ℕ+) {r : ℕ} (hr : r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (S : Fin (N : ℕ) → V) {A : ℝ}
    (hS : ∀ a, ‖S a‖ ≤ A) :
    ‖(∑ a : Fin (N : ℕ), if i + 1 ∈ cyclicIndexInterval N a r then S a else 0) -
      (∑ a : Fin (N : ℕ), if i ∈ cyclicIndexInterval N a r then S a else 0)‖ ≤ 2 * A := by
  rw [interval_row_increment N hr]
  exact (norm_sub_le _ _).trans (by linarith [hS (i + 1), hS (i + 1 - (r : Fin (N : ℕ)))])

variable [NormedSpace ℝ V]

private theorem interval_force_norm_le (N : ℕ+) {n : ℕ} (hn : n ≤ (N : ℕ))
    (T : Finset ℕ) (hT : ∀ r ∈ T, 1 ≤ r ∧ 2 * r ≤ (N : ℕ))
    (z : Fin (N : ℕ) → V) (hz : ∀ j, j.val < n → z j = 0)
    {t A B : ℝ} (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (c : ℕ → ℝ) (hc : ∀ r ∈ T, |c r| ≤ B * (r : ℝ) ^ (-2 - 2 * t))
    (hS : ∀ r ∈ T, ∀ a, ‖∑ j ∈ cyclicIndexInterval N a r, z j‖ ≤ A * (r : ℝ) ^ t)
    (i : Fin (N : ℕ)) (hi : i.val < n) :
    ‖∑ r ∈ T, c r • ∑ a : Fin (N : ℕ),
      if i ∈ cyclicIndexInterval N a r then ∑ j ∈ cyclicIndexInterval N a r, z j else 0‖ ≤
        A * B * (1 + 1 / t) * (min (i.val + 1) (n - i.val) : ℕ) ^ (-t) := by
  let d := min (i.val + 1) (n - i.val)
  let U := T.filter (fun r => d ≤ r)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hsum : (∑ r ∈ T, c r • ∑ a : Fin (N : ℕ),
      if i ∈ cyclicIndexInterval N a r then ∑ j ∈ cyclicIndexInterval N a r, z j else 0) =
      ∑ r ∈ U, c r • ∑ a : Fin (N : ℕ),
        if i ∈ cyclicIndexInterval N a r then ∑ j ∈ cyclicIndexInterval N a r, z j else 0 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hru
    have hshort : r < d := by simpa only [U, Finset.mem_filter, hr, true_and, not_le] using hru
    rw [short_interval_row_zero N hn (hT r hr).2 i hi hshort z hz, smul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ r ∈ U, ‖c r • ∑ a : Fin (N : ℕ),
        if i ∈ cyclicIndexInterval N a r then ∑ j ∈ cyclicIndexInterval N a r, z j else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ U, A * B * (r : ℝ) ^ (-1 - t) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrT := (Finset.mem_filter.mp hr).1
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (hT r hrT).1
      rw [norm_smul, Real.norm_eq_abs]
      have hb := mul_le_mul (hc r hrT)
        (interval_row_norm_le N (r := r) (by have := (hT r hrT).2; omega) i _ (hS r hrT))
        (norm_nonneg _) (mul_nonneg hB (Real.rpow_nonneg hr0.le _))
      apply hb.trans_eq
      have hp : (r : ℝ) ^ (-2 - 2 * t) * ((r : ℝ) * (r : ℝ) ^ t) =
          (r : ℝ) ^ (-1 - t) := by
        rw [mul_comm (r : ℝ) ((r : ℝ) ^ t), ← Real.rpow_add_one hr0.ne', ← Real.rpow_add hr0]
        congr 1
        ring
      calc
        B * (r : ℝ) ^ (-2 - 2 * t) * ((r : ℝ) * (A * (r : ℝ) ^ t)) =
          A * B * ((r : ℝ) ^ (-2 - 2 * t) * ((r : ℝ) * (r : ℝ) ^ t)) := by ring
        _ = _ := by rw [hp]
    _ = A * B * ∑ r ∈ U, (r : ℝ) ^ (-1 - t) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have htail := finite_power_tail ht hd U (fun r hr => (Finset.mem_filter.mp hr).2)
      have h := mul_le_mul_of_nonneg_left htail (mul_nonneg hA hB)
      simpa only [mul_assoc, d] using h

private theorem interval_force_increment_norm_le (N : ℕ+) {n : ℕ} (hn : n ≤ (N : ℕ))
    (T : Finset ℕ) (hT : ∀ r ∈ T, 1 ≤ r ∧ 2 * r ≤ (N : ℕ))
    (z : Fin (N : ℕ) → V) (hz : ∀ j, j.val < n → z j = 0)
    {t A B : ℝ} (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (c : ℕ → ℝ) (hc : ∀ r ∈ T, |c r| ≤ B * (r : ℝ) ^ (-2 - 2 * t))
    (hS : ∀ r ∈ T, ∀ a, ‖∑ j ∈ cyclicIndexInterval N a r, z j‖ ≤ A * (r : ℝ) ^ t)
    (i : Fin (N : ℕ)) (hi : i.val + 1 < n) :
    ‖(∑ r ∈ T, c r • ∑ a : Fin (N : ℕ),
      if i + 1 ∈ cyclicIndexInterval N a r then ∑ j ∈ cyclicIndexInterval N a r, z j else 0) -
      (∑ r ∈ T, c r • ∑ a : Fin (N : ℕ),
      if i ∈ cyclicIndexInterval N a r then ∑ j ∈ cyclicIndexInterval N a r, z j else 0)‖ ≤
        2 * A * B * (1 + 1 / (1 + t)) *
          (min (i.val + 1) (n - (i.val + 1)) : ℕ) ^ (-1 - t) := by
  let d := min (i.val + 1) (n - (i.val + 1))
  let U := T.filter (fun r => d ≤ r)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hval : (i + 1).val = i.val + 1 := by
    have hN : i.val + 1 < (N : ℕ) := lt_of_lt_of_le hi hn
    change (i.val + 1 % (N : ℕ)) % (N : ℕ) = i.val + 1
    rw [Nat.mod_eq_of_lt (show 1 < (N : ℕ) by omega), Nat.mod_eq_of_lt hN]
  let R := fun r (j : Fin (N : ℕ)) => ∑ a : Fin (N : ℕ),
    if j ∈ cyclicIndexInterval N a r then ∑ k ∈ cyclicIndexInterval N a r, z k else 0
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  change ‖∑ r ∈ T, c r • (R r (i + 1) - R r i)‖ ≤ _
  have hsum : (∑ r ∈ T, c r • (R r (i + 1) - R r i)) =
      ∑ r ∈ U, c r • (R r (i + 1) - R r i) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hru
    have hshort : r < d := by simpa only [U, Finset.mem_filter, hr, true_and, not_le] using hru
    have h0 : R r i = 0 := short_interval_row_zero N hn (hT r hr).2 i (by omega)
      (by dsimp [d] at hshort; omega) z hz
    have h1 : R r (i + 1) = 0 := short_interval_row_zero N hn (hT r hr).2 (i + 1)
      (by rw [hval]; exact hi) (by rw [hval]; dsimp [d] at hshort; omega) z hz
    rw [h0, h1, sub_self, smul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ r ∈ U, ‖c r • (R r (i + 1) - R r i)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ U, 2 * A * B * (r : ℝ) ^ (-1 - (1 + t)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrT := (Finset.mem_filter.mp hr).1
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (hT r hrT).1
      rw [norm_smul, Real.norm_eq_abs]
      have hb := mul_le_mul (hc r hrT)
        (interval_increment_norm_le N (r := r) (by have := (hT r hrT).2; omega) i _ (hS r hrT))
        (norm_nonneg _) (mul_nonneg hB (Real.rpow_nonneg hr0.le _))
      apply hb.trans_eq
      have hp : (r : ℝ) ^ (-2 - 2 * t) * (r : ℝ) ^ t = (r : ℝ) ^ (-1 - (1 + t)) := by
        rw [← Real.rpow_add hr0]
        congr 1
        ring
      change B * (r : ℝ) ^ (-2 - 2 * t) * (2 * (A * (r : ℝ) ^ t)) = _
      calc
        _ = 2 * A * B * ((r : ℝ) ^ (-2 - 2 * t) * (r : ℝ) ^ t) := by ring
        _ = _ := by rw [hp]
    _ = 2 * A * B * ∑ r ∈ U, (r : ℝ) ^ (-1 - (1 + t)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have htail := finite_power_tail (by linarith : 0 < 1 + t) hd U
        (fun r hr => (Finset.mem_filter.mp hr).2)
      have h := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * A * B)
      simpa only [mul_assoc, d, show -(1 + t) = -1 - t by ring] using h

end IntervalAlgebra

private def gaussianLinearFormLp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) :
    (ι → ℝ) →ₗ[ℝ] Lp ℝ 2 (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) where
  toFun v := (MemLp.const_inner (WithLp.toLp 2 v) IsGaussian.memLp_two_id).toLp
    (fun z => inner ℝ (WithLp.toLp 2 v) z)
  map_add' v w := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [] with z
    exact inner_add_left _ _ _
  map_smul' c v := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [] with z
    exact real_inner_smul_left _ _ _

private theorem gaussianLinearFormLp_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (v : ι → ℝ) :
    ‖gaussianLinearFormLp S v‖ ^ 2 = v ⬝ᵥ (S *ᵥ v) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  have hcoe : gaussianLinearFormLp S v =ᵐ[μ] (fun z => inner ℝ x z) :=
    (MemLp.const_inner (WithLp.toLp 2 v)
      (IsGaussian.memLp_two_id (μ := μ))).coeFn_toLp
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ z, inner ℝ (gaussianLinearFormLp S v z) (gaussianLinearFormLp S v z) ∂μ) =
        ∫ z, inner ℝ x z * inner ℝ x z ∂μ := by
      apply integral_congr_ae
      filter_upwards [hcoe] with z hz
      rw [hz]
      simp only [RCLike.inner_apply, conj_trivial]
    _ = covarianceBilin μ x x := by
      rw [covarianceBilin_apply IsGaussian.memLp_two_id]
      simp only [μ, integral_id_multivariateGaussian', sub_zero]
    _ = _ := covarianceBilin_multivariateGaussian hS x x

/-- Membership arithmetic for the crossing-interval split in Lemma 5.5. -/
private theorem interval_membership (N : ℕ+) (a j : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) : j ∈ cyclicIndexInterval N a r ↔
      (a.val ≤ j.val ∧ j.val < a.val + r) ∨ j.val + (N : ℕ) < a.val + r := by
  rw [mem_cyclicIndexInterval_iff N a j hr]
  have ha := a.isLt
  have hj := j.isLt
  rw [Fin.val_sub]
  by_cases h : a.val ≤ j.val
  · rw [Nat.mod_eq_sub_mod (by omega : (N : ℕ) ≤ (N : ℕ) - a.val + j.val),
      Nat.mod_eq_of_lt (by omega : (N : ℕ) - a.val + j.val - (N : ℕ) < (N : ℕ))]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : (N : ℕ) - a.val + j.val < (N : ℕ))]
    omega

/-- Ordinary components represented as cyclic intervals, for Lemma 5.5. -/
private theorem ordinary_interval (N : ℕ+) {l u : ℕ} (hu : u ≤ (N : ℕ))
    (j : Fin (N : ℕ)) :
    j ∈ cyclicIndexInterval N (l : Fin (N : ℕ)) (u - l) ↔ l ≤ j.val ∧ j.val < u := by
  by_cases hl : l < (N : ℕ)
  · rw [interval_membership N _ _ (by omega), Fin.val_natCast, Nat.mod_eq_of_lt hl]
    have hj := j.isLt
    omega
  · have hzero : u - l = 0 := by omega
    simp [hzero, cyclicIndexInterval]
    omega

/-- Crossing intervals in Lemma 5.5 have at most two exterior components. -/
theorem crossing_interval_components (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (a : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ)) :
    ∃ (a₁ a₂ : Fin (N : ℕ)) (r₁ r₂ : ℕ), r₁ ≤ r ∧ r₂ ≤ r ∧
      (∀ j ∈ cyclicIndexInterval N a₁ r₁, n ≤ j.val) ∧
      (∀ j ∈ cyclicIndexInterval N a₂ r₂, n ≤ j.val) ∧
      Disjoint (cyclicIndexInterval N a₁ r₁) (cyclicIndexInterval N a₂ r₂) ∧
      (cyclicIndexInterval N a r).filter (fun j => n ≤ j.val) =
        cyclicIndexInterval N a₁ r₁ ∪ cyclicIndexInterval N a₂ r₂ := by
  let l := max n a.val
  let u := min (N : ℕ) (a.val + r)
  let v := a.val + r - (N : ℕ)
  have hl : l ≤ (N : ℕ) := by dsimp [l]; omega
  have hu : u ≤ (N : ℕ) := by dsimp [u]; omega
  have hv : v ≤ (N : ℕ) := by dsimp [v]; have := a.isLt; omega
  refine ⟨(l : Fin (N : ℕ)), (n : Fin (N : ℕ)), u-l, v-n,
    by dsimp [l,u]; omega, by dsimp [v]; have := a.isLt; omega, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have h := (ordinary_interval N hu j).mp hj
    dsimp [l] at h
    omega
  · intro j hj
    exact ((ordinary_interval N hv j).mp hj).1
  · apply Finset.disjoint_left.mpr
    intro j hj hk
    have h := (ordinary_interval N hu j).mp hj
    have k := (ordinary_interval N hv j).mp hk
    dsimp [l,v] at h k
    have := a.isLt
    omega
  · ext j
    simp only [Finset.mem_filter, Finset.mem_union, interval_membership N a j hr,
      ordinary_interval N hu j, ordinary_interval N hv j]
    dsimp [l,u,v]
    have := j.isLt
    have := a.isLt
    omega

/-- The crossing-interval step of Lemma 5.5 of the paper: split the
exterior trace into at most two intervals, apply `exterior_partial_sums`
to each component, and use the Gaussian L² triangle inequality. -/
private theorem restricted_interval_norm_bound_by_components (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 → ∀ n : ℕ, n ≤ (N : ℕ) →
      ∀ (a : Fin (N : ℕ)) (r : ℕ), 1 ≤ r → r ≤ (N : ℕ) →
      let E := Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val)
      let D := ((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
        (Subtype.val : E → Fin (N : ℕ)) Subtype.val
      ‖gaussianLinearFormLp D⁻¹ (fun i : E => if i.val ∈ cyclicIndexInterval N a r then 1 else 0)‖ ≤
        C * K * (r : ℝ) ^ (s.val / 2) := by
  obtain ⟨C, hC, hb⟩ := exterior_partial_sums hz s
  refine ⟨2 * Real.sqrt C, by positivity, ?_⟩
  intro N hN K hK hKN n hn a r hr hrN
  dsimp only
  let E := Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val)
  let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
    Subtype.val Subtype.val
  let L := gaussianLinearFormLp D⁻¹
  let v (a : Fin (N : ℕ)) (r : ℕ) : E → ℝ :=
    fun i => if i.val ∈ cyclicIndexInterval N a r then 1 else 0
  have hcomponent (b : Fin (N : ℕ)) (t : ℕ) (ht : t ≤ r)
      (hE : ∀ j ∈ cyclicIndexInterval N b t, n ≤ j.val) :
      ‖L (v b t)‖ ≤ Real.sqrt C * K * (r : ℝ) ^ (s.val / 2) := by
    by_cases ht0 : t = 0
    · have hv : v b t = 0 := by
        subst t; funext i; simp [v, cyclicIndexInterval]
      rw [hv, map_zero, norm_zero]
      positivity
    have hsub : cyclicIndexInterval N b t ⊆ E := by
      intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE j hj⟩
    have hvar := (hb N hN K hK hKN E b t (by omega) (ht.trans hrN) hsub).2
    have hg := exterior_gaussian_linearForm s N hN hK hKN E (v b t)
    have hobs : (fun z : EuclideanSpace ℝ E =>
        ∑ i : E, if i.val ∈ cyclicIndexInterval N b t then z i else 0) =
        (fun z => inner ℝ (WithLp.toLp 2 (v b t)) z) := by
      funext z
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, v]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    dsimp only at hvar hg
    rw [hobs, hg.2] at hvar
    have hnorm := gaussianLinearFormLp_norm_sq
      (exteriorBlock_posDef s N hN hK hKN E).2.posSemidef (v b t)
    have hpow : ((r : ℝ) ^ (s.val / 2)) ^ 2 = (r : ℝ) ^ s.val := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg r)]
      congr 1; norm_num
    have hmajor : (t : ℝ) ^ s.val ≤ (r : ℝ) ^ s.val :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast ht) s.property.1.le
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ Real.sqrt C * (K : ℝ) * (r : ℝ) ^ (s.val / 2))).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, hpow]
    exact hnorm.trans_le (hvar.trans (mul_le_mul_of_nonneg_left hmajor (by positivity)))
  obtain ⟨a₁, a₂, r₁, r₂, h₁, h₂, hE₁, hE₂, hd, he⟩ :=
    crossing_interval_components N n hn a r hrN
  have hv : v a r = v a₁ r₁ + v a₂ r₂ := by
    funext i
    have hi : i.val ∈ (cyclicIndexInterval N a r).filter (fun j => n ≤ j.val) ↔
        i.val ∈ cyclicIndexInterval N a r := by simp [Finset.mem_filter, (Finset.mem_filter.mp i.property).2]
    have hm : i.val ∈ cyclicIndexInterval N a r ↔
        i.val ∈ cyclicIndexInterval N a₁ r₁ ∨ i.val ∈ cyclicIndexInterval N a₂ r₂ := by
      rw [← hi, he, Finset.mem_union]
    have hdis := Finset.disjoint_left.mp hd
    dsimp only [v, Pi.add_apply]
    by_cases hleft : i.val ∈ cyclicIndexInterval N a₁ r₁
    · have hright := hdis hleft
      simp only [hleft, hright, hm.mpr (Or.inl hleft), ↓reduceIte, add_zero]
    · by_cases hright : i.val ∈ cyclicIndexInterval N a₂ r₂
      · simp only [hleft, hright, hm.mpr (Or.inr hright), ↓reduceIte, zero_add]
      · have hnot : i.val ∉ cyclicIndexInterval N a r := by simp only [hm, hleft, hright, or_self, not_false_eq_true]
        simp only [hleft, hright, hnot, ↓reduceIte, add_zero]
  change ‖L (v a r)‖ ≤ _
  rw [hv, map_add]
  exact (norm_add_le _ _).trans ((add_le_add (hcomponent a₁ r₁ h₁ hE₁)
    (hcomponent a₂ r₂ h₂ hE₂)).trans_eq (by ring))

private theorem reference_vector_expansion {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ)
    (i : Fin (N : ℕ)) (z : Fin (N : ℕ) → V) :
    (∑ j : Fin (N : ℕ), (2 * referenceIntervalMatrix s N hN K i j) • z j) =
      ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r),
        (2 * ((1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (r : Fin (N : ℕ)))) •
        ∑ a : Fin (N : ℕ), if i ∈ cyclicIndexInterval N a r then
          ∑ j ∈ cyclicIndexInterval N a r, z j else 0 := by
  have hcast (r : ℕ) : (⟨r % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)) =
      (r : Fin (N : ℕ)) := by
    apply Fin.ext
    simp only [Fin.val_natCast]
  unfold referenceIntervalMatrix
  simp only [hcast, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : i ∈ cyclicIndexInterval N a r
  · simp only [hi, ↓reduceIte, mul_one]
    rw [Finset.smul_sum]
    calc
      _ = ∑ j : Fin (N : ℕ), if j ∈ cyclicIndexInterval N a r then
          (2 * ((1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (r : Fin (N : ℕ)))) • z j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp only [mul_one, mul_zero, zero_smul]
      _ = _ := by simp only [Finset.sum_ite_mem, Finset.univ_inter]
  · simp only [hi, ↓reduceIte, mul_zero, zero_mul, zero_smul, smul_zero, Finset.sum_const_zero]

private theorem reference_force_norms (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K n : ℕ), n ≤ (N : ℕ) →
      ∀ (A : ℝ), 0 ≤ A → ∀ z : Fin (N : ℕ) → V,
      (∀ j, j.val < n → z j = 0) →
      (∀ r, 1 ≤ r → 2 * r ≤ (N : ℕ) → ∀ a,
        ‖∑ j ∈ cyclicIndexInterval N a r, z j‖ ≤ A * (r : ℝ) ^ (s.val / 2)) →
      let F := fun i : Fin (N : ℕ) =>
        ∑ j : Fin (N : ℕ), (2 * referenceIntervalMatrix s N hN K i j) • z j
      (∀ i, i.val < n → ‖F i‖ ≤ C * A * (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2)) ∧
      (∀ i, i.val + 1 < n → ‖F (i + 1) - F i‖ ≤
        C * A * (min (i.val + 1) (n - (i.val + 1)) : ℕ) ^ (-1 - s.val / 2)) := by
  obtain ⟨_, B, _, hB, hb⟩ := sampledSecondDifference_bounds s
  let t := s.val / 2
  have ht : 0 < t := by dsimp [t]; linarith [s.property.1]
  let C₀ := 2 * B * (1 + 1 / t)
  let C₁ := 4 * B * (1 + 1 / (1 + t))
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro V _ _ N hN K n hn A hA z hz hS
  let T := (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r)
  let c := fun r : ℕ => 2 * ((1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
    sampledSecondDifference s N hN (r : Fin (N : ℕ)))
  have hT (r : ℕ) (hr : r ∈ T) : 1 ≤ r ∧ 2 * r ≤ (N : ℕ) := by
    have h := Finset.mem_filter.mp hr
    have h' := Finset.mem_range.mp h.1
    omega
  have hc (r : ℕ) (hr : r ∈ T) : |c r| ≤ (2 * B) * (r : ℝ) ^ (-2 - 2 * t) := by
    have hrN : r < (N : ℕ) := by have := hT r hr; omega
    have hne : (r : Fin (N : ℕ)) ≠ 0 := by
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hrN] at h'
      have := hT r hr
      omega
    have hd : Riesz1.cyclicIndexDistance N (r : Fin (N : ℕ)) 0 = r := by
      simp only [Riesz1.cyclicIndexDistance, Fin.val_natCast, Fin.val_zero,
        Nat.mod_eq_of_lt hrN, Nat.dist_zero_right]
      have := hT r hr
      omega
    have ha := (hb N hN _ hne).2
    rw [hd] at ha
    have hpos := (sampledSecondDifference_pos s N hN hne).le
    have hw : 0 ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) ∧
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> constructor <;> norm_num
    have hcoeff : 0 ≤ c r := by
      exact mul_nonneg (by norm_num) (mul_nonneg hw.1 hpos)
    rw [abs_of_nonneg hcoeff]
    have hmul := mul_le_mul_of_nonneg_right hw.2 hpos
    dsimp [c]
    calc
      _ ≤ 2 * sampledSecondDifference s N hN (r : Fin (N : ℕ)) := by linarith
      _ ≤ 2 * (B * (r : ℝ) ^ (-s.val - 2)) := by linarith
      _ = _ := by
        dsimp [t]
        rw [show -2 - 2 * (s.val / 2) = -s.val - 2 by ring]
        ring
  have hS' (r : ℕ) (hr : r ∈ T) := hS r (hT r hr).1 (hT r hr).2
  dsimp only
  constructor
  · intro i hi
    rw [reference_vector_expansion]
    have h := interval_force_norm_le N hn T hT z hz ht hA (by positivity : 0 ≤ 2 * B) c hc hS' i hi
    rw [show A * (2 * B) * (1 + 1 / t) = C₀ * A by dsimp [C₀]; ring,
      show -t = -s.val / 2 by dsimp [t]; ring] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁.le) hA
  · intro i hi
    rw [reference_vector_expansion, reference_vector_expansion]
    have h := interval_force_increment_norm_le N hn T hT z hz ht hA (by positivity : 0 ≤ 2 * B) c hc hS' i hi
    rw [show 2 * A * (2 * B) * (1 + 1 / (1 + t)) = C₁ * A by dsimp [C₁]; ring] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le) hA

private theorem depth_telescoping {V : Type} [NormedAddCommGroup V]
    (N : ℕ+) {n : ℕ} (_hn : n ≤ (N : ℕ)) (f : Fin (N : ℕ) → V)
    {M p : ℝ} (hM : 0 ≤ M) (hp : 0 ≤ p)
    (hf : ∀ i : Fin (N : ℕ), i.val + 1 < n →
      ‖f (i + 1) - f i‖ ≤ M * (min (i.val + 1) (n - (i.val + 1)) : ℕ) ^ (-p))
    (j l : Fin (N : ℕ)) (hj : j.val < n) (hl : l.val < n) :
    ‖f j - f l‖ ≤ M * (Nat.dist j.val l.val : ℝ) *
      (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^ (-p) := by
  have hordered (j l : Fin (N : ℕ)) (hj : j.val < n) (hl : l.val < n)
      (hjl : j.val ≤ l.val) :
      ‖f j - f l‖ ≤ M * (Nat.dist j.val l.val : ℝ) *
        (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^ (-p) := by
    let d := min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val))
    have hd : 1 ≤ d := by dsimp [d]; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hstep (k : ℕ) (hjk : j.val ≤ k) (hkl : k < l.val) :
        ‖f ((k : Fin (N : ℕ)) + 1) - f (k : Fin (N : ℕ))‖ ≤ M * (d : ℝ) ^ (-p) := by
      have hkN : k < (N : ℕ) := by omega
      have hki : (k : Fin (N : ℕ)).val = k := by simp only [Fin.val_natCast, Nat.mod_eq_of_lt hkN]
      have h := hf (k : Fin (N : ℕ)) (by rw [hki]; omega)
      rw [hki] at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ hM
      apply Real.rpow_le_rpow_of_nonpos hdR _ (neg_nonpos.mpr hp)
      exact_mod_cast (show d ≤ min (k + 1) (n - (k + 1)) by dsimp [d]; omega)
    have htel (q : ℕ) (hq : j.val + q ≤ l.val) :
        ‖f ((j.val + q : ℕ) : Fin (N : ℕ)) - f j‖ ≤ (q : ℝ) * (M * (d : ℝ) ^ (-p)) := by
      induction q with
      | zero => simp only [Nat.add_zero, Fin.cast_val_eq_self, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
      | succ q ih =>
        have hq' : j.val + q ≤ l.val := by omega
        have hnext : ((j.val + (q + 1) : ℕ) : Fin (N : ℕ)) =
            ((j.val + q : ℕ) : Fin (N : ℕ)) + 1 := by push_cast; abel
        rw [hnext]
        have htri := dist_triangle (f (((j.val + q : ℕ) : Fin (N : ℕ)) + 1))
          (f ((j.val + q : ℕ) : Fin (N : ℕ))) (f j)
        simp only [dist_eq_norm] at htri
        have h := hstep (j.val + q) (by omega) (by omega)
        have hprev := ih hq'
        simp only [Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self] at htri h hprev ⊢
        nlinarith only [htri, h, hprev]
    have h := htel (l.val - j.val) (by omega)
    rw [Nat.add_sub_of_le hjl, Fin.cast_val_eq_self, norm_sub_rev] at h
    have hdif : Nat.dist j.val l.val = l.val - j.val := Nat.dist_eq_sub_of_le hjl
    rw [hdif]
    convert h using 1
    ring
  rcases le_total j.val l.val with h | h
  · exact hordered j l hj hl h
  · have hb := hordered l j hl hj h
    simpa only [norm_sub_rev (f l) (f j), Nat.dist_comm l.val j.val, min_comm
      (min (l.val + 1) (n - l.val)) (min (j.val + 1) (n - j.val))] using hb

private theorem gaussian_sum_memLp_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (v : ι → ℝ) :
    let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S
    MemLp (fun z : EuclideanSpace ℝ ι => ∑ a, v a * z a) 2 μ ∧
      ‖gaussianLinearFormLp S v‖ =
        (eLpNorm (fun z : EuclideanSpace ℝ ι => ∑ a, v a * z a) 2 μ).toReal := by
  have heq : (fun z : EuclideanSpace ℝ ι => ∑ a, v a * z a) =
      (fun z => inner ℝ (WithLp.toLp 2 v) z) := by
    funext z
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  dsimp only
  rw [heq]
  exact ⟨MemLp.const_inner _ IsGaussian.memLp_two_id,
    Lp.norm_toLp _ (MemLp.const_inner _ IsGaussian.memLp_two_id)⟩

private theorem linear_interval_sum {V : Type} [AddCommGroup V] [Module ℝ V]
    {ι : Type} [Fintype ι] [DecidableEq ι] (E : Finset ι)
    (L : (E → ℝ) →ₗ[ℝ] V) (J : Finset ι) :
    (∑ j ∈ J, L (fun a : E => if a.val = j then 1 else 0)) =
      L (fun a : E => if a.val ∈ J then 1 else 0) := by
  rw [← map_sum]
  congr 1
  funext a
  simp [eq_comm]

private theorem linear_reference_row {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ)
    (E : Finset (Fin (N : ℕ))) (L : (E → ℝ) →ₗ[ℝ] V) (i : Fin (N : ℕ)) :
    (∑ j : Fin (N : ℕ), (2 * referenceIntervalMatrix s N hN K i j) •
      L (fun a : E => if a.val = j then 1 else 0)) =
        L (fun a : E => 2 * referenceIntervalMatrix s N hN K i a.val) := by
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  funext a
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, eq_comm]

/-- See the proof of Lemma 5.5 in the paper: exterior force L² bounds and every active
increment, with a constant depending only on `s`. The force is the off-diagonal
block of twice the reference matrix applied to its centered
exterior Gaussian. Membership in L² is included for every displayed norm.
The result includes the empty exterior and all admissible cutoffs. The crossing
interval step follows Lemma 5.5 of the paper by its two exterior components. -/
theorem exterior_force_bounds (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 → ∀ n : ℕ, n ≤ (N : ℕ) →
      let E := Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val)
      let D := ((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
        (Subtype.val : E → Fin (N : ℕ)) (Subtype.val : E → Fin (N : ℕ))
      let μ := multivariateGaussian (0 : EuclideanSpace ℝ E) D⁻¹
      let F := fun (i : Fin (N : ℕ)) (z : EuclideanSpace ℝ E) =>
        ∑ a : E, (2 * referenceIntervalMatrix s N hN K i a.val) * z a
      (∀ i : Fin (N : ℕ), i.val < n → MemLp (F i) 2 μ ∧
        (eLpNorm (F i) 2 μ).toReal ≤ C * K *
          (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2)) ∧
      (∀ j l : Fin (N : ℕ), j.val < n → l.val < n →
        MemLp (F j - F l) 2 μ ∧
        (eLpNorm (F j - F l) 2 μ).toReal ≤ C * K * (Nat.dist j.val l.val : ℝ) *
          (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^
            (-1 - s.val / 2)) := by
  obtain ⟨A, hA, hinterval⟩ := restricted_interval_norm_bound_by_components hz s
  obtain ⟨B, hB, hforce⟩ := reference_force_norms s
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro N hN K hK hKN n hn
  dsimp only
  let E := Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val)
  let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
    Subtype.val Subtype.val
  let L := gaussianLinearFormLp D⁻¹
  let z := fun j : Fin (N : ℕ) => L (fun a : E => if a.val = j then 1 else 0)
  let v := fun (i : Fin (N : ℕ)) (a : E) => 2 * referenceIntervalMatrix s N hN K i a.val
  have hz0 (j : Fin (N : ℕ)) (hj : j.val < n) : z j = 0 := by
    have hv : (fun a : E => if a.val = j then (1 : ℝ) else 0) = 0 := by
      funext a
      have hE : n ≤ a.val.val := (Finset.mem_filter.mp a.property).2
      have hne : a.val ≠ j := by intro h; rw [h] at hE; omega
      simp only [hne, ↓reduceIte, Pi.zero_apply]
    dsimp only [z]
    rw [hv, map_zero]
  have hsum (r : ℕ) (a : Fin (N : ℕ)) :
      (∑ j ∈ cyclicIndexInterval N a r, z j) =
        L (fun i : E => if i.val ∈ cyclicIndexInterval N a r then 1 else 0) :=
    linear_interval_sum E L _
  have hS (r : ℕ) (hr : 1 ≤ r) (hrN : 2 * r ≤ (N : ℕ)) (a : Fin (N : ℕ)) :
      ‖∑ j ∈ cyclicIndexInterval N a r, z j‖ ≤ (A * K) * (r : ℝ) ^ (s.val / 2) := by
    rw [hsum]
    exact hinterval N hN K hK hKN n hn a r hr (by omega)
  have h := hforce N hN K n hn (A * K) (by positivity) z hz0 hS
  dsimp only at h
  have hrow (i : Fin (N : ℕ)) :
      (∑ j : Fin (N : ℕ), (2 * referenceIntervalMatrix s N hN K i j) • z j) = L (v i) :=
    linear_reference_row s N hN K E L i
  simp_rw [hrow] at h
  have hmem (i : Fin (N : ℕ)) := gaussian_sum_memLp_norm D⁻¹ (v i)
  constructor
  · intro i hi
    refine ⟨(hmem i).1, ?_⟩
    rw [← (hmem i).2]
    simpa only [mul_assoc] using h.1 i hi
  · intro j l hj hl
    have hobs : ((fun x : EuclideanSpace ℝ E => ∑ a, v j a * x a) -
        (fun x : EuclideanSpace ℝ E => ∑ a, v l a * x a)) =
        (fun x : EuclideanSpace ℝ E => ∑ a, (v j - v l) a * x a) := by
      funext x
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have hm := gaussian_sum_memLp_norm D⁻¹ (v j - v l)
    refine ⟨(hmem j).1.sub (hmem l).1, ?_⟩
    change (eLpNorm ((fun x : EuclideanSpace ℝ E => ∑ a, v j a * x a) -
        (fun x : EuclideanSpace ℝ E => ∑ a, v l a * x a)) 2 _).toReal ≤ _
    rw [hobs, ← hm.2, map_sub]
    have hpair := depth_telescoping N hn (fun i => L (v i))
      (M := B * (A * K)) (p := 1 + s.val / 2) (by positivity)
      (by linarith [s.property.1]) (by
        intro i hi
        rw [show -(1 + s.val / 2) = -1 - s.val / 2 by ring]
        exact h.2 i hi) j l hj hl
    rw [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] at hpair
    simpa only [mul_assoc] using hpair

end Riesz2.ExteriorForces
