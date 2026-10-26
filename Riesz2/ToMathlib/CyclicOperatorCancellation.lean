/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalSums

/-!
# Cancellation estimates for finite cyclic operator sums

The row mass is retained exactly. These estimates apply to operators on
any real normed space, including the value and half-generator kernels of
the scalar reference inverse.
-/

@[expose] public section
noncomputable section

open Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.CyclicOperatorCancellation

/-- The short and long parts of a power kernel against a translation modulus.
The radius is positive and the shell weight is at least one, including at zero. -/
theorem power_modulus_sum (N : ℕ+) (a b R : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1 + a) (hR : 1 ≤ R) :
    (∑ h : Fin (N : ℕ), weightRadius N h 0 ^ (-(1 + a)) *
      min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / R) ^ b)) ≤
      (2 / (b - a) + 2 * (1 + 1 / a)) * R ^ (-a) := by
  have hRp : 0 < R := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hr0 (h : Fin (N : ℕ)) : 0 ≤ weightRadius N h 0 := (zero_le_one.trans (one_le_weightRadius N h 0))
  let S := univ.filter (fun h : Fin (N : ℕ) => weightRadius N h 0 ≤ R)
  let q := fun h : Fin (N : ℕ) => weightRadius N h 0 ^ (-(1 + a)) *
    min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / R) ^ b)
  have hshort : ∑ h ∈ S, q h ≤ (2 / (b - a)) * R ^ (-a) := by
    calc
      _ ≤ ∑ h ∈ S, weightRadius N h 0 ^ (-(1 + a - b)) * R ^ (-b) := by
        apply sum_le_sum
        intro h _
        have hr : 0 < weightRadius N h 0 := lt_of_lt_of_le zero_lt_one (one_le_weightRadius N h 0)
        have hd : (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ weightRadius N h 0 := by
          dsimp only [weightRadius]; linarith
        calc
          q h ≤ weightRadius N h 0 ^ (-(1 + a)) *
              ((weightRadius N h 0 / R) ^ b) :=
            mul_le_mul_of_nonneg_left ((min_le_right _ _).trans
              (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hd hRp.le) hb0)) (by positivity)
          _ = _ := by
            rw [Real.div_rpow hr.le hRp.le, div_eq_mul_inv, ← Real.rpow_neg hRp.le,
              ← mul_assoc, ← Real.rpow_add hr]
            congr 2
            ring
      _ = (∑ h ∈ S, weightRadius N h 0 ^ (-(1 + a - b))) * R ^ (-b) := by rw [sum_mul]
      _ ≤ (2 / (b - a) * R ^ (b - a)) * R ^ (-b) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        convert sum_weightRadius_le_of_lt_one N 0
          (t := 1 + a - b) (by linarith) (by linarith) hR using 1
        all_goals congr 2 <;> ring
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hRp, show b - a + -b = -a by ring]
  have hlong : ∑ h ∈ Sᶜ, q h ≤ (2 * (1 + 1 / a)) * R ^ (-a) := by
    calc
      _ ≤ ∑ h ∈ Sᶜ, weightRadius N h 0 ^ (-(1 + a)) :=
        sum_le_sum fun h _ => mul_le_of_le_one_right (Real.rpow_nonneg (hr0 h) _) (min_le_left _ _)
      _ ≤ ∑ h ∈ univ.filter (fun h => R ≤ weightRadius N h 0),
          weightRadius N h 0 ^ (-(1 + a)) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro h hh
          simp only [mem_compl, S, mem_filter, mem_univ, true_and, not_le] at hh
          exact mem_filter.mpr ⟨mem_univ _, hh.le⟩
        · intro h _ _; exact Real.rpow_nonneg (hr0 h) _
      _ ≤ _ := by
        convert sum_weightRadius_tail_le N 0 (t := 1 + a) (by linarith) hR using 1
        all_goals congr 2 <;> ring
  have he : (∑ h, q h) = (∑ h ∈ S, q h) + ∑ h ∈ Sᶜ, q h :=
    (sum_add_sum_compl S q).symm
  change (∑ h, q h) ≤ _
  rw [he]
  nlinarith only [hshort, hlong]

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Subtracting the source leaves the exact operator row mass. -/
theorem cancellation_identity (N : ℕ+) (K : Fin (N : ℕ) → E →L[ℝ] E)
    (f : Fin (N : ℕ) → E) (i : Fin (N : ℕ)) :
    (∑ h, K h (f (i + h))) = (∑ h, K h) (f i) +
      ∑ h, K h (f (i + h) - f i) := by
  simp only [_root_.sum_apply, map_sub, sum_sub_distrib]
  abel

/-- Counting-measure mass of a cyclic operator sum with cancellation.
This internal estimate takes kernel and source bounds explicitly. -/
theorem mass_le_internal (N : ℕ+) (K : Fin (N : ℕ) → E →L[ℝ] E)
    (f : Fin (N : ℕ) → E) (A B M a b R : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hab : a < b) (hb : b < 1 + a)
    (hR : 1 ≤ R)
    (hK : ∀ h, ‖K h‖ ≤ B * weightRadius N h 0 ^ (-(1 + a)))
    (hM : ‖∑ h, K h‖ ≤ M)
    (hf : (∑ i, ‖f i‖) ≤ A)
    (hmod : ∀ h, (∑ i, ‖f (i + h) - f i‖) ≤
      A * min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / R) ^ b)) :
    (∑ i, ‖∑ h, K h (f (i + h))‖) ≤
      A * (M + B * (2 / (b - a) + 2 * (1 + 1 / a)) * R ^ (-a)) := by
  have hr0 (h : Fin (N : ℕ)) : 0 ≤ weightRadius N h 0 := (zero_le_one.trans (one_le_weightRadius N h 0))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hp (i : Fin (N : ℕ)) : ‖∑ h, K h (f (i + h))‖ ≤
      M * ‖f i‖ + ∑ h, ‖K h‖ * ‖f (i + h) - f i‖ := by
    rw [cancellation_identity]
    exact (norm_add_le _ _).trans (add_le_add
      (((∑ h, K h).le_opNorm _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _)))
      ((norm_sum_le _ _).trans (sum_le_sum fun h _ => (K h).le_opNorm _)))
  have hs := power_modulus_sum N a b R ha hab hb hR
  calc
    _ ≤ ∑ i, (M * ‖f i‖ + ∑ h, ‖K h‖ * ‖f (i + h) - f i‖) := sum_le_sum fun i _ => hp i
    _ = M * (∑ i, ‖f i‖) + ∑ h, ‖K h‖ * (∑ i, ‖f (i + h) - f i‖) := by
      rw [sum_add_distrib, ← mul_sum, sum_comm]
      simp_rw [mul_sum]
    _ ≤ M * A + ∑ h, (B * weightRadius N h 0 ^ (-(1 + a))) *
        (A * min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / R) ^ b)) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hf hM0)
      apply sum_le_sum
      intro h _
      exact mul_le_mul (hK h) (hmod h) (by positivity) (mul_nonneg hB (Real.rpow_nonneg (hr0 h) _))
    _ = M * A + B * A * ∑ h, weightRadius N h 0 ^ (-(1 + a)) *
        min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / R) ^ b) := by
      simp_rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro h _
      ring
    _ ≤ M * A + B * A * ((2 / (b - a) + 2 * (1 + 1 / a)) * R ^ (-a)) := by
      gcongr
    _ = _ := by ring

/-- A central component estimate from a local Lipschitz bound and the
global source mass. The long translations use mass rather than a pointwise
bound on the source near its boundary. -/
theorem pointwise_le_internal (N : ℕ+) (K : Fin (N : ℕ) → E →L[ℝ] E)
    (f : Fin (N : ℕ) → E) (i : Fin (N : ℕ)) (A B M c R : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hc1 : c < 1) (hR : 16 ≤ R)
    (hK : ∀ h, ‖K h‖ ≤ B * weightRadius N h 0 ^ (-(1 + c)))
    (hM : ‖∑ h, K h‖ ≤ M)
    (hf : (∑ j, ‖f j‖) ≤ A) (hi : ‖f i‖ ≤ A * R ^ (-1 : ℝ))
    (hlocal : ∀ h, (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ R / 32 →
      ‖f (i + h) - f i‖ ≤ A * (Riesz1.cyclicIndexDistance N h 0 : ℝ) * R ^ (-2 : ℝ)) :
    ‖∑ h, K h (f (i + h))‖ ≤ M * A * R ^ (-1 : ℝ) +
      B * A * (2 / (1 - c) + 32 ^ (1 + c) +
        2 * (1 + 1 / c) * 32 ^ c) * R ^ (-1 - c) := by
  have hRp : 0 < R := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hr (h : Fin (N : ℕ)) : 0 < weightRadius N h 0 :=
    zero_lt_one.trans_le (one_le_weightRadius N h 0)
  let S := univ.filter (fun h : Fin (N : ℕ) =>
    (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ R / 32)
  have hshort : (∑ h ∈ S, ‖K h‖ * ‖f (i + h) - f i‖) ≤
      B * A * (2 / (1 - c)) * R ^ (-1 - c) := by
    have hsum : (∑ h ∈ S, weightRadius N h 0 ^ (-c)) ≤
        2 / (1 - c) * R ^ (1 - c) := by
      apply le_trans _ (sum_weightRadius_le_of_lt_one N 0 hc hc1 (by linarith : 1 ≤ R))
      apply sum_le_sum_of_subset_of_nonneg
      · intro h hh
        have hd := (mem_filter.mp hh).2
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        dsimp only [weightRadius]
        linarith
      · intro h _ _; exact Real.rpow_nonneg (hr h).le _
    calc
      _ ≤ ∑ h ∈ S, (B * A * R ^ (-2 : ℝ)) * weightRadius N h 0 ^ (-c) := by
        apply sum_le_sum
        intro h hh
        have hd := (mem_filter.mp hh).2
        have hdr : (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ weightRadius N h 0 := by
          dsimp only [weightRadius]; linarith
        calc
          _ ≤ (B * weightRadius N h 0 ^ (-(1 + c))) *
              (A * weightRadius N h 0 * R ^ (-2 : ℝ)) :=
            mul_le_mul (hK h) ((hlocal h hd).trans (by gcongr))
              (norm_nonneg _) (mul_nonneg hB (Real.rpow_nonneg (hr h).le _))
          _ = _ := by
            have he : weightRadius N h 0 ^ (-(1 + c)) * weightRadius N h 0 =
                weightRadius N h 0 ^ (-c) := by
              rw [← Real.rpow_add_one (hr h).ne']
              congr 1
              ring
            calc
              _ = (B * A * R ^ (-2 : ℝ)) *
                  (weightRadius N h 0 ^ (-(1 + c)) * weightRadius N h 0) := by ring
              _ = _ := by rw [he]
      _ = (B * A * R ^ (-2 : ℝ)) * ∑ h ∈ S, weightRadius N h 0 ^ (-c) := by rw [mul_sum]
      _ ≤ (B * A * R ^ (-2 : ℝ)) * (2 / (1 - c) * R ^ (1 - c)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
        calc
          _ = (B * A * (2 / (1 - c))) * (R ^ (-2 : ℝ) * R ^ (1 - c)) := by ring
          _ = _ := by rw [← Real.rpow_add hRp]; congr 2; ring
  have hlong : (∑ h ∈ Sᶜ, ‖K h‖ * ‖f (i + h) - f i‖) ≤
      B * A * (32 ^ (1 + c) + 2 * (1 + 1 / c) * 32 ^ c) * R ^ (-1 - c) := by
    have hfar (h : Fin (N : ℕ)) (hh : h ∈ Sᶜ) : R / 32 ≤ weightRadius N h 0 := by
      simp only [mem_compl, S, mem_filter, mem_univ, true_and, not_le] at hh
      dsimp only [weightRadius]
      linarith
    have hpoint (h : Fin (N : ℕ)) (hh : h ∈ Sᶜ) :
        weightRadius N h 0 ^ (-(1 + c)) ≤ 32 ^ (1 + c) * R ^ (-1 - c) := by
      have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R / 32) (hfar h hh)
        (by linarith : -(1 + c) ≤ 0)
      convert hh using 1
      rw [Real.div_rpow hRp.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 32)]
      ring_nf
    have htail : (∑ h ∈ Sᶜ, weightRadius N h 0 ^ (-(1 + c))) ≤
        (2 * (1 + 1 / c) * 32 ^ c) * R ^ (-c) := by
      have hs : Sᶜ ⊆ univ.filter (fun h : Fin (N : ℕ) => 1 + R / 32 ≤ weightRadius N h 0) := by
        intro h hh
        simp only [mem_compl, S, mem_filter, mem_univ, true_and, not_le] at hh
        exact mem_filter.mpr ⟨mem_univ _, by dsimp only [weightRadius]; linarith⟩
      calc
        _ ≤ ∑ h ∈ univ.filter (fun h : Fin (N : ℕ) => 1 + R / 32 ≤ weightRadius N h 0),
            weightRadius N h 0 ^ (-(1 + c)) :=
          sum_le_sum_of_subset_of_nonneg hs (fun h _ _ => Real.rpow_nonneg (hr h).le _)
        _ ≤ (2 * (1 + 1 / c)) * (1 + R / 32) ^ (-c) := by
          convert sum_weightRadius_tail_le N 0 (t := 1 + c) (R := 1 + R / 32)
            (by linarith) (by linarith) using 1
          all_goals congr 2 <;> ring
        _ ≤ (2 * (1 + 1 / c)) * (R / 32) ^ (-c) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        _ = _ := by
          rw [Real.div_rpow hRp.le (by norm_num : (0 : ℝ) ≤ 32)]
          simp only [div_eq_mul_inv]
          rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 32), neg_neg]
          ring
    have hfmass : (∑ h ∈ Sᶜ, ‖f (i + h)‖) ≤ A := by
      apply le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun h _ _ => norm_nonneg _))
      exact (show (∑ h, ‖f (i + h)‖) = ∑ j, ‖f j‖ from
        Fintype.sum_equiv (Equiv.addRight i) _ _ (fun h => by simp [add_comm])).le.trans hf
    calc
      _ ≤ ∑ h ∈ Sᶜ, ((B * 32 ^ (1 + c) * R ^ (-1 - c)) * ‖f (i + h)‖ +
          B * weightRadius N h 0 ^ (-(1 + c)) * ‖f i‖) := by
        apply sum_le_sum
        intro h hh
        calc
          _ ≤ (B * weightRadius N h 0 ^ (-(1 + c))) * (‖f (i + h)‖ + ‖f i‖) :=
            mul_le_mul (hK h) (norm_sub_le _ _) (norm_nonneg _) (mul_nonneg hB (Real.rpow_nonneg (hr h).le _))
          _ ≤ _ := by
            have hv := mul_le_mul_of_nonneg_left (hpoint h hh) hB
            nlinarith only [mul_le_mul_of_nonneg_right hv (norm_nonneg (f (i + h)))]
      _ = (B * 32 ^ (1 + c) * R ^ (-1 - c)) * (∑ h ∈ Sᶜ, ‖f (i + h)‖) +
          B * (∑ h ∈ Sᶜ, weightRadius N h 0 ^ (-(1 + c))) * ‖f i‖ := by
        rw [sum_add_distrib, ← mul_sum, ← sum_mul, ← mul_sum]
      _ ≤ (B * 32 ^ (1 + c) * R ^ (-1 - c)) * A +
          B * ((2 * (1 + 1 / c) * 32 ^ c) * R ^ (-c)) * (A * R ^ (-1 : ℝ)) := by
        gcongr
      _ = _ := by
        have he : R ^ (-c) * R ^ (-1 : ℝ) = R ^ (-1 - c) := by
          rw [← Real.rpow_add hRp]; congr 1; ring
        calc
          _ = (B * A * 32 ^ (1 + c)) * R ^ (-1 - c) +
              (B * A * (2 * (1 + 1 / c) * 32 ^ c)) * (R ^ (-c) * R ^ (-1 : ℝ)) := by ring
          _ = _ := by rw [he]; ring
  rw [cancellation_identity]
  calc
    _ ≤ ‖(∑ h, K h) (f i)‖ + ∑ h, ‖K h‖ * ‖f (i + h) - f i‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        ((norm_sum_le _ _).trans (sum_le_sum fun h _ => (K h).le_opNorm _)))
    _ ≤ M * (A * R ^ (-1 : ℝ)) +
        ((∑ h ∈ S, ‖K h‖ * ‖f (i + h) - f i‖) + ∑ h ∈ Sᶜ, ‖K h‖ * ‖f (i + h) - f i‖) := by
      rw [sum_add_sum_compl]
      exact add_le_add (((∑ h, K h).le_opNorm _).trans
        (mul_le_mul hM hi (norm_nonneg _) hM0)) le_rfl
    _ ≤ _ := by linarith only [hshort, hlong]

end Operators

/-- Adjacent differences control an interval difference in any normed
additive group. Only edges between the two specified labels are used. -/
theorem interval_difference_le_internal {E : Type*} [NormedAddCommGroup E]
    (n : ℕ+) (f : Fin (n : ℕ) → E) (i j : Fin (n : ℕ)) (L : ℝ)
    (hstep : ∀ (k : ℕ) (_hk₁ : min i.val j.val ≤ k) (hk₂ : k < max i.val j.val),
      ‖f ⟨k + 1, by have := i.isLt; have := j.isLt; omega⟩ -
        f ⟨k, by have := i.isLt; have := j.isLt; omega⟩‖ ≤ L) :
    ‖f i - f j‖ ≤ L * (Nat.dist i.val j.val : ℝ) := by
  have hordered (a b : Fin (n : ℕ)) (hab : a.val ≤ b.val)
      (he : ∀ (k : ℕ) (hk₁ : a.val ≤ k) (hk₂ : k < b.val),
        ‖f ⟨k + 1, by have := b.isLt; omega⟩ - f ⟨k, by have := b.isLt; omega⟩‖ ≤ L) :
      ‖f a - f b‖ ≤ L * (b.val - a.val : ℕ) := by
    have hs := dist_le_Ico_sum_dist (fun k : ℕ => f (k : Fin (n : ℕ))) hab
    have hsum : (∑ k ∈ Ico a.val b.val, dist (f (k : Fin (n : ℕ)))
        (f ((k + 1 : ℕ) : Fin (n : ℕ)))) ≤ (b.val - a.val : ℕ) * L := by
      calc
        _ ≤ ∑ k ∈ Ico a.val b.val, L := by
          apply sum_le_sum
          intro k hk
          obtain ⟨hk₁, hk₂⟩ := mem_Ico.mp hk
          have heq (t : ℕ) (ht : t < (n : ℕ)) : (t : Fin (n : ℕ)) = ⟨t, ht⟩ := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt ht
          rw [heq k (by omega), heq (k + 1) (by omega), dist_eq_norm, norm_sub_rev]
          exact he k hk₁ hk₂
        _ = _ := by simp
    have ha : (a.val : Fin (n : ℕ)) = a := by simp
    have hb : (b.val : Fin (n : ℕ)) = b := by simp
    rw [ha, hb, dist_eq_norm] at hs
    exact hs.trans (hsum.trans_eq (mul_comm _ _))
  rcases le_total i.val j.val with hij | hji
  · simpa only [Nat.dist_eq_sub_of_le hij] using
      hordered i j hij (fun k hk₁ hk₂ => hstep k (by omega) (by omega))
  · rw [norm_sub_rev, Nat.dist_comm]
    simpa only [Nat.dist_eq_sub_of_le hji] using
      hordered j i hji (fun k hk₁ hk₂ => hstep k (by omega) (by omega))

end Riesz2.CyclicOperatorCancellation
