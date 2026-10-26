/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PaperCutoffDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cutoff-scale rigidity for the physical core

The short/long interval split in the proof of Lemma 5.4 of the paper.
The floor is retained throughout, including when the forcing scale is small.
-/

@[expose] public section
noncomputable section

namespace Riesz2.PhysicalCore

/-- Lemma 5.4 of the paper: above the powered floor cutoff, the
rigidity denominator dominates the square of half the forcing scale. -/
theorem paper_cutoff_denominator (s : Riesz1.RieszExponent) {q R : ℝ}
    (hq : 2 ≤ q) (hR : (⌊q⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) ≤ R) :
    q ^ 2 / 4 ≤ R ^ (1 - s.val / 2) := by
  let m : ℕ := paperReferenceCutoffExponent s
  let f : ℝ := ⌊q⌋₊
  have hf : 1 ≤ f := by
    dsimp only [f]
    exact_mod_cast (Nat.one_le_floor_iff q).mpr (by linarith)
  have hhalf : q / 2 ≤ f := by
    have hh := Nat.self_sub_floor_lt_one q
    dsimp only [f]
    linarith
  have ha : 0 ≤ 1 - s.val / 2 := by linarith [s.property.2]
  have hm : 2 ≤ (m : ℝ) * (1 - s.val / 2) :=
    (paperReferenceCutoffExponent_large s).le
  have hpow : f ^ 2 ≤ R ^ (1 - s.val / 2) := by
    calc
      f ^ 2 = f ^ (2 : ℝ) := (Real.rpow_two f).symm
      _ ≤ f ^ ((m : ℝ) * (1 - s.val / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hf hm
      _ = (f ^ m) ^ (1 - s.val / 2) := by
        rw [Real.rpow_mul (by linarith : 0 ≤ f), Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by simpa only [f, m, Nat.cast_pow] using hR) ha
  nlinarith [sq_nonneg (f - q / 2)]

/-- Lemma 5.4 of the paper: the above-cutoff relative rigidity error
is at most `4 / q`, hence tends to zero for `q = n^ε`, `ε > 0`. -/
theorem paper_cutoff_relative_error (s : Riesz1.RieszExponent) {q R : ℝ}
    (hq : 2 ≤ q) (hR0 : 0 < R)
    (hR : (⌊q⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) ≤ R) :
    q * R ^ (s.val / 2 - 1) ≤ 4 / q := by
  have hd := paper_cutoff_denominator s hq hR
  have hq0 : 0 < q := by linarith
  have he : R ^ (s.val / 2 - 1) = (R ^ (1 - s.val / 2))⁻¹ := by
    rw [show s.val / 2 - 1 = -(1 - s.val / 2) by ring, Real.rpow_neg hR0.le]
  rw [he, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hR0 _)).mpr
  have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4 / q)
  have heq : (4 / q) * (q ^ 2 / 4) = q := by field_simp
  rw [heq] at hh
  exact hh

/-- Lemma 5.4 of the paper: all lengths above the cutoff satisfy the
Taylor small-displacement condition as soon as `n^ε ≥ 8`. -/
theorem paper_cutoff_taylor_condition (s : Riesz1.RieszExponent) {q R : ℝ}
    (hq : 8 ≤ q) (hR0 : 0 < R)
    (hR : (⌊q⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) ≤ R) :
    q * R ^ (s.val / 2) ≤ R / 2 := by
  have hr := paper_cutoff_relative_error s (by linarith) hR0 hR
  have hhalf : 4 / q ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ (by linarith : 0 < q)).mpr (by linarith)
  have he : R ^ (s.val / 2 - 1) * R = R ^ (s.val / 2) := by
    calc
      _ = R ^ (s.val / 2 - 1) * R ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hR0]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right (hr.trans hhalf) hR0.le
  simpa only [mul_assoc, he, one_div, inv_mul_eq_div] using hh

/-- Lemma 5.4 of the paper: for the bounded forcing scales left out
of the large-size argument, every length at least 256 still admits Taylor.
Only bounded lengths require the crude coefficient bound. -/
theorem paper_cutoff_taylor_or_bounded (s : Riesz1.RieszExponent) {q R : ℝ}
    (_hq : 1 ≤ q) (hR1 : 1 ≤ R)
    (hR : (⌊q⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) ≤ R) :
    q * R ^ (s.val / 2) ≤ R / 2 ∨ R ^ (1 - s.val / 2) ≤ 256 := by
  by_cases hlarge : 8 ≤ q
  · exact Or.inl (paper_cutoff_taylor_condition s hlarge (by linarith) hR)
  by_cases hlength : 256 ≤ R
  · left
    have hp : (16 : ℝ) ≤ R ^ (1 / 2 : ℝ) := by
      have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 256) hlength
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have he : (256 : ℝ) ^ (1 / 2 : ℝ) = 16 := by
        rw [← Real.sqrt_eq_rpow]
        norm_num
      rwa [he] at hh
    have hd : 2 * q ≤ R ^ (1 - s.val / 2) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hR1
        (show (1 / 2 : ℝ) ≤ 1 - s.val / 2 by linarith [s.property.2])
      linarith
    have he : R ^ (1 - s.val / 2) * R ^ (s.val / 2) = R := by
      rw [← Real.rpow_add (by linarith : 0 < R)]
      norm_num
    have hh := mul_le_mul_of_nonneg_right hd
      (Real.rpow_nonneg (by linarith : 0 ≤ R) (s.val / 2))
    rw [he] at hh
    linarith
  · right
    exact (Real.rpow_le_self_of_one_le hR1 (by linarith [s.property.1])).trans
      (le_of_not_ge hlength)

/-- Lemma 5.4 of the paper: below the cutoff the gap mass is bounded
by `n^((m+1)ε)`, and by `n^(1/4)` at the paper's forcing threshold.
This is the numerical step used with the coordinate upper-gap bound. -/
theorem paper_cutoff_short_mass (s : Riesz1.RieszExponent) (n : ℕ+)
    {ε : ℝ} (_hε : 0 ≤ ε) (hεsmall : ε ≤ paperCutoffThreshold s)
    {r : ℕ} (hr : r < ⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ)) :
    (r : ℝ) * (n : ℝ) ^ ε ≤
        (n : ℝ) ^ (((paperReferenceCutoffExponent s : ℝ) + 1) * ε) ∧
    (n : ℝ) ^ (((paperReferenceCutoffExponent s : ℝ) + 1) * ε) ≤
        (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  constructor
  · have hr' : (r : ℝ) ≤ (n : ℝ) ^ ((paperReferenceCutoffExponent s : ℝ) * ε) := by
      calc
        _ ≤ ((⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) : ℝ) := by exact_mod_cast hr.le
        _ = (⌊(n : ℝ) ^ ε⌋₊ : ℝ) ^ (paperReferenceCutoffExponent s : ℕ) := by rw [Nat.cast_pow]
        _ ≤ ((n : ℝ) ^ ε) ^ (paperReferenceCutoffExponent s : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hn0.le ε)) _
        _ = _ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
          congr 1
          ring
    calc
      _ ≤ (n : ℝ) ^ ((paperReferenceCutoffExponent s : ℝ) * ε) * (n : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right hr' (Real.rpow_nonneg hn0.le ε)
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  · apply Real.rpow_le_rpow_of_exponent_le hn1
    have hd : 0 < 4 * ((paperReferenceCutoffExponent s : ℝ) + 1) := by positivity
    change ε ≤ 1 / (4 * ((paperReferenceCutoffExponent s : ℝ) + 1)) at hεsmall
    have hh := (le_div_iff₀ hd).mp hεsmall
    nlinarith

end Riesz2.PhysicalCore
