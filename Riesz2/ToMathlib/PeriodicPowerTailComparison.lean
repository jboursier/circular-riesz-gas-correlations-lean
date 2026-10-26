/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.PeriodicPowerBounds
public import Riesz2.ToMathlib.PowerTailBounds

/-!
# Comparison of positive image sums at different periods

Subtracting the common principal image leaves a tail of order the
period to the negative power. This supplies the different-period term
in the coefficient comparison of the proof of Lemma 5.4.
-/

public section
noncomputable section

open scoped BigOperators

namespace Riesz2.PeriodicPower

/-- The nonprincipal images of a point in the first half-period have
a bound uniform in its distance from zero. The constant depends only
on the power, and both sums are proved summable before subtraction. -/
theorem principal_image_error {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N x : ℝ}, 2 ≤ N → 0 < x → 2 * x ≤ N →
      Summable (fun k : ℤ => |x + k * N| ^ (-p)) ∧
      0 ≤ (∑' k : ℤ, |x + k * N| ^ (-p)) - x ^ (-p) ∧
      (∑' k : ℤ, |x + k * N| ^ (-p)) - x ^ (-p) ≤ C * N ^ (-p) := by
  let S := ∑' k : ℤ, |(k : ℝ)| ^ (-p)
  have hS : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _
  let C := 1 + (1 / 2 : ℝ) ^ (-p) * S
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun {N x} hN hx hhalf => ?_⟩
  classical
  have hN0 : 0 < N := by linarith
  have hf := (summable_and_le hp hx le_rfl (by linarith : x ≤ N - x)).1
  let g : ℤ → ℝ := fun k => if k = 0 then 0 else |x + k * N| ^ (-p)
  let B := (1 / 2 : ℝ) ^ (-p) * N ^ (-p)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hmajor := (Real.summable_abs_int_rpow hp).mul_left B
  have hle (k : ℤ) : g k ≤ B * |(k : ℝ)| ^ (-p) := by
    by_cases hk : k = 0
    · simp only [g, hk, ↓reduceIte]
      positivity
    · have hk0 : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hk)
      have hd := half_mul_le_abs_add hN (by rwa [abs_of_pos hx]) hk1
      have hd' : |(k : ℝ)| * ((1 / 2 : ℝ) * N) ≤ |x + k * N| := by
        nlinarith only [hd]
      have hr := Real.rpow_le_rpow_of_nonpos (by positivity :
        (0 : ℝ) < |(k : ℝ)| * ((1 / 2 : ℝ) * N)) hd' (by linarith : -p ≤ 0)
      simp only [g, hk, ↓reduceIte]
      apply hr.trans_eq
      rw [Real.mul_rpow (abs_nonneg _) (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hN0.le]
      dsimp only [B]
      ring
  have hg : Summable g := Summable.of_nonneg_of_le
    (fun k => by dsimp only [g]; split_ifs <;> positivity) hle hmajor
  have he : (∑' k : ℤ, |x + k * N| ^ (-p)) - x ^ (-p) = ∑' k, g k := by
    rw [hf.tsum_eq_add_tsum_ite 0]
    simp only [Int.cast_zero, zero_mul, add_zero, abs_of_pos hx, add_sub_cancel_left, g]
  refine ⟨hf, he.symm ▸ tsum_nonneg (fun k => by dsimp only [g]; split_ifs <;> positivity), ?_⟩
  rw [he]
  calc
    ∑' k, g k ≤ ∑' k : ℤ, B * |(k : ℝ)| ^ (-p) := hg.tsum_le_tsum hle hmajor
    _ = B * S := tsum_mul_left
    _ ≤ C * N ^ (-p) := by
      dsimp only [B, C]
      nlinarith only [Real.rpow_nonneg hN0.le (-p)]

/-- A change to a larger period changes the image sum by at most a
constant times the smaller period to the negative power. -/
theorem different_period_error {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N M x : ℝ}, 2 ≤ M → M ≤ N → 0 < x → 2 * x ≤ M →
      |(∑' k : ℤ, |x + k * N| ^ (-p)) -
        (∑' k : ℤ, |x + k * M| ^ (-p))| ≤ C * M ^ (-p) := by
  obtain ⟨C, hC, hb⟩ := principal_image_error hp
  refine ⟨2 * C, by positivity, fun {N M x} hM hMN hx hhalf => ?_⟩
  have h₁ := hb (hM.trans hMN) hx (hhalf.trans hMN)
  have h₂ := hb hM hx hhalf
  have hpow : N ^ (-p) ≤ M ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hMN (by linarith)
  have hbound := mul_le_mul_of_nonneg_left hpow hC.le
  rw [abs_le]
  constructor <;> linarith only [h₁.2.1, h₁.2.2, h₂.2.1, h₂.2.2, hbound]

end Riesz2.PeriodicPower
