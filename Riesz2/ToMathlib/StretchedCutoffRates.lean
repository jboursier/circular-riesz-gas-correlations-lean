/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MomentEventBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Numerical estimates for a stretched exponential cutoff

Polynomial losses and the square root of a rare-event bound are controlled
uniformly above one real threshold. These statements contain no measure or
model hypotheses.
-/

public section
open Filter
open scoped Topology

namespace Riesz2.StretchedCutoff

/-- Every polynomial times a stretched exponential tends to zero. -/
theorem tendsto_power_mul_exp {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ a * Real.exp (-c * x ^ δ)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / δ) c hc).comp
    (tendsto_rpow_atTop hδ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, ← Real.rpow_mul hx]
  rw [show δ * (a / δ) = a by field_simp]

/-- An upper-tail error and its induced mean displacement are small at every
sufficiently large scale, with the threshold independent of any volume. -/
theorem eventual_small {δ c B : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hB : 0 ≤ B) (h : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x : ℝ, K ≤ x →
      3 * x * Real.exp (-c * x ^ δ) ≤ 1 / 2 ∧
        B * x * Real.sqrt (3 * x * Real.exp (-c * x ^ δ)) ≤ x ^ h / 2 := by
  have ht₁ := (tendsto_power_mul_exp hδ hc 1).const_mul 3
  have ht₂ := (tendsto_power_mul_exp hδ hc (3 - 2 * h)).const_mul (12 * B ^ 2)
  simp only [mul_zero] at ht₁ ht₂
  have he₁ : ∀ᶠ x : ℝ in atTop, 3 * (x ^ (1 : ℝ) * Real.exp (-c * x ^ δ)) < 1 / 2 :=
    ht₁.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have he₂ : ∀ᶠ x : ℝ in atTop,
      (12 * B ^ 2) * (x ^ (3 - 2 * h) * Real.exp (-c * x ^ δ)) < 1 :=
    ht₂.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (he₁.and he₂)
  refine ⟨max K 1, le_max_right _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right K 1).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  obtain ⟨he₁, he₂⟩ := hK x ((le_max_left K 1).trans hx)
  refine ⟨by simpa only [Real.rpow_one, ← mul_assoc] using he₁.le, ?_⟩
  let E := 3 * x * Real.exp (-c * x ^ δ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpow : x ^ (3 - 2 * h) * x ^ (2 * h) = x ^ (3 : ℝ) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hsquare : 4 * (B * x * Real.sqrt E) ^ 2 =
      ((12 * B ^ 2) * (x ^ (3 - 2 * h) * Real.exp (-c * x ^ δ))) * x ^ (2 * h) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hE]
    calc
      _ = 12 * B ^ 2 * x ^ (3 : ℕ) * Real.exp (-c * x ^ δ) := by dsimp [E]; ring
      _ = 12 * B ^ 2 * (x ^ (3 - 2 * h) * x ^ (2 * h)) * Real.exp (-c * x ^ δ) := by
        rw [hpow]
        norm_num
      _ = _ := by ring
  have ht : x ^ (2 * h) = (x ^ h) ^ 2 := by
    rw [← Real.rpow_two (x ^ h), ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right he₂.le (Real.rpow_nonneg hx0.le (2 * h))
  rw [← hsquare, one_mul, ht] at hm
  have hpos : 0 ≤ B * x * Real.sqrt E := by positivity
  have htpos : 0 < x ^ h := Real.rpow_pos_of_pos hx0 h
  change B * x * Real.sqrt E ≤ x ^ h / 2
  nlinarith

/-- Absorb the polynomial error and lower both stretched-exponential rates
to a prescribed smaller positive exponent. -/
theorem sum_bound {δ q r a b : ℝ} (hq : 0 < q) (hqδ : q ≤ δ) (hqr : q ≤ r)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, 1 ≤ x →
      2 * Real.exp (-b * x ^ r) + 3 * x * Real.exp (-a * x ^ δ) ≤
        C * Real.exp (-c * x ^ q) := by
  have hδ : 0 < δ := lt_of_lt_of_le hq hqδ
  obtain ⟨D, hD, hbound⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := a) (c' := a / 2) hδ (by linarith)
  let c := min b (a / 2)
  have hc : 0 < c := lt_min hb (by linarith)
  refine ⟨2 + 3 * D, c, by positivity, hc, ?_⟩
  intro x hx
  have hpower₁ := Real.rpow_le_rpow_of_exponent_le hx hqr
  have hpower₂ := Real.rpow_le_rpow_of_exponent_le hx hqδ
  have hnonneg : 0 ≤ x ^ q := Real.rpow_nonneg (zero_le_one.trans hx) _
  have hfirst : Real.exp (-b * x ^ r) ≤ Real.exp (-c * x ^ q) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left b (a / 2)]
  have hsecond : Real.exp (-(a / 2) * x ^ δ) ≤ Real.exp (-c * x ^ q) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right b (a / 2)]
  have he := hbound x hx
  rw [Real.rpow_one] at he
  have hs := mul_le_mul_of_nonneg_left hsecond hD
  nlinarith

end Riesz2.StretchedCutoff
