/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.LogConcaveMeanTangent
public import Riesz1.ToMathlib.LogConcave.NegativePower

/-!
# The residual slope at one half

A residual chord ending at one half cannot be too negative: its supporting
bound to the right would force survival to decay faster than mean one permits.
This is the chord-slope form of the manuscript's left-derivative argument.
-/

public section

open MeasureTheory Set

namespace Riesz2.BarrierTail

/-- A density ratio at the base point propagates to a survival ratio by log concavity. -/
theorem survival_shift_of_density_shift {L b k : ℝ} {f : ℝ → ℝ}
    (hb : b ∈ Ioo (0 : ℝ) L) (hfi : Integrable f)
    (hp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (f x)))
    (hshift : ∀ t : ℝ, 0 ≤ t → f (b + t) ≤ Real.exp (-k * t) * f b)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in Ici (b + t), f x) ≤ Real.exp (-k * t) * (∫ x in Ici b, f x) := by
  rw [Riesz1.logConcave_setIntegral_Ici_translate f (b + t),
    Riesz1.logConcave_setIntegral_Ici_translate f b, ← integral_const_mul]
  refine setIntegral_mono_on (hfi.comp_add_left (b + t)).integrableOn
    ((hfi.comp_add_left b).const_mul _).integrableOn measurableSet_Ici ?_
  intro y hy
  have hh := Riesz1.logConcave_shift_le hp hz hc hb.1
    (show b ≤ b + y by linarith [show 0 ≤ y from hy]) ht
  have hn := Riesz1.logConcave_nonneg hp hz (b + y)
  have hh' := mul_le_mul_of_nonneg_right (hshift t ht) hn
  have he : f (b + t + y) * f b ≤ (Real.exp (-k * t) * f (b + y)) * f b := by
    rw [show b + t + y = b + y + t by ring]
    nlinarith [hh, hh']
  exact (mul_le_mul_iff_left₀ (hp b hb)).mp he

/-- A too-negative residual chord gives the density shift used in the mean contradiction. -/
theorem density_shift_of_residual_chord {L a s u : ℝ} {f h : ℝ → ℝ}
    (hL : 2 ≤ L) (hs : 0 < s) (ha : 0 ≤ a) (hu : 0 < u) (hub : u < 1 / 2)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hhp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < h x)
    (hfac : ∀ x ∈ Ioo (0 : ℝ) L, f x = Real.exp (-a * x ^ (-s)) * h x)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (h x)))
    (hq : (Real.log (h (1 / 2)) - Real.log (h u)) / (1 / 2 - u) ≤
      -a * s * (1 / 2 : ℝ) ^ (-s - 1) - 2)
    (t : ℝ) (ht : 0 ≤ t) :
    f (1 / 2 + t) ≤ Real.exp (-2 * t) * f (1 / 2) := by
  have hb : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) L := ⟨by norm_num, by linarith⟩
  have hfb : 0 < f (1 / 2) := by rw [hfac _ hb]; exact mul_pos (Real.exp_pos _) (hhp _ hb)
  by_cases htL : 1 / 2 + t < L
  swap
  · rw [hz _ (fun hx => htL hx.2)]
    positivity
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp
  have htb : (1 / 2 : ℝ) + t ∈ Ioo (0 : ℝ) L := ⟨by linarith, htL⟩
  have hg := hc.slope_anti_adjacent (⟨hu, by linarith⟩ : u ∈ Ioo (0 : ℝ) L)
    htb hub (by linarith : (1 / 2 : ℝ) < 1 / 2 + t)
  simp only [add_sub_cancel_left] at hg
  have hgline := (div_le_iff₀ ht).mp (hg.trans hq)
  have hp := (Riesz1.convexOn_rpow_neg_Ioi hs).le_slope_of_hasDerivAt
    (show (1 / 2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + t ∈ Ioi (0 : ℝ) by change 0 < (1 / 2 : ℝ) + t; linarith)
    (by linarith : (1 / 2 : ℝ) < 1 / 2 + t)
    (Real.hasDerivAt_rpow_const (p := -s) (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0)))
  rw [slope_def_field] at hp
  simp only [add_sub_cancel_left] at hp
  have hpline := (le_div_iff₀ ht).mp hp
  have hbarrier := mul_le_mul_of_nonpos_left hpline (neg_nonpos.mpr ha)
  have hlogfac (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) L) :
      Real.log (f x) = -a * x ^ (-s) + Real.log (h x) := by
    rw [hfac x hx, Real.log_mul (Real.exp_ne_zero _) (hhp x hx).ne', Real.log_exp]
  have hlog : Real.log (f (1 / 2 + t)) ≤ Real.log (f (1 / 2)) - 2 * t := by
    rw [hlogfac _ htb, hlogfac _ hb]
    nlinarith [hgline, hbarrier]
  have hft : 0 < f (1 / 2 + t) := by
    rw [hfac _ htb]; exact mul_pos (Real.exp_pos _) (hhp _ htb)
  calc f (1 / 2 + t) = Real.exp (Real.log (f (1 / 2 + t))) := (Real.exp_log hft).symm
    _ ≤ Real.exp (Real.log (f (1 / 2)) - 2 * t) := Real.exp_le_exp.mpr hlog
    _ = Real.exp (-2 * t) * f (1 / 2) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hfb]
      rw [neg_mul, mul_comm]

/-- Mean one rules out every residual chord below the manuscript's left-slope bound. -/
theorem residual_half_chord_lower {L a s : ℝ} {f h : ℝ → ℝ}
    (hL : 2 ≤ L) (hs : 0 < s) (ha : 0 ≤ a)
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (f x)))
    (hfi : Integrable f) (hxfi : Integrable (fun x => x * f x))
    (hmass : (∫ x, f x) = 1) (hmean : (∫ x, x * f x) = 1)
    (hhp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < h x)
    (hfac : ∀ x ∈ Ioo (0 : ℝ) L, f x = Real.exp (-a * x ^ (-s)) * h x)
    (hhc : ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (h x)))
    (u : ℝ) (hu : 0 < u) (hub : u < 1 / 2) :
    -a * s * (1 / 2 : ℝ) ^ (-s - 1) - 2 ≤
      (Real.log (h (1 / 2)) - Real.log (h u)) / (1 / 2 - u) := by
  by_contra! hq
  have hb : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) L := ⟨by norm_num, by linarith⟩
  have hshift := density_shift_of_residual_chord hL hs ha hu hub hz hhp hfac hhc hq.le
  have hsurv := survival_shift_of_density_shift hb hfi hp hz hc hshift
  have hm := mean_le_of_survival_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) < 2) hfm hfn hz hfi hxfi hmass hmean hsurv
  have hS := survival_half_lt_one hL hp hz hfi hmass
  linarith

end Riesz2.BarrierTail
