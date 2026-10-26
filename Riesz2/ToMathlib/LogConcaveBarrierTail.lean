/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.LogConcaveResidualSlope

/-!
# Uniform bounds for a log-concave residual density

The manuscript's survival tangent bounds the density at one half. Mean one
bounds residual chords there from below. Concavity then bounds the residual
towards zero. Integrating the density gives the lower tail directly.
-/

public section

open MeasureTheory Set

namespace Riesz2.BarrierTail

/-- The tangent and residual-slope estimates bound the regular factor on `(0, 1/2]`.
The constant precedes the support, density, and barrier coefficient. -/
theorem exists_residual_bound {s A : ℝ} (hs : 0 < s) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {L a : ℝ} {f h : ℝ → ℝ},
      2 ≤ L → 0 ≤ a → a ≤ A → Measurable f →
      (∀ x, 0 ≤ f x) → (∀ x ∈ Ioo (0 : ℝ) L, 0 < f x) →
      (∀ x ∉ Ioo (0 : ℝ) L, f x = 0) →
      ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (f x)) →
      Integrable f → Integrable (fun x => x * f x) →
      (∫ x, f x) = 1 → (∫ x, x * f x) = 1 →
      (∀ x ∈ Ioo (0 : ℝ) L, 0 < h x) →
      (∀ x ∈ Ioo (0 : ℝ) L, f x = Real.exp (-a * x ^ (-s)) * h x) →
      ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (h x)) →
      ∀ u : ℝ, 0 < u → u ≤ 1 / 2 → h u ≤ B := by
  let D := A * s * (1 / 2 : ℝ) ^ (-s - 1) + 2
  let T := A * (1 / 2 : ℝ) ^ (-s) + D / 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2 * Real.exp T, by positivity, ?_⟩
  intro L a f h hL ha haA hfm hfn hp hz hc hfi hxfi hmass hmean hhp hfac hhc u hu hub
  have hb : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) L := ⟨by norm_num, by linarith⟩
  have huL : u ∈ Ioo (0 : ℝ) L := ⟨hu, by linarith⟩
  have hfb := density_half_le_two hL hfm hfn hp hz hc hfi hxfi hmass hmean
  have hhb : h (1 / 2) ≤ 2 * Real.exp (A * (1 / 2 : ℝ) ^ (-s)) := by
    have he : h (1 / 2) = Real.exp (a * (1 / 2 : ℝ) ^ (-s)) * f (1 / 2) := by
      rw [hfac _ hb, ← mul_assoc, ← Real.exp_add]
      simp
    rw [he]
    have hexp := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right haA (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (-s)))
    nlinarith [Real.exp_pos (a * (1 / 2 : ℝ) ^ (-s)), Real.exp_pos (A * (1 / 2 : ℝ) ^ (-s))]
  have hline : Real.log (h u) ≤ Real.log (h (1 / 2)) + D * (1 / 2 - u) := by
    rcases hub.eq_or_lt with he | he
    · rw [he]; simp
    have hq := residual_half_chord_lower hL hs ha hfm hfn hp hz hc hfi hxfi
      hmass hmean hhp hfac hhc u hu he
    have hcoef : -D ≤ -a * s * (1 / 2 : ℝ) ^ (-s - 1) - 2 := by
      have hh := mul_le_mul_of_nonneg_right haA
        (mul_nonneg hs.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (-s - 1)))
      dsimp [D]
      nlinarith
    have hh := (le_div_iff₀ (by linarith : 0 < (1 / 2 : ℝ) - u)).mp (hcoef.trans hq)
    linarith
  calc h u = Real.exp (Real.log (h u)) := (Real.exp_log (hhp u huL)).symm
    _ ≤ Real.exp (Real.log (h (1 / 2)) + D * (1 / 2 - u)) := Real.exp_le_exp.mpr hline
    _ = h (1 / 2) * Real.exp (D * (1 / 2 - u)) := by
      rw [Real.exp_add, Real.exp_log (hhp _ hb)]
    _ ≤ (2 * Real.exp (A * (1 / 2 : ℝ) ^ (-s))) * Real.exp (D / 2) :=
      mul_le_mul hhb (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity)
    _ = 2 * Real.exp T := by rw [mul_assoc, ← Real.exp_add]

/-- Integrating the barrier bound gives the lower tail, without exponential Markov. -/
theorem lower_tail_integral {s a d B L : ℝ} {f h : ℝ → ℝ}
    (hs : 0 < s) (hd : 0 ≤ d) (hda : d ≤ a) (hB : 0 ≤ B)
    (hfn : ∀ x, 0 ≤ f x) (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hfi : Integrable f) (hmass : (∫ x, f x) = 1)
    (hfac : ∀ x ∈ Ioo (0 : ℝ) L, f x = Real.exp (-a * x ^ (-s)) * h x)
    (hh : ∀ x, 0 < x → x ≤ 1 / 2 → h x ≤ B)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫ x in Iic u, f x) ≤
      (B + Real.exp (d * (2 : ℝ) ^ s)) * Real.exp (-d * u ^ (-s)) := by
  by_cases hub : u ≤ 1 / 2
  · have he : (∫ x in Iic u, f x) = ∫ x in Ioc (0 : ℝ) u, f x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
        (fun x hx => hz x (fun hm => hx.2 ⟨hm.1, hx.1⟩))
    rw [he]
    have hi : IntegrableOn (fun _ : ℝ => B * Real.exp (-d * u ^ (-s))) (Ioc 0 u) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hbound (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) u) :
        f x ≤ B * Real.exp (-d * u ^ (-s)) := by
      by_cases hxL : x ∈ Ioo (0 : ℝ) L
      swap
      · rw [hz x hxL]; positivity
      have hhn : 0 ≤ h x := by
        have hn := hfn x
        rw [hfac x hxL] at hn
        exact nonneg_of_mul_nonneg_right hn (Real.exp_pos _)
      have hp := Real.rpow_le_rpow_of_nonpos hx.1 hx.2 (by linarith : -s ≤ 0)
      have hcoef : -a * x ^ (-s) ≤ -d * u ^ (-s) := by
        have he := mul_le_mul hp hda hd (Real.rpow_nonneg hx.1.le (-s))
        linarith
      rw [hfac x hxL, mul_comm]
      exact mul_le_mul (hh x hx.1 (hx.2.trans hub)) (Real.exp_le_exp.mpr hcoef)
        (Real.exp_pos _).le hB
    have hb := setIntegral_mono_on hfi.integrableOn hi measurableSet_Ioc hbound
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hu.le] at hb
    have hb' : u * (B * Real.exp (-d * u ^ (-s))) ≤ B * Real.exp (-d * u ^ (-s)) :=
      mul_le_of_le_one_left (by positivity) hu1
    calc (∫ x in Ioc (0 : ℝ) u, f x) ≤ u * (B * Real.exp (-d * u ^ (-s))) := by
          simpa only [sub_zero] using hb
      _ ≤ B * Real.exp (-d * u ^ (-s)) := hb'
      _ ≤ (B + Real.exp (d * (2 : ℝ) ^ s)) * Real.exp (-d * u ^ (-s)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_pos _).le)
            (Real.exp_pos _).le
  · have hp : u ^ (-s) ≤ (2 : ℝ) ^ s := by
      calc u ^ (-s) ≤ (1 / 2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_not_ge hub) (by linarith)
        _ = (2 : ℝ) ^ s := by
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg, neg_neg]; norm_num
    have he : 1 ≤ Real.exp (d * (2 : ℝ) ^ s) * Real.exp (-d * u ^ (-s)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    have hm := (setIntegral_le_integral hfi (Filter.Eventually.of_forall hfn)
      (s := Iic u)).trans_eq hmass
    nlinarith [mul_nonneg hB (Real.exp_pos (-d * u ^ (-s))).le]

/-- Removing half of a singular barrier leaves a uniformly integrable
inverse exponential. This converts a residual-density bound into both
lower tails and inverse moments without totalized expectations. -/
theorem inverse_exponential_integral {s a d B b : ℝ} {f h : ℝ → ℝ}
    (hs : 0 < s) (hd : 0 ≤ d) (hda : d ≤ a) (hB : 0 ≤ B)
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hzero : ∀ x ∉ Ioo (0 : ℝ) b, f x = 0) (hi : Integrable f)
    (hmass : (∫ x, f x) = 1)
    (hfactor : ∀ x ∈ Ioo (0 : ℝ) b, f x = Real.exp (-a * x ^ (-s)) * h x)
    (hh : ∀ x, 0 < x → x ≤ 1 / 4 → h x ≤ B) :
    Integrable (fun x => Real.exp (d * x ^ (-s)) * f x) ∧
      (∫ x, Real.exp (d * x ^ (-s)) * f x) ≤ B / 4 + Real.exp (d * (4 : ℝ) ^ s) := by
  let J := Icc (0 : ℝ) (1 / 4)
  have hJi : Integrable (J.indicator (fun _ : ℝ => B)) :=
    (integrableOn_const (μ := volume) (C := B) isCompact_Icc.measure_lt_top.ne).integrable_indicator
      measurableSet_Icc
  have hb (x : ℝ) : Real.exp (d * x ^ (-s)) * f x ≤
      J.indicator (fun _ : ℝ => B) x + Real.exp (d * (4 : ℝ) ^ s) * f x := by
    have hj : 0 ≤ J.indicator (fun _ : ℝ => B) x := indicator_nonneg (fun _ _ => hB) x
    have hf : 0 ≤ Real.exp (d * (4 : ℝ) ^ s) * f x := mul_nonneg (Real.exp_pos _).le (hfn x)
    by_cases hx : x ∈ Ioo (0 : ℝ) b
    swap
    · rw [hzero x hx, mul_zero, mul_zero, add_zero]; exact hj
    by_cases hx4 : x ≤ 1 / 4
    · rw [indicator_of_mem (show x ∈ J from ⟨hx.1.le, hx4⟩)]
      conv_lhs => rw [hfactor x hx, ← mul_assoc, ← Real.exp_add]
      have he : Real.exp (d * x ^ (-s) + -a * x ^ (-s)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.rpow_nonneg hx.1.le (-s)])
      have hhn : 0 ≤ h x := by
        have hff := hfn x
        rw [hfactor x hx] at hff
        exact nonneg_of_mul_nonneg_right hff (Real.exp_pos _)
      have hm := mul_le_mul_of_nonneg_right he hhn
      have hhh := hh x hx.1 hx4
      nlinarith
    · have hp : x ^ (-s) ≤ (4 : ℝ) ^ s := by
        calc x ^ (-s) ≤ (1 / 4 : ℝ) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_not_ge hx4) (by linarith)
          _ = (4 : ℝ) ^ s := by
            rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg, neg_neg]; norm_num
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hd)
      exact (mul_le_mul_of_nonneg_right he (hfn x)).trans (le_add_of_nonneg_left hj)
  have hm : Measurable (fun x : ℝ => Real.exp (d * x ^ (-s)) * f x) :=
    ((measurable_id.pow_const (-s)).const_mul d).exp.mul hfm
  have hdom := hJi.add (hi.const_mul (Real.exp (d * (4 : ℝ) ^ s)))
  have hint : Integrable (fun x => Real.exp (d * x ^ (-s)) * f x) := by
    apply hdom.mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hfn x))]
      exact hb x
  refine ⟨hint, ?_⟩
  have hh := integral_mono hint hdom hb
  simp only [Pi.add_apply] at hh
  rw [integral_add hJi (hi.const_mul _), integral_const_mul, hmass,
    integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hh
  linarith

end Riesz2.BarrierTail
