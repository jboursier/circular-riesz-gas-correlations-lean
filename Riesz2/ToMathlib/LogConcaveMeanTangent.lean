/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.ExpMoment
public import Mathlib.Tactic

/-!
# The mean and a tangent to log survival

The survival tangent at an interior point bounds a log-concave density there.
These are the fixed-point estimates used in the written one-gap tail proof.
-/

public section

open MeasureTheory Set

namespace Riesz2.BarrierTail

/-- Layer cake for a nonnegative density of mean one. -/
theorem survival_integral {L : ℝ} {f : ℝ → ℝ}
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hfi : Integrable f) (hxfi : Integrable (fun x => x * f x))
    (hmean : (∫ x, x * f x) = 1) :
    (∫ t in Ici (0 : ℝ), ∫ x in Ici t, f x) = 1 := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hid : Integrable (fun x : ℝ => x) ν := by
    rw [integrable_withDensity_iff hfm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hfn _)] using hxfi
  have hnn : 0 ≤ᵐ[ν] (fun x : ℝ => x) := by
    refine (ae_withDensity_iff hfm.ennreal_ofReal).mpr ?_
    exact Filter.Eventually.of_forall fun x hx => by
      by_cases hm : x ∈ Ioo (0 : ℝ) L
      · exact hm.1.le
      · exact False.elim (hx (by rw [hz x hm, ENNReal.ofReal_zero]))
  have he := hid.integral_eq_integral_meas_le hnn
  have htail (t : ℝ) : ν.real {x : ℝ | t ≤ x} = ∫ x in Ici t, f x := by
    change (volume.withDensity (fun x => ENNReal.ofReal (f x)) (Ici t)).toReal = _
    rw [withDensity_apply _ measurableSet_Ici,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
        (Filter.Eventually.of_forall hfn), ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ici (fun x _ => hfn x)
  simp only [htail] at he
  rw [integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at he
  simp only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul, mul_comm] at he
  rw [integral_Ici_eq_integral_Ioi]
  exact he.symm.trans hmean

/-- Integrating a translated exponential bound for survival controls the mean. -/
theorem mean_le_of_survival_bound {L b k : ℝ} {f : ℝ → ℝ}
    (hb : 0 ≤ b) (hk : 0 < k)
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hfi : Integrable f) (hxfi : Integrable (fun x => x * f x))
    (hmass : (∫ x, f x) = 1) (hmean : (∫ x, x * f x) = 1)
    (htail : ∀ t : ℝ, 0 ≤ t → (∫ x in Ici (b + t), f x) ≤
      Real.exp (-k * t) * (∫ x in Ici b, f x)) :
    1 ≤ b + (∫ x in Ici b, f x) / k := by
  let S := fun t => ∫ x in Ici t, f x
  have hSint : (∫ t in Ici (0 : ℝ), S t) = 1 :=
    survival_integral hfm hfn hz hfi hxfi hmean
  have hSi : IntegrableOn S (Ici 0) := Integrable.of_integral_ne_zero (by rw [hSint]; norm_num)
  have hsplit := intervalIntegral.integral_Ici_sub_Ici hSi hb
  rw [hSint] at hsplit
  have hpre : (∫ t in Ico (0 : ℝ) b, S t) ≤ b := by
    have hh := setIntegral_mono_on (hSi.mono_set (s := Ico 0 b) Ico_subset_Ici_self)
      (integrableOn_const (μ := volume) (C := (1 : ℝ))
        (by exact measure_Ico_lt_top.ne)) measurableSet_Ico
      (fun t _ => (setIntegral_le_integral hfi (Filter.Eventually.of_forall hfn)).trans_eq hmass)
    simpa [Real.volume_real_Ico_of_le hb] using hh
  have hpost : (∫ t in Ici b, S t) ≤ S b / k := by
    rw [Riesz1.logConcave_setIntegral_Ici_translate]
    have hi : IntegrableOn (fun t : ℝ => Real.exp (-k * t) * S b) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact (exp_neg_integrableOn_Ioi 0 hk).mul_const _
    have hiS : IntegrableOn (fun t => S (b + t)) (Ici 0) := by
      have hiSb := hSi.mono_set (Ici_subset_Ici.mpr hb)
      have he : Integrable ((Ici b).indicator S) := hiSb.integrable_indicator measurableSet_Ici
      have hh := he.comp_add_left b
      have heq : (fun t => (Ici b).indicator S (b + t)) =
          (Ici (0 : ℝ)).indicator (fun t => S (b + t)) := by
        funext t
        simp only [indicator_apply, mem_Ici, le_add_iff_nonneg_right]
      rw [heq] at hh
      exact (integrable_indicator_iff measurableSet_Ici).mp hh
    have hh := setIntegral_mono_on hiS hi measurableSet_Ici (fun t ht => htail t ht)
    refine hh.trans_eq ?_
    rw [integral_mul_const, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (by linarith : -k < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  change 1 - (∫ t in Ici b, S t) = _ at hsplit
  linarith

/-- The tangent to log survival is an exponential upper bound to its right. -/
theorem survival_tangent {L b : ℝ} {f : ℝ → ℝ}
    (hb : b ∈ Ioo (0 : ℝ) L) (hfi : Integrable f)
    (hp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (f x)))
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in Ici (b + t), f x) ≤
      Real.exp (-(f b / (∫ x in Ici b, f x)) * t) * (∫ x in Ici b, f x) := by
  let S := fun t => ∫ x in Ici t, f x
  have hSb : 0 < S b := Riesz1.logConcave_survival_pos hfi hp hz hb.1.le hb.2
  by_cases hL : b + t < L
  swap
  · have he : S (b + t) = 0 := setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      hz x (fun h => by linarith [show b + t ≤ x from hx, h.2, le_of_not_gt hL])
    change S (b + t) ≤ _
    rw [he]
    positivity
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp
  have hSt : 0 < S (b + t) := Riesz1.logConcave_survival_pos hfi hp hz (by linarith [hb.1]) hL
  have hlog := Riesz1.logConcave_concaveOn_log_survival hfi hp hz hc
  have hd := Riesz1.logConcave_hasDerivAt_log_survival hfi hp hz
    (Riesz1.logConcave_continuousOn hp hc) hb
  have hh := hlog.slope_le_of_hasDerivAt (⟨hb.1.le, hb.2⟩ : b ∈ Ico 0 L)
    (⟨by linarith [hb.1], hL⟩ : b + t ∈ Ico 0 L) (by linarith) hd
  rw [slope_def_field] at hh
  simp only [add_sub_cancel_left] at hh
  have hline : Real.log (S (b + t)) ≤ Real.log (S b) - f b / S b * t := by
    have he := (div_le_iff₀ ht).mp hh
    change Real.log (S (b + t)) - Real.log (S b) ≤ (-f b / S b) * t at he
    rw [neg_div] at he
    linarith
  calc (∫ x in Ici (b + t), f x) = Real.exp (Real.log (S (b + t))) :=
        (Real.exp_log hSt).symm
    _ ≤ Real.exp (Real.log (S b) - f b / S b * t) := Real.exp_le_exp.mpr hline
    _ = Real.exp (-(f b / S b) * t) * S b := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hSb]
      rw [neg_mul, mul_comm]

/-- The survival tangent and mean one give the manuscript's `f(1/2) ≤ 2`. -/
theorem density_half_le_two {L : ℝ} {f : ℝ → ℝ} (hL : 2 ≤ L)
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) L) (fun x => Real.log (f x)))
    (hfi : Integrable f) (hxfi : Integrable (fun x => x * f x))
    (hmass : (∫ x, f x) = 1) (hmean : (∫ x, x * f x) = 1) :
    f (1 / 2) ≤ 2 := by
  have hb : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) L := ⟨by norm_num, by linarith⟩
  let S := ∫ x in Ici (1 / 2 : ℝ), f x
  have hS : 0 < S := Riesz1.logConcave_survival_pos hfi hp hz (by norm_num) hb.2
  have hS1 : S ≤ 1 := (setIntegral_le_integral hfi (Filter.Eventually.of_forall hfn)).trans_eq hmass
  have hfb := hp _ hb
  have hm := mean_le_of_survival_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (div_pos hfb hS) hfm hfn hz hfi hxfi hmass hmean (survival_tangent hb hfi hp hz hc)
  change 1 ≤ 1 / 2 + S / (f (1 / 2) / S) at hm
  have he : S / (f (1 / 2) / S) = S ^ 2 / f (1 / 2) := by field_simp
  rw [he] at hm
  have hh : (1 / 2 : ℝ) * f (1 / 2) ≤ S ^ 2 :=
    (le_div_iff₀ hfb).mp (by linarith)
  nlinarith

/-- Positive density below the fixed point makes its survival strictly less than one. -/
theorem survival_half_lt_one {L : ℝ} {f : ℝ → ℝ} (hL : 2 ≤ L)
    (hp : ∀ x ∈ Ioo (0 : ℝ) L, 0 < f x)
    (hz : ∀ x ∉ Ioo (0 : ℝ) L, f x = 0)
    (hfi : Integrable f) (hmass : (∫ x, f x) = 1) :
    (∫ x in Ici (1 / 2 : ℝ), f x) < 1 := by
  have he := intervalIntegral.integral_Ici_sub_Ici' (a := (0 : ℝ)) (b := 1 / 2)
    hfi.integrableOn hfi.integrableOn
  rw [Riesz1.logConcave_survival_zero hmass hz] at he
  have hpint : 0 < ∫ x in (0 : ℝ)..(1 / 2 : ℝ), f x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hfi.intervalIntegrable
      (fun x hx => hp x ⟨hx.1, by linarith [hx.2]⟩) (by norm_num)
  linarith

end Riesz2.BarrierTail
