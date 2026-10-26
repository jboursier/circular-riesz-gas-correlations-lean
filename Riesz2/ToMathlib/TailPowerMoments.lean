/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.Moments
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic

/-!
# Power norms by integrating exponential tails

Layer cake gives the Gamman integral for each positive moment. A bound on
Gamma, obtained by maximizing a power times a decaying exponential, then
gives a constant independent of the norm exponent. Applying this to
`X⁻ˢ` with power `r/s` also handles stretched exponential inverse tails.
-/

public section

open MeasureTheory Set

namespace Riesz2.TailPower

/-- The elementary Gamma bound used after integrating the tails. -/
theorem gamma_add_one_le {t : ℝ} (ht : 0 < t) :
    Real.Gamma (t + 1) ≤ 2 * (2 * t / Real.exp 1) ^ t := by
  let K := (2 * t / Real.exp 1) ^ t
  have hpoint (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      Real.exp (-u) * u ^ t ≤ K * Real.exp (-(1 / 2 : ℝ) * u) := by
    have h := Riesz1.rpow_le_div_exp_mul_exp ht (div_nonneg hu.le (by norm_num : (0 : ℝ) ≤ 2))
    rw [Real.div_rpow hu.le (by norm_num : (0 : ℝ) ≤ 2)] at h
    have he : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(1 / 2 : ℝ) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hK : (t / Real.exp 1) ^ t * (2 : ℝ) ^ t = K := by
      rw [← Real.mul_rpow (by positivity) (by norm_num)]
      congr 1; ring
    have hmul := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) t)).mp h)
      (Real.exp_pos (-u)).le
    calc Real.exp (-u) * u ^ t ≤
        ((t / Real.exp 1) ^ t * Real.exp (u / 2) * (2 : ℝ) ^ t) * Real.exp (-u) := by
          nlinarith [hmul]
      _ = K * Real.exp (-(1 / 2 : ℝ) * u) := by rw [← he, ← hK]; ring
  have hi := Real.GammaIntegral_convergent (show 0 < t + 1 by linarith)
  simp only [add_sub_cancel_right] at hi
  have hmajor := (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K
  rw [Real.Gamma_eq_integral (by linarith : 0 < t + 1)]
  simp only [add_sub_cancel_right]
  calc (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ t) ≤
      ∫ u in Ioi (0 : ℝ), K * Real.exp (-(1 / 2 : ℝ) * u) :=
        setIntegral_mono_on hi hmajor measurableSet_Ioi hpoint
    _ = 2 * K := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0]
      simp; ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Enlarge the prefactor of a tail estimate to cover all positive thresholds. -/
theorem extend_tail [IsProbabilityMeasure μ] {Y : Ω → ℝ} {C c : ℝ} (hc : 0 < c)
    (htail : ∀ u : ℝ, 1 ≤ u → μ {x | u ≤ Y x} ≤ ENNReal.ofReal (C * Real.exp (-c * u))) :
    ∀ u : ℝ, 0 < u → μ {x | u ≤ Y x} ≤
      ENNReal.ofReal (max C (Real.exp c) * Real.exp (-c * u)) := by
  intro u _
  by_cases hu : 1 ≤ u
  · exact (htail u hu).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  · have he : 1 ≤ Real.exp c * Real.exp (-c * u) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith [not_le.mp hu]
    exact (prob_le_one).trans (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (he.trans (mul_le_mul_of_nonneg_right
        (le_max_right _ _) (Real.exp_pos _).le)))

/-- Layer cake followed by the Gamman integral. No exponential moment is used. -/
theorem lintegral_rpow_le {Y : Ω → ℝ} {C c q : ℝ}
    (hY : Measurable Y) (hYn : ∀ x, 0 ≤ Y x) (hC : 0 ≤ C) (hc : 0 < c) (hq : 0 < q)
    (htail : ∀ u : ℝ, 0 < u → μ {x | u ≤ Y x} ≤ ENNReal.ofReal (C * Real.exp (-c * u))) :
    (∫⁻ x, ENNReal.ofReal (Y x ^ q) ∂μ) ≤
      ENNReal.ofReal (2 * C * (2 * q / (Real.exp 1 * c)) ^ q) := by
  have hG := Real.integral_rpow_mul_exp_neg_mul_Ioi hq hc
  have hi : IntegrableOn (fun u : ℝ => u ^ (q - 1) * Real.exp (-(c * u))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hG]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hq)).ne'
  have hn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ C * (u ^ (q - 1) * Real.exp (-(c * u))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ (Filter.Eventually.of_forall hYn)
    hY.aemeasurable hq]
  calc ENNReal.ofReal q * (∫⁻ u in Ioi (0 : ℝ),
        μ {x | u ≤ Y x} * ENNReal.ofReal (u ^ (q - 1))) ≤
      ENNReal.ofReal q * ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (C * (u ^ (q - 1) * Real.exp (-(c * u)))) := by
          apply mul_le_mul_right
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          calc μ {x | u ≤ Y x} * ENNReal.ofReal (u ^ (q - 1)) ≤
              ENNReal.ofReal (C * Real.exp (-c * u)) * ENNReal.ofReal (u ^ (q - 1)) :=
                mul_le_mul_left (htail u hu) _
            _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              simp only [neg_mul]
              ring
    _ = ENNReal.ofReal (C * (1 / c) ^ q * Real.Gamma (q + 1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul C) hn,
        integral_const_mul, hG, ← ENNReal.ofReal_mul hq.le, Real.Gamma_add_one hq.ne']
      congr 1; ring
    _ ≤ ENNReal.ofReal (2 * C * (2 * q / (Real.exp 1 * c)) ^ q) := by
      apply ENNReal.ofReal_le_ofReal
      calc C * (1 / c) ^ q * Real.Gamma (q + 1) ≤
          C * (1 / c) ^ q * (2 * (2 * q / Real.exp 1) ^ q) :=
            mul_le_mul_of_nonneg_left (gamma_add_one_le hq) (by positivity)
        _ = _ := by
          have he : (1 / c) ^ q * (2 * q / Real.exp 1) ^ q =
              (2 * q / (Real.exp 1 * c)) ^ q := by
            rw [← Real.mul_rpow (by positivity) (by positivity)]
            congr 1; field_simp
          nlinarith [he]

/-- Integrating an exponential tail bounds every finite power norm, with
the same prefactor for all norm exponents `p ≥ 1`. -/
theorem power_eLpNorm_le {Y : Ω → ℝ} {C c r : ℝ}
    (hY : Measurable Y) (hYn : ∀ x, 0 ≤ Y x) (hC : 0 ≤ C) (hc : 0 < c) (hr : 0 < r)
    (htail : ∀ u : ℝ, 0 < u → μ {x | u ≤ Y x} ≤ ENNReal.ofReal (C * Real.exp (-c * u)))
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => Y x ^ r) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max (2 * C) 1 * (2 * r / (Real.exp 1 * c)) ^ r * p ^ r) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq : 0 < r * p := mul_pos hr hp0
  have hL := lintegral_rpow_le hY hYn hC hc hq htail
  have he (x : Ω) : ‖Y x ^ r‖ₑ ^ p = ENNReal.ofReal (Y x ^ (r * p)) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (hYn x) _),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hYn x) _) hp0.le,
      ← Real.rpow_mul (hYn x)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top (hY.pow_const r).aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  simp_rw [he]
  have hb := ENNReal.rpow_le_rpow hL (show 0 ≤ (1 / p : ℝ) by positivity)
  refine hb.trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpC : (2 * C) ^ (1 / p) ≤ max (2 * C) 1 := by
    calc (2 * C) ^ (1 / p) ≤ (max (2 * C) 1) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) (le_max_left _ _) (by positivity)
      _ ≤ (max (2 * C) 1) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (le_max_right _ _) ((div_le_one hp0).mpr hp)
      _ = max (2 * C) 1 := Real.rpow_one _
  have hqp : r * p * (1 / p) = r := by field_simp
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity : 0 ≤ 2 * (r * p) / (Real.exp 1 * c)), hqp]
  have hscale : (2 * (r * p) / (Real.exp 1 * c)) ^ r =
      (2 * r / (Real.exp 1 * c)) ^ r * p ^ r := by
    rw [← Real.mul_rpow (by positivity) hp0.le]
    congr 1; ring
  rw [hscale]
  exact (mul_le_mul_of_nonneg_right hpC (by positivity)).trans_eq (by ring)

end Riesz2.TailPower
