/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.Moments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic

/-!
# Closed tails and power norms from exponential moments

The companion library supplies the scalar moment estimate. Here it is
converted to extended-valued probabilities and `eLpNorm` bounds with the
constant independent of the norm exponent.
-/

public section

open MeasureTheory

namespace Riesz2.ExponentialPower

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Markov's inequality with a closed threshold and extended-valued
probability. Integrability is explicit, so no totalized integral is used. -/
theorem closed_tail [IsFiniteMeasure μ] {c A : ℝ} (hc : 0 < c)
    {Y : Ω → ℝ} (hi : Integrable (fun x => Real.exp (c * Y x)) μ)
    (hA : (∫ x, Real.exp (c * Y x) ∂μ) ≤ A) (u : ℝ) :
    μ {x | u ≤ Y x} ≤ ENNReal.ofReal (A * Real.exp (-c * u)) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (c * Y x)).le)) hi (Real.exp (c * u))
  have hset : {x | u ≤ Y x} = {x | Real.exp (c * u) ≤ Real.exp (c * Y x)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.exp_le_exp, mul_le_mul_iff_right₀ hc]
  rw [← hset] at hmarkov
  have hh : μ.real {x | u ≤ Y x} ≤ A * Real.exp (-c * u) := by
    rw [show A * Real.exp (-c * u) = A / Real.exp (c * u) by
      rw [neg_mul, Real.exp_neg, div_eq_mul_inv], le_div_iff₀ (Real.exp_pos _)]
    nlinarith
  have he := ENNReal.ofReal_le_ofReal hh
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)] using he

/-- A single exponential moment controls every positive power in every
finite `L^p`, with the same constant for all `p ≥ 1`. -/
theorem power_eLpNorm_le {c A r : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hr : 0 < r)
    {Y : Ω → ℝ} (hY : Measurable Y) (hYn : ∀ x, 0 ≤ Y x)
    (hi : Integrable (fun x => Real.exp (c * Y x)) μ)
    (hint : (∫ x, Real.exp (c * Y x) ∂μ) ≤ A)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => Y x ^ r) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max A 1 * (r / (Real.exp 1 * c)) ^ r * p ^ r) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq : 0 < r * p := mul_pos hr hp0
  have hm := Riesz1.moment_le_of_exp_moment_le hc Y hY hYn hi hint (r * p) hq
  have hL : (∫⁻ x, ‖Y x ^ r‖ₑ ^ p ∂μ) ≤
      ENNReal.ofReal (A * (r * p / Real.exp 1) ^ (r * p) / c ^ (r * p)) := by
    have he (x : Ω) : ‖Y x ^ r‖ₑ ^ p = ENNReal.ofReal (Y x ^ (r * p)) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (hYn x) _),
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hYn x) _) hp0.le,
        ← Real.rpow_mul (hYn x)]
    simp_rw [he]
    rw [← ofReal_integral_eq_lintegral_ofReal hm.1
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hYn x) _))]
    exact ENNReal.ofReal_le_ofReal hm.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top (hY.pow_const r).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  rw [one_div]
  have hb := ENNReal.rpow_le_rpow hL (inv_nonneg.mpr hp0.le)
  refine hb.trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.mpr hp0.le)]
  apply ENNReal.ofReal_le_ofReal
  have hpA : A ^ p⁻¹ ≤ max A 1 := by
    calc A ^ p⁻¹ ≤ (max A 1) ^ p⁻¹ := Real.rpow_le_rpow hA (le_max_left _ _) (by positivity)
      _ ≤ (max A 1) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (le_max_right _ _) ((inv_le_one₀ hp0).mpr hp)
      _ = max A 1 := Real.rpow_one _
  have hqp : r * p * p⁻¹ = r := by field_simp
  rw [Real.div_rpow (by positivity) (Real.rpow_nonneg hc.le _),
    Real.mul_rpow hA (by positivity), ← Real.rpow_mul (by positivity : 0 ≤ r * p / Real.exp 1),
    ← Real.rpow_mul hc.le, hqp]
  have hscale : (r * p / Real.exp 1) ^ r / c ^ r =
      (r / (Real.exp 1 * c)) ^ r * p ^ r := by
    rw [← Real.div_rpow (by positivity) hc.le, ← Real.mul_rpow (by positivity) hp0.le]
    congr 1
    field_simp
  calc A ^ p⁻¹ * (r * p / Real.exp 1) ^ r / c ^ r
      = A ^ p⁻¹ * ((r / (Real.exp 1 * c)) ^ r * p ^ r) := by rw [← hscale]; ring
    _ ≤ max A 1 * ((r / (Real.exp 1 * c)) ^ r * p ^ r) :=
      mul_le_mul_of_nonneg_right hpA (by positivity)
    _ = _ := by ring

end Riesz2.ExponentialPower
