/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.IntervalVarianceScaling
public import Riesz2.Bridges.RieszNormalization
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.ToMathlib.VarianceThreeTerm
public import Riesz1.Kernel.SeminormScaling
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic

/-!
# Finite interval normalization

Normalization bridges for the proof of Corollary 1.1. Real profiles are supplied to the
existing `Riesz1.lineVariance` as complex L² classes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal NNReal

namespace Riesz2

/-- The real unit-interval profile in the proof of Corollary 1.1. -/
def unitIntervalIndicator (x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x

lemma unitIntervalIndicator_complex_eq :
    (fun x : ℝ => (unitIntervalIndicator x : ℂ)) =
      (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;> simp [unitIntervalIndicator, hx]

lemma integrable_unitIntervalIndicator :
    Integrable (fun x : ℝ => (unitIntervalIndicator x : ℂ)) := by
  rw [unitIntervalIndicator_complex_eq, integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by simp)

lemma memLp_unitIntervalIndicator :
    MemLp (fun x : ℝ => (unitIntervalIndicator x : ℂ)) 2 volume := by
  rw [unitIntervalIndicator_complex_eq]
  exact memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet _ (Or.inr (by simp))

/-- The unit interval as a complex L² class, for the literal `Riesz1.lineVariance`. -/
def unitIntervalL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  memLp_unitIntervalIndicator.toLp _

/-- Right translation preserves the modulus of the line Fourier transform. -/
lemma norm_fourier_translate (f : ℝ → ℂ) (a u : ℝ) :
    ‖𝓕 (fun x => f (x + a)) u‖ = ‖𝓕 f u‖ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) f a) u
  change ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (fun x => f (x + a)) u‖ =
    ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f u‖
  simpa only [Function.comp_def, Circle.norm_smul] using congrArg norm h

/-- The unit indicator is a dilation and translation of the half-length profile. -/
lemma unitIntervalIndicator_eq_rescale (x : ℝ) :
    (unitIntervalIndicator x : ℂ) = (intervalIndicator ((x - 1 / 2) / 2) : ℂ) := by
  have h : x ∈ Set.Ioc (0 : ℝ) 1 ↔ (x - 1 / 2) / 2 ∈ Set.Ioc (-(1 / 4 : ℝ)) (1 / 4) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [unitIntervalIndicator, intervalIndicator, Set.indicator_apply, h]

/-- Dilation of the unweighted Fourier integral. Translation contributes a unit phase. -/
lemma unitInterval_fourier_lintegral (s : Riesz1.RieszExponent) :
    (∫⁻ u : ℝ, ENNReal.ofReal (|u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2)) =
    ENNReal.ofReal ((2 : ℝ) ^ s.val) *
      ∫⁻ u : ℝ, ENNReal.ofReal (|u| ^ (1 - s.val) *
        ‖𝓕 (fun x : ℝ => (intervalIndicator x : ℂ)) u‖ ^ 2) := by
  have hf : Continuous (𝓕 (fun x : ℝ => (intervalIndicator x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ integrable_intervalIndicator
  have h := Riesz1.lintegral_line_seminorm_rescale (by linarith [s.property.1] : 1 - s.val < 2)
    hf (show (0 : ℝ) < 2 by norm_num)
  rw [show 1 - (1 - s.val) = s.val by ring] at h
  rw [← h]
  apply lintegral_congr
  intro u
  have heq : (fun x : ℝ => (unitIntervalIndicator x : ℂ)) =
      fun x => (intervalIndicator ((x + (-(1 / 2 : ℝ))) / 2) : ℂ) := by
    funext x
    simpa only [sub_eq_add_neg] using unitIntervalIndicator_eq_rescale x
  rw [heq, norm_fourier_translate (fun x => (intervalIndicator (x / 2) : ℂ))]

/-- See Subsection 6.4 of the paper: the pointwise Fourier formula agrees with the existing L² variance. -/
lemma lineVariance_eq_fourier_lintegral (β : InverseTemperature) (s : Riesz1.RieszExponent)
    {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    Riesz1.lineVariance (longParameters β s) (hf2.toLp f) =
      ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val) /
        (2 * β.val * Riesz1.rieszConstant s)) *
        ∫⁻ u : ℝ, ENNReal.ofReal (|u| ^ (1 - s.val) * ‖𝓕 f u‖ ^ 2) := by
  unfold Riesz1.lineVariance
  rw [Riesz1.lineSobolevSq_toLp_eq_lintegral hf1 hf2]
  congr 2
  funext u
  change ENNReal.ofReal (|u| ^ (2 * ((1 - s.val) / 2)) * ‖𝓕 f u‖ ^ 2) = _
  rw [show 2 * ((1 - s.val) / 2) = 1 - s.val by ring]

/-- See the proof of Corollary 1.1 in the paper, the unit-interval variance normalization.
Finiteness is explicit, so the variance has no infinite-value ambiguity. -/
theorem unitInterval_lineVariance (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    Riesz1.lineVariance (longParameters β s) unitIntervalL2 =
      ENNReal.ofReal (Riesz1.countVariance (longParameters β s)) ∧
    Riesz1.lineVariance (longParameters β s) unitIntervalL2 < ⊤ := by
  have hhalf := lineVariance_eq_fourier_lintegral β s
    integrable_intervalIndicator memLp_intervalIndicator
  have hunit := lineVariance_eq_fourier_lintegral β s
    integrable_unitIntervalIndicator memLp_unitIntervalIndicator
  change Riesz1.lineVariance (longParameters β s) intervalL2 = _ at hhalf
  change Riesz1.lineVariance (longParameters β s) unitIntervalL2 = _ at hunit
  rw [unitInterval_fourier_lintegral] at hunit
  have hscale : Riesz1.lineVariance (longParameters β s) unitIntervalL2 =
      ENNReal.ofReal ((2 : ℝ) ^ s.val) * intervalLineVariance β s := by
    rw [intervalLineVariance_eq, hhalf, hunit]
    ring
  have hpow : (2 : ℝ) ^ s.val * (2 : ℝ) ^ (-s.val) = 1 := by
    rw [← Real.rpow_add two_pos]; simp
  have heq : Riesz1.lineVariance (longParameters β s) unitIntervalL2 =
      ENNReal.ofReal (Riesz1.countVariance (longParameters β s)) := by
    rw [hscale, intervalLineVariance_eq_cot,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ← mul_assoc, hpow, one_mul]
    rfl
  exact ⟨heq, heq ▸ ENNReal.ofReal_lt_top⟩

/-- Algebraic normalization in the proof of Corollary 1.1. -/
lemma unitInterval_normalization_algebra (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ((2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s)) *
      ((2 * Real.pi) ^ s.val /
        (2 * Real.pi * Real.Gamma (1 + s.val) * Real.sin (Real.pi * s.val / 2))) =
      Riesz1.countVariance (longParameters β s) := by
  have hs := s.property.1
  have hβ := β.property
  have hsin : 0 < Real.sin (Real.pi * s.val / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, s.property.2])
  have hsin' : 0 < Real.sin (Real.pi * s.val) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, s.property.2])
  have hG := Real.Gamma_pos_of_pos hs
  have hG' := Real.Gamma_pos_of_pos (by linarith [s.property.2] : 0 < 1 - s.val)
  have hreflection : Real.Gamma s.val * Real.Gamma (1 - s.val) *
      (2 * Real.sin (Real.pi * s.val / 2) * Real.cos (Real.pi * s.val / 2)) = Real.pi := by
    rw [show 2 * Real.sin (Real.pi * s.val / 2) * Real.cos (Real.pi * s.val / 2) =
      Real.sin (Real.pi * s.val) by rw [← Real.sin_two_mul]; congr 1; ring]
    rw [Real.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hsin'.ne']
  have hp : (2 * Real.pi) ^ (1 - s.val) * (2 * Real.pi) ^ s.val = 2 * Real.pi := by
    rw [← Real.rpow_add (by positivity), sub_add_cancel, Real.rpow_one]
  rw [(rieszConstant_pos_and_eq_sin s.val hs s.property.2).2,
    show 1 + s.val = s.val + 1 by ring, Real.Gamma_add_one hs.ne', countVariance_longParameters]
  rw [div_mul_div_comm, hp]
  field_simp
  nlinarith [hreflection]

/-- See the proof of Corollary 1.1 in the paper: the unweighted Fourier integral of the
unit-interval indicator, in its nonnegative extended form. -/
theorem unitInterval_fourier_integral_ennreal (s : Riesz1.RieszExponent) :
    (∫⁻ u : ℝ, ENNReal.ofReal (|u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ s.val /
        (2 * Real.pi * Real.Gamma (1 + s.val) * Real.sin (Real.pi * s.val / 2))) := by
  let β : InverseTemperature := ⟨1, zero_lt_one⟩
  let A := (2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s)
  have hA : 0 < A := div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (mul_pos (mul_pos two_pos β.property) (Riesz1.rieszConstant_pos s))
  have h := (unitInterval_lineVariance β s).1
  rw [show unitIntervalL2 = memLp_unitIntervalIndicator.toLp _ from rfl,
    lineVariance_eq_fourier_lintegral β s integrable_unitIntervalIndicator memLp_unitIntervalIndicator] at h
  apply (ENNReal.mul_right_inj (by positivity : ENNReal.ofReal A ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [h, ← ENNReal.ofReal_mul hA.le, unitInterval_normalization_algebra]

/-- See the proof of Corollary 1.1 in the paper: finiteness and the real-valued Fourier integral.
The integrability assertion rules out the Bochner integral's nonintegrable junk value. -/
theorem unitInterval_fourier_integral (s : Riesz1.RieszExponent) :
    Integrable (fun u : ℝ => |u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2) ∧
    (∫ u : ℝ, |u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2) =
      (2 * Real.pi) ^ s.val /
        (2 * Real.pi * Real.Gamma (1 + s.val) * Real.sin (Real.pi * s.val / 2)) := by
  have hc : Continuous (𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ integrable_unitIntervalIndicator
  have hm : Measurable (fun u : ℝ => |u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2) := by
    have := hc.measurable
    fun_prop
  have hn : ∀ u : ℝ, 0 ≤ |u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2 := fun u => by positivity
  have hi := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ hn)).mp ((unitInterval_fourier_integral_ennreal s) ▸ ENNReal.ofReal_ne_top)
  refine ⟨hi, ?_⟩
  have h := unitInterval_fourier_integral_ennreal s
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at h
  have hsine : 0 < Real.sin (Real.pi * s.val / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity [s.property.1])
      (by nlinarith [Real.pi_pos, s.property.2])
  have hgamma : 0 < Real.Gamma (1 + s.val) := Real.Gamma_pos_of_pos (by linarith [s.property.1])
  have hval := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_ofReal (by positivity)] at hval
  exact hval

/-- All finite half-open interval fluctuations are square integrable. -/
lemma memLp_intervalFluctuation (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ℓ : Riesz1.Scale) :
    MemLp (intervalFluctuation ℓ N) 2 (gibbsMeasure (ofLong β s) N) := by
  rw [gibbsMeasure_ofLong]
  have := (Riesz1.modelWellDefined (longParameters β s) N).2.2
  have ha : MemLp (Riesz1.arcIndicator 0 (ℓ.val / 4)) 2 volume := by
    have hr := (Riesz1.memLp_arcIndicator 0 (ℓ.val / 4)).re
    change MemLp (fun x => (Riesz1.arcIndicator 0 (ℓ.val / 4) x : ℂ).re) 2 volume at hr
    simpa only [Complex.ofReal_re] using hr
  have hf : MemLp (intervalProfile ℓ) 2 (volume : Measure UnitAddCircle) :=
    ha.ae_eq (show intervalProfile ℓ =ᵐ[volume] Riesz1.arcIndicator 0 (ℓ.val / 4) from intervalProfile_ae_arcIndicator ℓ).symm
  exact (Riesz1.memLp_linearStatistic (longParameters β s) N hf).sub (memLp_const _)

/-- The first moment required by `Riesz1.variance`, at every size and scale. -/
lemma integrable_intervalFluctuation (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ℓ : Riesz1.Scale) :
    Integrable (intervalFluctuation ℓ N) (gibbsMeasure (ofLong β s) N) := by
  have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) N) := by
    rw [gibbsMeasure_ofLong]
    exact (Riesz1.modelWellDefined (longParameters β s) N).2.2
  exact (memLp_intervalFluctuation β s N ℓ).integrable one_le_two

/-- Internal error estimate for the proof of Corollary 1.1,
valid at every admissible size and scale, with the power of `Nℓ` strictly negative. -/
theorem intervalVariance_normalized_error (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧
      ∀ (N : ℕ+) (ℓ : Riesz1.Scale), 1 ≤ (N : ℝ) * ℓ.val →
        |((N : ℝ) * ℓ.val) ^ (-s.val) *
          (Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N)
            (integrable_intervalFluctuation β s N ℓ)).toReal -
          (intervalLineVariance β s).toReal| ≤
            C * (((N : ℝ) * ℓ.val) ^ e + ℓ.val ^ (2 - s.val)) := by
  let a := max (2 * s.val - 1) 0
  have ha : a < s.val := max_lt (by linarith [s.property.2]) s.property.1
  let η := (s.val - a) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C₁, hC₁, hb⟩ := intervalVariance_expansion β s η hη
  obtain ⟨C₂, hC₂, hc⟩ := arc_quantitative_bounds β s
  refine ⟨C₁ + C₂, by positivity, a + η - s.val, by dsimp [η]; linarith, ?_⟩
  intro N ℓ hN
  obtain ⟨hF, -, hbound⟩ := hb N ℓ hN
  have hK : 0 < (N : ℝ) * ℓ.val := lt_of_lt_of_le zero_lt_one hN
  have hpow : ((N : ℝ) * ℓ.val) ^ (-s.val) * ((N : ℝ) * ℓ.val) ^ s.val = 1 := by
    rw [← Real.rpow_add hK]; simp
  have hscale : ((N : ℝ) * ℓ.val) ^ (-s.val) *
      |(Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF).toReal -
        ((N : ℝ) * ℓ.val) ^ s.val * (intervalCircleVariance β s ℓ).toReal| ≤
      C₁ * ((N : ℝ) * ℓ.val) ^ (a + η - s.val) := by
    have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hK.le (-s.val))
    have hp : ((N : ℝ) * ℓ.val) ^ (-s.val) * ((N : ℝ) * ℓ.val) ^ (a + η) =
        ((N : ℝ) * ℓ.val) ^ (a + η - s.val) := by
      rw [← Real.rpow_add hK]; congr 1; ring
    calc _ ≤ ((N : ℝ) * ℓ.val) ^ (-s.val) * (C₁ * ((N : ℝ) * ℓ.val) ^ (a + η)) := hm
      _ = _ := by rw [mul_left_comm, hp]
  have hsimp : |((N : ℝ) * ℓ.val) ^ (-s.val) *
      (Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF).toReal -
        (intervalCircleVariance β s ℓ).toReal| ≤ C₁ * ((N : ℝ) * ℓ.val) ^ (a + η - s.val) := by
    rw [← abs_of_nonneg (Real.rpow_nonneg hK.le (-s.val)), ← abs_mul, mul_sub, ← mul_assoc, hpow,
      one_mul] at hscale
    exact hscale
  have hc' := (hc ℓ).2
  rw [← intervalCircleVariance_eq] at hc'
  calc _ ≤ |((N : ℝ) * ℓ.val) ^ (-s.val) *
        (Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF).toReal -
        (intervalCircleVariance β s ℓ).toReal| +
        |(intervalCircleVariance β s ℓ).toReal - (intervalLineVariance β s).toReal| := abs_sub_le _ _ _
    _ ≤ C₁ * ((N : ℝ) * ℓ.val) ^ (a + η - s.val) + C₂ * ℓ.val ^ (2 - s.val) :=
      add_le_add hsimp hc'
    _ ≤ _ := by
      nlinarith [Real.rpow_nonneg hK.le (a + η - s.val), Real.rpow_nonneg ℓ.property.1.le (2 - s.val)]

/-- The variance half of the proof of Corollary 1.1 for the centered
half-length statistic, along arbitrary pairs of particle numbers and admissible scales. -/
theorem intervalVariance_pairs_limit (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (ℓ : ℕ → Riesz1.Scale)
    (hℓ : Tendsto (fun j => (ℓ j).val) atTop (𝓝 0))
    (hK : Tendsto (fun j => (N j : ℝ) * (ℓ j).val) atTop atTop) :
    Tendsto (fun j => ((N j : ℝ) * (ℓ j).val) ^ (-s.val) *
      (Riesz1.variance (gibbsMeasure (ofLong β s) (N j)) (intervalFluctuation (ℓ j) (N j))
        (integrable_intervalFluctuation β s (N j) (ℓ j))).toReal)
      atTop (𝓝 (intervalLineVariance β s).toReal) := by
  obtain ⟨C, -, e, he, hb⟩ := intervalVariance_normalized_error β s
  have h₁ : Tendsto (fun j => ((N j : ℝ) * (ℓ j).val) ^ e) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_neg] using (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp hK
  have h₂ : Tendsto (fun j => (ℓ j).val ^ (2 - s.val)) atTop (𝓝 0) := by
    exact hℓ.rpow_const_nhds_zero (by linarith [s.property.2])
  have hzero : Tendsto (fun j => C * (((N j : ℝ) * (ℓ j).val) ^ e +
      (ℓ j).val ^ (2 - s.val))) atTop (𝓝 0) := by
    simpa using (h₁.add h₂).const_mul C
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hzero
  filter_upwards [hK.eventually_ge_atTop 1] with j hj
  simpa only [Real.dist_eq] using hb (N j) (ℓ j) hj

/-- Explicit finiteness accompanies every real finite-interval variance below. -/
theorem intervalFluctuation_variance_finite (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ℓ : Riesz1.Scale) :
    Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N)
      (integrable_intervalFluctuation β s N ℓ) < ⊤ := by
  have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) N) := by
    rw [gibbsMeasure_ofLong]
    exact (Riesz1.modelWellDefined (longParameters β s) N).2.2
  exact (Riesz1.variance_ne_top_of_memLp _ (memLp_intervalFluctuation β s N ℓ)).lt_top

/-- See the proof of Corollary 1.1 in the paper, normalization and variance limit for the
centered half-open count, whose microscopic interval length is `R = Nℓ/2`.
The indexing allows arbitrary pairs of particle numbers and admissible scales. -/
theorem intervalVariance_radius_pairs_limit (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (ℓ : ℕ → Riesz1.Scale)
    (hℓ : Tendsto (fun j => (ℓ j).val) atTop (𝓝 0))
    (hK : Tendsto (fun j => (N j : ℝ) * (ℓ j).val) atTop atTop) :
    (∀ j, Riesz1.variance (gibbsMeasure (ofLong β s) (N j)) (intervalFluctuation (ℓ j) (N j))
      (integrable_intervalFluctuation β s (N j) (ℓ j)) < ⊤) ∧
    Tendsto (fun j => ((N j : ℝ) * (ℓ j).val / 2) ^ (-s.val) *
      (Riesz1.variance (gibbsMeasure (ofLong β s) (N j)) (intervalFluctuation (ℓ j) (N j))
        (integrable_intervalFluctuation β s (N j) (ℓ j))).toReal)
      atTop (𝓝 (Riesz1.countVariance (longParameters β s))) := by
  refine ⟨fun j => intervalFluctuation_variance_finite β s (N j) (ℓ j), ?_⟩
  have hv : (2 : ℝ) ^ s.val * (intervalLineVariance β s).toReal =
      Riesz1.countVariance (longParameters β s) := by
    rw [intervalLineVariance_eq_cot, ENNReal.toReal_ofReal]
    · rw [← mul_assoc, ← Real.rpow_add two_pos]
      simp only [add_neg_cancel, Real.rpow_zero, one_mul]
      rfl
    · have hc : 0 ≤ Riesz1.countVariance (longParameters β s) := by
        have hsin : 0 ≤ Real.sin (Real.pi * s.val / 2) :=
          Real.sin_nonneg_of_mem_Icc ⟨by positivity [s.property.1], by nlinarith [s.property.2, Real.pi_pos]⟩
        have hcos : 0 ≤ Real.cos (Real.pi * s.val / 2) :=
          Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [s.property.1, Real.pi_pos], by nlinarith [s.property.2, Real.pi_pos]⟩
        rw [countVariance_longParameters]
        positivity [s.property.1, β.property]
      change 0 ≤ (2 : ℝ) ^ (-s.val) * Riesz1.countVariance (longParameters β s)
      positivity
  have h := (intervalVariance_pairs_limit β s N ℓ hℓ hK).const_mul ((2 : ℝ) ^ s.val)
  rw [hv] at h
  convert h using 1
  funext j
  rw [Real.div_rpow (by positivity [((ℓ j).property.1)] : 0 ≤ (N j : ℝ) * (ℓ j).val) (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  ring

end Riesz2

end
