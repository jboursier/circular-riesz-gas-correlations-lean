/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-!
# Exponential tails from two quantiles

The secant argument in the proof of Theorem 1. The logarithm is
only evaluated on the positive support. A vanishing survival probability
is handled separately, so that `Real.log 0` never supplies a slope.
-/

public section

open MeasureTheory Set

namespace Riesz2.LogConcaveQuantileTail

/-- Internal secant estimate. Two separated quantiles of an antitone,
nonnegative function with concave logarithm control its whole right tail.
This also covers the endpoint `t = b` and tails which vanish. -/
theorem tail_le_of_quantiles {S : ℝ → ℝ}
    (hS : ∀ x, 0 ≤ S x) (hanti : Antitone S)
    (hlog : ConcaveOn ℝ {x | 0 < S x} (fun x => Real.log (S x)))
    {a b p q : ℝ} (hab : a < b) (hp : 0 < p) (hq : 0 < q)
    (ha : p ≤ S a) (hb : S b ≤ q) {t : ℝ} (ht : b ≤ t) :
    S t ≤ q * Real.exp (-(t - b) * Real.log (p / q) / (b - a)) := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hb
  by_cases hz : S t = 0
  · rw [hz]
    positivity
  have hSt : 0 < S t := lt_of_le_of_ne (hS t) (Ne.symm hz)
  have hSb : 0 < S b := hSt.trans_le (hanti ht.le)
  have hSa : 0 < S a := hp.trans_le ha
  have hslope := hlog.slope_anti_adjacent hSa hSt hab ht
  have hlogs : Real.log (S b) - Real.log (S a) ≤ -Real.log (p / q) := by
    rw [Real.log_div hp.ne' hq.ne']
    linarith [Real.log_le_log hSb hb, Real.log_le_log hp ha]
  have hslope' : (Real.log (S t) - Real.log (S b)) / (t - b) ≤
      -Real.log (p / q) / (b - a) :=
    hslope.trans (div_le_div_of_nonneg_right hlogs (sub_pos.mpr hab).le)
  have hbound : Real.log (S t) ≤ Real.log q +
      (-(t - b) * Real.log (p / q) / (b - a)) := by
    have hmul := (div_le_iff₀ (sub_pos.mpr ht)).mp hslope'
    have hqlog := Real.log_le_log hSb hb
    have he : -Real.log (p / q) / (b - a) * (t - b) =
        -(t - b) * Real.log (p / q) / (b - a) := by ring
    rw [he] at hmul
    linarith
  have he := Real.exp_le_exp.mpr hbound
  rwa [Real.exp_log hSt, Real.exp_add, Real.exp_log hq] at he

/-- The quantitative bound used in the proof of Theorem 1: survival at `-A`
at least `3/4` and survival at `A` at most `1/4` give a fixed exponential
rate on `[A,∞)`. -/
theorem tail_le_of_quarter_quantiles {S : ℝ → ℝ}
    (hS : ∀ x, 0 ≤ S x) (hanti : Antitone S)
    (hlog : ConcaveOn ℝ {x | 0 < S x} (fun x => Real.log (S x)))
    {A : ℝ} (hA : 0 < A) (hleft : 3 / 4 ≤ S (-A)) (hright : S A ≤ 1 / 4)
    {t : ℝ} (ht : A ≤ t) :
    S t ≤ (1 / 4) * Real.exp (-(t - A) * Real.log 3 / (2 * A)) := by
  have h := tail_le_of_quantiles hS hanti hlog (a := -A) (b := A)
    (p := 3 / 4) (q := 1 / 4) (by linarith) (by norm_num) (by norm_num)
    hleft hright ht
  norm_num only [show (3 / 4 : ℝ) / (1 / 4) = 3 by norm_num,
    show A - -A = 2 * A by ring] at h
  exact h

/-- The decay rate from the quarter-quantile estimate is strictly positive. -/
theorem quarter_quantile_rate_pos {A : ℝ} (hA : 0 < A) :
    0 < Real.log 3 / (2 * A) :=
  div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) hA)

/-- Internal probability interface for the right-tail estimate. Finiteness
of the measure justifies the conversion from real to extended probabilities. -/
theorem measure_Ici_le_of_quarter_quantiles (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hlog : ConcaveOn ℝ {x | 0 < (μ (Ici x)).toReal}
      (fun x => Real.log ((μ (Ici x)).toReal)))
    {A : ℝ} (hA : 0 < A)
    (hleft : 3 / 4 ≤ (μ (Ici (-A))).toReal)
    (hright : (μ (Ici A)).toReal ≤ 1 / 4) {t : ℝ} (ht : A ≤ t) :
    μ (Ici t) ≤ ENNReal.ofReal
      ((1 / 4) * Real.exp (-(t - A) * Real.log 3 / (2 * A))) := by
  have hanti : Antitone (fun x : ℝ => (μ (Ici x)).toReal) := by
    intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Ici_subset_Ici.mpr hxy))
  have h := tail_le_of_quarter_quantiles (fun _ => ENNReal.toReal_nonneg) hanti
    hlog hA hleft hright ht
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _)] using ENNReal.ofReal_le_ofReal h

/-- The reflected quarter-quantile estimate, stated for the actual lower
ray rather than a separately encoded reflected law. -/
theorem measure_Iic_le_of_quarter_quantiles (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hlog : ConcaveOn ℝ {x | 0 < (μ (Iic (-x))).toReal}
      (fun x => Real.log ((μ (Iic (-x))).toReal)))
    {A : ℝ} (hA : 0 < A)
    (hleft : 3 / 4 ≤ (μ (Iic A)).toReal)
    (hright : (μ (Iic (-A))).toReal ≤ 1 / 4) {t : ℝ} (ht : A ≤ t) :
    μ (Iic (-t)) ≤ ENNReal.ofReal
      ((1 / 4) * Real.exp (-(t - A) * Real.log 3 / (2 * A))) := by
  have hanti : Antitone (fun x : ℝ => (μ (Iic (-x))).toReal) := by
    intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono (Iic_subset_Iic.mpr (neg_le_neg hxy)))
  have h := tail_le_of_quarter_quantiles (fun _ => ENNReal.toReal_nonneg) hanti hlog
    hA (by simpa only [neg_neg] using hleft) hright ht
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _)] using ENNReal.ofReal_le_ofReal h

/-- Internal two-sided probability interface for the proof of Theorem 1. The same constants
control both tails, including a finite endpoint or a vanishing tail. -/
theorem measure_abs_ge_le_internal (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hlogR : ConcaveOn ℝ {x | 0 < (μ (Ici x)).toReal}
      (fun x => Real.log ((μ (Ici x)).toReal)))
    (hlogL : ConcaveOn ℝ {x | 0 < (μ (Iic (-x))).toReal}
      (fun x => Real.log ((μ (Iic (-x))).toReal)))
    {A : ℝ} (hA : 0 < A)
    (hRL : 3 / 4 ≤ (μ (Ici (-A))).toReal)
    (hRR : (μ (Ici A)).toReal ≤ 1 / 4)
    (hLL : 3 / 4 ≤ (μ (Iic A)).toReal)
    (hLR : (μ (Iic (-A))).toReal ≤ 1 / 4) {t : ℝ} (ht : A ≤ t) :
    μ {x : ℝ | t ≤ |x|} ≤ ENNReal.ofReal
      ((1 / 2) * Real.exp (-(t - A) * Real.log 3 / (2 * A))) := by
  have hset : {x : ℝ | t ≤ |x|} = Ici t ∪ Iic (-t) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Ici, mem_Iic, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [hset]
  calc μ (Ici t ∪ Iic (-t)) ≤ μ (Ici t) + μ (Iic (-t)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((1 / 4) * Real.exp (-(t - A) * Real.log 3 / (2 * A))) +
        ENNReal.ofReal ((1 / 4) * Real.exp (-(t - A) * Real.log 3 / (2 * A))) :=
      add_le_add (measure_Ici_le_of_quarter_quantiles μ hlogR hA hRL hRR ht)
        (measure_Iic_le_of_quarter_quantiles μ hlogL hA hLL hLR ht)
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Internal layer-cake interface. A common exponential tail gives a
common fourth moment, uniformly over the measures. Finiteness is proved
as an extended-integral bound before any real fourth moment is used. -/
theorem exists_fourth_moment_bound_internal {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 < M ∧ ∀ (μ : Measure ℝ),
      (∀ t : ℝ, 0 < t → μ {x : ℝ | t ≤ |x|} ≤ ENNReal.ofReal (C * Real.exp (-c * t))) →
      MemLp (fun x : ℝ => x ^ 2) 2 μ ∧ (∫ x : ℝ, (x ^ 2) ^ 2 ∂μ) ≤ M := by
  let B := fun t : ℝ => (4 * C) * (t ^ 3 * Real.exp (-c * t))
  have hBi : IntegrableOn B (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 3) (p := 1) (b := c) (by norm_num) (by norm_num) hc
    simpa only [B, IntegrableOn, Real.rpow_ofNat, Real.rpow_one] using h.const_mul (4 * C)
  let M := max 1 (∫ t in Ioi 0, B t)
  refine ⟨M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun μ htail => ?_⟩
  have hlayer := lintegral_comp_eq_lintegral_meas_le_mul μ
    (f := fun x : ℝ => |x|) (g := fun t : ℝ => 4 * t ^ 3)
    (Filter.Eventually.of_forall abs_nonneg) (continuous_abs.measurable.aemeasurable)
    (fun t _ => (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      positivity)
  have hprim (x : ℝ) : (∫ t in (0 : ℝ)..|x|, 4 * t ^ 3) = (x ^ 2) ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    convert congrArg (fun y : ℝ => y ^ 2) (sq_abs x) using 1; ring
  simp_rw [hprim] at hlayer
  have hbound : (∫⁻ x : ℝ, ENNReal.ofReal ((x ^ 2) ^ 2) ∂μ) ≤
      ENNReal.ofReal (∫ t in Ioi 0, B t) := by
    rw [hlayer, ofReal_integral_eq_lintegral_ofReal hBi
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        dsimp [B]
        positivity)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc μ {x : ℝ | t ≤ |x|} * ENNReal.ofReal (4 * t ^ 3) ≤
        ENNReal.ofReal (C * Real.exp (-c * t)) * ENNReal.ofReal (4 * t ^ 3) :=
          mul_le_mul' (htail t ht) le_rfl
      _ = ENNReal.ofReal (B t) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [B]
        ring
  have hi : Integrable (fun x : ℝ => (x ^ 2) ^ 2) μ := by
    refine ⟨(measurable_id.pow_const 2).pow_const 2 |>.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun x => sq_nonneg (x ^ 2))).mpr ?_⟩
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have hmem : MemLp (fun x : ℝ => x ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq (measurable_id.pow_const 2).aestronglyMeasurable).mpr hi
  refine ⟨hmem, ?_⟩
  have hnonneg : 0 ≤ ∫ t in Ioi 0, B t := integral_nonneg_of_ae
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      dsimp [B]
      positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sq_nonneg (x ^ 2)),
    ENNReal.ofReal_le_ofReal_iff hnonneg] at hbound
  exact hbound.trans (le_max_right _ _)

end Riesz2.LogConcaveQuantileTail
