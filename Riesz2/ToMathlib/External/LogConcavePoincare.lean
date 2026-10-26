/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.GeneralLogConcaveSurvival
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Analytic reductions for the one-dimensional Poincaré inequality

One-dimensional tail-to-density bounds give a smooth Poincaré inequality.
For a log-concave density, the coefficient is controlled by its value at a median.
All nonnegative integral estimates use extended integrals.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff Topology

namespace Riesz2.LogConcavePoincare

/-- Tonelli on the region `m ≤ t ≤ x`, with no regularity assumption on
the measure. This is a general integral identity, not a log-concavity input. -/
theorem lintegral_primitive_eq_tail (μ : Measure ℝ) [SFinite μ]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) (m : ℝ) :
    (∫⁻ x, ∫⁻ t in Icc m x, g t ∂volume ∂μ) =
      ∫⁻ t in Ici m, g t * μ (Ici t) ∂volume := by
  let D : Set (ℝ × ℝ) := {p | m ≤ p.2 ∧ p.2 ≤ p.1}
  have hD : MeasurableSet D :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hm : Measurable (D.indicator (fun p : ℝ × ℝ => g p.2)) :=
    (hg.comp measurable_snd).indicator hD
  have hpoint (x t : ℝ) :
      (Icc m x).indicator g t = D.indicator (fun p : ℝ × ℝ => g p.2) (x, t) := rfl
  simp_rw [← lintegral_indicator measurableSet_Icc, hpoint]
  rw [lintegral_lintegral_swap (μ := μ) (ν := volume)
    (f := fun x t => D.indicator (fun p : ℝ × ℝ => g p.2) (x, t))
    hm.aemeasurable]
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro t
  by_cases ht : m ≤ t
  · have he : (fun x : ℝ => D.indicator (fun p : ℝ × ℝ => g p.2) (x, t)) =
        (Ici t).indicator (fun _ => g t) := by
      ext x
      simp [D, Set.indicator, ht]
    rw [he, lintegral_indicator measurableSet_Ici, lintegral_const,
      Measure.restrict_apply_univ, indicator_of_mem (show t ∈ Ici m from ht)]
  · have he : (fun x : ℝ => D.indicator (fun p : ℝ × ℝ => g p.2) (x, t)) = 0 := by
      ext x
      simp [D, Set.indicator, ht]
    rw [he]
    simp [Set.indicator, ht]
    change (∫⁻ _x, (0 : ℝ≥0∞) ∂μ) = 0
    simp

/-- Tonelli on the region `x ≤ t ≤ m`, with no regularity assumption on
the measure. This is a general integral identity, not a log-concavity input. -/
theorem lintegral_left_primitive_eq_tail (μ : Measure ℝ) [SFinite μ]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) (m : ℝ) :
    (∫⁻ x, ∫⁻ t in Icc x m, g t ∂volume ∂μ) =
      ∫⁻ t in Iic m, g t * μ (Iic t) ∂volume := by
  let D : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ m}
  have hD : MeasurableSet D :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hm : Measurable (D.indicator (fun p : ℝ × ℝ => g p.2)) :=
    (hg.comp measurable_snd).indicator hD
  have hpoint (x t : ℝ) :
      (Icc x m).indicator g t = D.indicator (fun p : ℝ × ℝ => g p.2) (x, t) := rfl
  simp_rw [← lintegral_indicator measurableSet_Icc, hpoint]
  rw [lintegral_lintegral_swap (μ := μ) (ν := volume)
    (f := fun x t => D.indicator (fun p : ℝ × ℝ => g p.2) (x, t))
    hm.aemeasurable]
  rw [← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro t
  by_cases ht : t ≤ m
  · have he : (fun x : ℝ => D.indicator (fun p : ℝ × ℝ => g p.2) (x, t)) =
        (Iic t).indicator (fun _ => g t) := by
      ext x
      simp [D, Set.indicator, ht]
    rw [he, lintegral_indicator measurableSet_Iic, lintegral_const,
      Measure.restrict_apply_univ, indicator_of_mem (show t ∈ Iic m from ht)]
  · have he : (fun x : ℝ => D.indicator (fun p : ℝ × ℝ => g p.2) (x, t)) = 0 := by
      ext x
      simp [D, Set.indicator, ht]
    rw [he]
    simp [Set.indicator, ht]
    change (∫⁻ _x, (0 : ℝ≥0∞) ∂μ) = 0
    simp

/-- The squared increment of a `C¹` function is bounded by the primitive
of twice the absolute product of its increment and derivative. -/
theorem sq_sub_le_primitive {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {m x : ℝ} (hmx : m ≤ x) :
    ENNReal.ofReal ((h x - h m) ^ 2) ≤
      ∫⁻ t in Icc m x, ENNReal.ofReal (2 * |h t - h m| * |deriv h t|) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hc : Continuous (fun t => 2 * |h t - h m| * |deriv h t|) := by fun_prop
  have he : (∫ t in m..x, 2 * (h t - h m) * deriv h t) = (h x - h m) ^ 2 := by
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := m) (b := x) (f := fun t => (h t - h m) ^ 2)
      (f' := fun t => 2 * (h t - h m) * deriv h t)
      (fun t _ => by
        convert (((hh.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub_const
          (h m)).pow 2 using 1; ring)
      (by exact (by fun_prop : Continuous (fun t =>
        2 * (h t - h m) * deriv h t)).intervalIntegrable _ _)
    simpa using hf
  have hb : (h x - h m) ^ 2 ≤ ∫ t in m..x, 2 * |h t - h m| * |deriv h t| := by
    rw [← he]
    apply intervalIntegral.integral_mono_on hmx
      (by exact (by fun_prop : Continuous (fun t =>
        2 * (h t - h m) * deriv h t)).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    intro t _
    calc 2 * (h t - h m) * deriv h t ≤ |2 * (h t - h m) * deriv h t| := le_abs_self _
      _ = 2 * |h t - h m| * |deriv h t| := by simp [abs_mul]
  apply (ENNReal.ofReal_le_ofReal hb).trans_eq
  rw [intervalIntegral.integral_of_le hmx,
    ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
      (ae_of_all _ fun t => by positivity)]

/-- The two-sided version of the squared-increment primitive estimate. -/
theorem sq_sub_le_uIcc_primitive {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (m x : ℝ) :
    ENNReal.ofReal ((h x - h m) ^ 2) ≤
      ∫⁻ t in uIcc m x, ENNReal.ofReal (2 * |h t - h m| * |deriv h t|) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hc : Continuous (fun t => 2 * (h t - h m) * deriv h t) := by fun_prop
  have he : (∫ t in m..x, 2 * (h t - h m) * deriv h t) = (h x - h m) ^ 2 := by
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := m) (b := x) (f := fun t => (h t - h m) ^ 2)
      (f' := fun t => 2 * (h t - h m) * deriv h t)
      (fun t _ => by
        convert (((hh.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub_const
          (h m)).pow 2 using 1; ring)
      (hc.intervalIntegrable _ _)
    simpa using hf
  have hb := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (f := fun t => 2 * (h t - h m) * deriv h t) (μ := volume) (a := m) (b := x)
  rw [he, Real.norm_of_nonneg (sq_nonneg _)] at hb
  apply (ENNReal.ofReal_le_ofReal hb).trans_eq
  change ENNReal.ofReal (∫ t in Ioc (min m x) (max m x),
    ‖2 * (h t - h m) * deriv h t‖) = _
  rw [← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hc.norm.integrableOn_Icc
      (ae_of_all _ fun t => norm_nonneg _)]
  apply lintegral_congr
  intro t
  congr 1
  simp [Real.norm_eq_abs]

/-- Upper-tail domination controls the upper half of a squared increment.
 -/
theorem upper_increment_bound_internal {f h : ℝ → ℝ} (hf : Measurable f)
    (hh : ContDiff ℝ 1 h) (m : ℝ) (A : ℝ≥0∞)
    (htail : ∀ t ∈ Ici m,
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici t) ≤
        A * ENNReal.ofReal (f t)) :
    (∫⁻ x in Ici m, ENNReal.ofReal ((h x - h m) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ≤
      A * ∫⁻ t in Ici m, ENNReal.ofReal (2 * |h t - h m| * |deriv h t|)
        ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let g := fun t => ENNReal.ofReal (2 * |h t - h m| * |deriv h t|)
  have hhc := hh.continuous
  have hd : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hg : Measurable g := by dsimp [g]; fun_prop
  calc
    (∫⁻ x in Ici m, ENNReal.ofReal ((h x - h m) ^ 2) ∂μ) ≤
        ∫⁻ x, ∫⁻ t in Icc m x, g t ∂volume ∂μ := by
      rw [← lintegral_indicator measurableSet_Ici]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Ici m
      · rw [indicator_of_mem hx]
        exact sq_sub_le_primitive hh hx
      · rw [indicator_of_notMem hx]
        exact zero_le
    _ = ∫⁻ t in Ici m, g t * μ (Ici t) := lintegral_primitive_eq_tail μ hg m
    _ ≤ ∫⁻ t in Ici m, g t * (A * ENNReal.ofReal (f t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      gcongr
      exact htail t ht
    _ = A * ∫⁻ t in Ici m, g t ∂μ := by
      change (∫⁻ t in Ici m, g t * (A * ENNReal.ofReal (f t))) =
        A * ∫⁻ t in Ici m, g t ∂volume.withDensity (fun x => ENNReal.ofReal (f x))
      rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hf.ennreal_ofReal hg
          measurableSet_Ici, ← lintegral_const_mul _ ((hf.ennreal_ofReal).mul hg)]
      apply lintegral_congr
      intro t
      change g t * (A * ENNReal.ofReal (f t)) = A * (ENNReal.ofReal (f t) * g t)
      ring

/-- Lower-tail domination controls the lower half of a squared increment.
 -/
theorem lower_increment_bound_internal {f h : ℝ → ℝ} (hf : Measurable f)
    (hh : ContDiff ℝ 1 h) (m : ℝ) (A : ℝ≥0∞)
    (htail : ∀ t ∈ Iic m,
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic t) ≤
        A * ENNReal.ofReal (f t)) :
    (∫⁻ x in Iic m, ENNReal.ofReal ((h x - h m) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ≤
      A * ∫⁻ t in Iic m, ENNReal.ofReal (2 * |h t - h m| * |deriv h t|)
        ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let g := fun t => ENNReal.ofReal (2 * |h t - h m| * |deriv h t|)
  have hhc := hh.continuous
  have hd : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hg : Measurable g := by dsimp [g]; fun_prop
  calc
    (∫⁻ x in Iic m, ENNReal.ofReal ((h x - h m) ^ 2) ∂μ) ≤
        ∫⁻ x, ∫⁻ t in Icc x m, g t ∂volume ∂μ := by
      rw [← lintegral_indicator measurableSet_Iic]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Iic m
      · rw [indicator_of_mem hx]
        simpa only [uIcc_of_ge hx] using sq_sub_le_uIcc_primitive hh m x
      · rw [indicator_of_notMem hx]
        exact zero_le
    _ = ∫⁻ t in Iic m, g t * μ (Iic t) := lintegral_left_primitive_eq_tail μ hg m
    _ ≤ ∫⁻ t in Iic m, g t * (A * ENNReal.ofReal (f t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      gcongr
      exact htail t ht
    _ = A * ∫⁻ t in Iic m, g t ∂μ := by
      change (∫⁻ t in Iic m, g t * (A * ENNReal.ofReal (f t))) =
        A * ∫⁻ t in Iic m, g t ∂volume.withDensity (fun x => ENNReal.ofReal (f x))
      rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hf.ennreal_ofReal hg
          measurableSet_Iic, ← lintegral_const_mul _ ((hf.ennreal_ofReal).mul hg)]
      apply lintegral_congr
      intro t
      change g t * (A * ENNReal.ofReal (f t)) = A * (ENNReal.ofReal (f t) * g t)
      ring

/-- Splitting a diffuse measure into the two closed half-lines does not
double count any mass. -/
theorem lintegral_halfline_add (μ : Measure ℝ) [NullSingletonClass μ]
    (g : ℝ → ℝ≥0∞) (m : ℝ) :
    (∫⁻ x in Iic m, g x ∂μ) + (∫⁻ x in Ici m, g x ∂μ) = ∫⁻ x, g x ∂μ := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  simpa only [compl_Iic] using lintegral_add_compl g (μ := μ) measurableSet_Iic

/-- Two one-sided tail bounds yield the global first-order estimate
used in the one-dimensional Cheeger argument. No finite-integral
assumption is needed for this step. -/
theorem increment_bound_internal {f h : ℝ → ℝ} (hf : Measurable f)
    (hh : ContDiff ℝ 1 h) (m : ℝ) (A : ℝ≥0∞)
    (hleft : ∀ t ∈ Iic m,
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic t) ≤
        A * ENNReal.ofReal (f t))
    (hright : ∀ t ∈ Ici m,
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici t) ≤
        A * ENNReal.ofReal (f t)) :
    (∫⁻ x, ENNReal.ofReal ((h x - h m) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ≤
      A * ∫⁻ t, ENNReal.ofReal (2 * |h t - h m| * |deriv h t|)
        ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  rw [← lintegral_halfline_add μ _ m,
    ← lintegral_halfline_add μ (fun t =>
      ENNReal.ofReal (2 * |h t - h m| * |deriv h t|)) m, mul_add]
  exact add_le_add (lower_increment_bound_internal hf hh m A hleft)
    (upper_increment_bound_internal hf hh m A hright)

/-- The mean minimizes the square integral. The variance identity and
all integrability facts are reused from Riesz 1 and Mathlib. -/
theorem centered_square_le_square_sub_const (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ → ℝ} (hh : MemLp h 2 μ) (c : ℝ) :
    (∫ x, (h x - ∫ y, h y ∂μ) ^ 2 ∂μ) ≤ ∫ x, (h x - c) ^ 2 ∂μ := by
  have hi := hh.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu := hh.sub (memLp_const c)
  have hm : (∫ x, (h x - c) ∂μ) = (∫ x, h x ∂μ) - c := by
    rw [integral_sub hi (integrable_const c)]
    simp
  have hv := Riesz1.WeightedSobolev.integral_sub_mean_sq hu
  simp only [Pi.sub_apply] at hv
  rw [hm] at hv
  have hp (x : ℝ) : (h x - c) - ((∫ x, h x ∂μ) - c) = h x - ∫ x, h x ∂μ := by ring
  simp_rw [hp] at hv
  linarith [sq_nonneg ((∫ x, h x ∂μ) - c)]

/-- A one-dimensional tail-to-density bound with coefficient `A` gives
a smooth Poincaré bound with coefficient `4 A²`.  -/
theorem poincare_of_tail_bounds_internal {f h : ℝ → ℝ} (hf : Measurable f)
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hh : ContDiff ℝ 1 h)
    (hL2 : MemLp h 2 (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hdL2 : MemLp (deriv h) 2 (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (m : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hleft : ∀ t ∈ Iic m,
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic t) ≤
        ENNReal.ofReal A * ENNReal.ofReal (f t))
    (hright : ∀ t ∈ Ici m,
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici t) ≤
        ENNReal.ofReal A * ENNReal.ofReal (f t)) :
    (∫⁻ x, ENNReal.ofReal ((h x - ∫ y, h y
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ≤
      ENNReal.ofReal (4 * A ^ 2) * ∫⁻ x, ENNReal.ofReal ((deriv h x) ^ 2)
        ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsProbabilityMeasure μ := hprob
  have hu : MemLp (fun x => h x - h m) 2 μ := hL2.sub (memLp_const _)
  have hiu := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp hu
  have hid := (memLp_two_iff_integrable_sq hdL2.aestronglyMeasurable).mp hdL2
  have hic := (memLp_two_iff_integrable_sq
    (hL2.sub (memLp_const (∫ y, h y ∂μ))).aestronglyMeasurable).mp
      (hL2.sub (memLp_const _))
  have hpLp : MemLp (fun x => |h x - h m| * |deriv h x|) 1 μ := by
    simpa only [Real.norm_eq_abs] using hu.norm.fun_mul hdL2.norm
  have hip := hpLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hip2 : Integrable (fun x => 2 * |h x - h m| * |deriv h x|) μ := by
    convert hip.const_mul 2 using 1
    ext x
    ring
  change Integrable (fun x => (h x - ∫ y, h y ∂μ) ^ 2) μ at hic
  have he := increment_bound_internal hf hh m (ENNReal.ofReal A) hleft hright
  rw [← ofReal_integral_eq_lintegral_ofReal hiu (ae_of_all _ fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hip2
      (ae_of_all _ fun x => by positivity), ← ENNReal.ofReal_mul hA] at he
  have hSn : 0 ≤ ∫ x, (h x - h m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hDn : 0 ≤ ∫ x, (deriv h x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have heR : (∫ x, (h x - h m) ^ 2 ∂μ) ≤
      2 * A * ∫ x, |h x - h m| * |deriv h x| ∂μ := by
    have hnonneg : 0 ≤ A * ∫ x, 2 * |h x - h m| * |deriv h x| ∂μ := by positivity
    have ht := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp he
    simp_rw [mul_assoc] at ht
    rw [integral_const_mul] at ht
    nlinarith
  have hcs := Riesz1.WeightedSobolev.abs_integral_mul_le_sqrt hu.norm hdL2.norm
  simp only [Real.norm_eq_abs, sq_abs] at hcs
  have heS : (∫ x, (h x - h m) ^ 2 ∂μ) ≤
      2 * A * (Real.sqrt (∫ x, (h x - h m) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (deriv h x) ^ 2 ∂μ)) :=
    heR.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcs) (by positivity))
  have hbound : (∫ x, (h x - h m) ^ 2 ∂μ) ≤
      4 * A ^ 2 * ∫ x, (deriv h x) ^ 2 ∂μ := by
    have hs := Real.sq_sqrt hSn
    have hd := Real.sq_sqrt hDn
    have hs0 := Real.sqrt_nonneg (∫ x, (h x - h m) ^ 2 ∂μ)
    have hd0 := Real.sqrt_nonneg (∫ x, (deriv h x) ^ 2 ∂μ)
    have hsB : Real.sqrt (∫ x, (h x - h m) ^ 2 ∂μ) ≤
        2 * A * Real.sqrt (∫ x, (deriv h x) ^ 2 ∂μ) := by
      by_cases hz : Real.sqrt (∫ x, (h x - h m) ^ 2 ∂μ) = 0
      · rw [hz]
        positivity
      · have hspos : 0 < Real.sqrt (∫ x, (h x - h m) ^ 2 ∂μ) := lt_of_le_of_ne hs0 (Ne.symm hz)
        apply (mul_le_mul_iff_right₀ hspos).mp
        nlinarith only [heS, hs]
    have hp := pow_le_pow_left₀ hs0 hsB 2
    nlinarith
  have hv := (centered_square_le_square_sub_const μ hL2 (h m)).trans hbound
  rw [← ofReal_integral_eq_lintegral_ofReal hic (ae_of_all _ fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hid (ae_of_all _ fun x => sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * A ^ 2)]
  exact ENNReal.ofReal_le_ofReal hv

/-- Equal-length increments of the logarithm decrease from left to right.
The product formulation remains valid at zeros and support endpoints. -/
theorem mul_shift_le_of_concaveOn_log {f : ℝ → ℝ} (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {a b t : ℝ} (hab : a ≤ b) (ht : 0 ≤ t) :
    f a * f (b + t) ≤ f b * f (a + t) := by
  by_cases ha : 0 < f a
  · by_cases hbt : 0 < f (b + t)
    · by_cases hzero : b + t - a = 0
      · have he : b = a := by linarith
        have ht0 : t = 0 := by linarith
        simp [he, ht0]
      have hL : 0 < b + t - a := lt_of_le_of_ne (by linarith) (Ne.symm hzero)
      let u := t / (b + t - a)
      let w := (b - a) / (b + t - a)
      have hu : 0 ≤ u := div_nonneg ht hL.le
      have hw : 0 ≤ w := div_nonneg (sub_nonneg.mpr hab) hL.le
      have huw : u + w = 1 := by dsimp [u, w]; field_simp; ring
      have hb : u • a + w • (b + t) = b := by
        dsimp [u, w]
        field_simp
        ring
      have hat : w • a + u • (b + t) = a + t := by
        dsimp [u, w]
        field_simp
        ring
      have hfb : 0 < f b := by
        have hx := hlog.1 ha hbt hu hw huw
        rw [hb] at hx
        exact hx
      have hfat : 0 < f (a + t) := by
        have hx := hlog.1 ha hbt hw hu (by linarith)
        rw [hat] at hx
        exact hx
      have hc1 := hlog.2 ha hbt hu hw huw
      have hc2 := hlog.2 ha hbt hw hu (by linarith : w + u = 1)
      rw [hb] at hc1
      rw [hat] at hc2
      simp only [smul_eq_mul] at hc1 hc2
      have hw' : w = 1 - u := by linarith
      rw [hw'] at hc1 hc2
      have hsum : Real.log (f a) + Real.log (f (b + t)) ≤
          Real.log (f b) + Real.log (f (a + t)) := by nlinarith only [hc1, hc2]
      rw [← Real.log_mul ha.ne' hbt.ne', ← Real.log_mul hfb.ne' hfat.ne'] at hsum
      exact (Real.log_le_log_iff (mul_pos ha hbt) (mul_pos hfb hfat)).mp hsum
    · have hz : f (b + t) = 0 := le_antisymm (le_of_not_gt hbt) (hnn _)
      rw [hz, mul_zero]
      exact mul_nonneg (hnn _) (hnn _)
  · have hz : f a = 0 := le_antisymm (le_of_not_gt ha) (hnn _)
    rw [hz, zero_mul]
    exact mul_nonneg (hnn _) (hnn _)

/-- Translating a Lebesgue upper-ray integral to the positive half-line. -/
theorem lintegral_upper_translate {g : ℝ → ℝ≥0∞} (hg : Measurable g) (c : ℝ) :
    (∫⁻ x in Ici c, g x) = ∫⁻ t in Ici 0, g (c + t) := by
  have he := (measurePreserving_add_left volume c).setLIntegral_comp_preimage
    (s := Ici c) measurableSet_Ici hg
  have hs : (fun t : ℝ => c + t) ⁻¹' Ici c = Ici 0 := by
    ext t
    simp only [mem_preimage, mem_Ici]
    constructor <;> intro ht <;> linarith
  rw [hs] at he
  exact he.symm

/-- The survival-to-density ratio of a log-concave density decreases.
The multiplied form needs no strict positivity and handles zeros. -/
theorem upper_tail_mul_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (f a) *
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici b) ≤
      ENNReal.ofReal (f b) *
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici a) := by
  rw [withDensity_apply _ measurableSet_Ici, withDensity_apply _ measurableSet_Ici,
    lintegral_upper_translate hf.ennreal_ofReal b,
    lintegral_upper_translate hf.ennreal_ofReal a,
    ← lintegral_const_mul _ (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (f (b + t)))),
    ← lintegral_const_mul _ (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (f (a + t))))]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [← ENNReal.ofReal_mul (hnn _), ← ENNReal.ofReal_mul (hnn _)]
  exact ENNReal.ofReal_le_ofReal (mul_shift_le_of_concaveOn_log hnn hlog hab ht)

/-- Reflecting and translating a Lebesgue lower-ray integral to the
positive half-line. -/
theorem lintegral_lower_translate {g : ℝ → ℝ≥0∞} (hg : Measurable g) (c : ℝ) :
    (∫⁻ x in Iic c, g x) = ∫⁻ t in Ici 0, g (c - t) := by
  have he := (volume.measurePreserving_sub_left c).setLIntegral_comp_preimage
    (s := Iic c) measurableSet_Iic hg
  have hs : (fun t : ℝ => c - t) ⁻¹' Iic c = Ici 0 := by
    ext t
    simp only [mem_preimage, mem_Ici, mem_Iic]
    constructor <;> intro ht <;> linarith
  rw [hs] at he
  exact he.symm

/-- The lower-tail-to-density ratio of a log-concave density increases.
The multiplied form also covers zero density values. -/
theorem lower_tail_mul_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (f b) *
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic a) ≤
      ENNReal.ofReal (f a) *
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic b) := by
  rw [withDensity_apply _ measurableSet_Iic, withDensity_apply _ measurableSet_Iic,
    lintegral_lower_translate hf.ennreal_ofReal a,
    lintegral_lower_translate hf.ennreal_ofReal b,
    ← lintegral_const_mul _ (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (f (a - t)))),
    ← lintegral_const_mul _ (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (f (b - t))))]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  change 0 ≤ t at ht
  rw [← ENNReal.ofReal_mul (hnn _), ← ENNReal.ofReal_mul (hnn _)]
  apply ENNReal.ofReal_le_ofReal
  have hs := mul_shift_le_of_concaveOn_log hnn hlog
    (a := a - t) (b := a) (t := b - a) (by linarith : a - t ≤ a) (sub_nonneg.mpr hab)
  have he1 : a + (b - a) = b := by ring
  have he2 : a - t + (b - a) = b - t := by ring
  rw [he1, he2] at hs
  simpa only [mul_comm] using hs

/-- A log-concave density has Poincaré coefficient at most `1 / f(m)²`
at a positive-density median.  -/
theorem poincare_of_median_internal {f h : ℝ → ℝ} (hf : Measurable f)
    (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hh : ContDiff ℝ ∞ h)
    (hL2 : MemLp h 2 (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hdL2 : MemLp (deriv h) 2 (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (m : ℝ) (hfm : 0 < f m)
    (hmleft : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic m) = ENNReal.ofReal (1 / 2))
    (hmright : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici m) = ENNReal.ofReal (1 / 2)) :
    (∫⁻ x, ENNReal.ofReal ((h x - ∫ y, h y
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ≤
      ENNReal.ofReal (1 / (f m) ^ 2) * ∫⁻ x, ENNReal.ofReal ((deriv h x) ^ 2)
        ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hfm0 : ENNReal.ofReal (f m) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hfm)
  have hcancel (t : ℝ) :
      ENNReal.ofReal (1 / (2 * f m)) * ENNReal.ofReal (f t) * ENNReal.ofReal (f m) =
        ENNReal.ofReal (f t) * ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * f m)),
      ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (hnn _)),
      ← ENNReal.ofReal_mul (hnn _)]
    congr 1
    field_simp
  have hleft (t : ℝ) (ht : t ∈ Iic m) :
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic t) ≤
        ENNReal.ofReal (1 / (2 * f m)) * ENNReal.ofReal (f t) := by
    apply (ENNReal.mul_le_mul_iff_left hfm0 ENNReal.ofReal_ne_top).mp
    rw [hcancel]
    have he := lower_tail_mul_le hf hnn hlog ht
    rw [hmleft] at he
    simpa only [mul_comm] using he
  have hright (t : ℝ) (ht : t ∈ Ici m) :
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici t) ≤
        ENNReal.ofReal (1 / (2 * f m)) * ENNReal.ofReal (f t) := by
    apply (ENNReal.mul_le_mul_iff_left hfm0 ENNReal.ofReal_ne_top).mp
    rw [hcancel]
    have he := upper_tail_mul_le hf hnn hlog ht
    rw [hmright] at he
    simpa only [mul_comm] using he
  have hcoef : 4 * (1 / (2 * f m)) ^ 2 = 1 / (f m) ^ 2 := by
    field_simp
    ring
  simpa only [hcoef] using poincare_of_tail_bounds_internal hf hprob
    (hh.of_le (by norm_num)) hL2 hdL2 m
      (by positivity : 0 ≤ 1 / (2 * f m)) hleft hright

/-- A log-concave probability density has a median in its positive
support. Both closed rays have exactly half the mass. This uses the
given density representative, without choosing an a.e. replacement. -/
theorem exists_positive_density_median {f : ℝ → ℝ} (hf : Measurable f)
    (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    ∃ m : ℝ, 0 < f m ∧
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic m) = ENNReal.ofReal (1 / 2) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici m) = ENNReal.ofReal (1 / 2) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsProbabilityMeasure μ := hprob
  have hs : Function.support f = {x | 0 < f x} := by
    ext x
    simp only [Function.mem_support, mem_ofPred_eq]
    exact ne_comm.trans (hnn x).lt_iff_ne.symm
  have hlogs := hlog
  rw [← hs] at hlogs
  obtain ⟨hfi, _⟩ := GeneralLogConcaveSurvival.probability_density_log_survival
    μ hf hnn hlogs rfl
  let S := fun t => ∫ x in Ici t, f x
  have hS : Continuous S := by
    rw [continuous_iff_continuousAt]
    intro t
    have hc : ContinuousOn S (Ici (t - 1)) := hfi.integrableOn.continuousOn_Ici_primitive_Ici
    exact hc.continuousAt (Ici_mem_nhds (by linarith : t - 1 < t))
  have htail (t : ℝ) : (μ (Ici t)).toReal = S t := by
    rw [withDensity_apply _ measurableSet_Ici,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (ae_of_all _ hnn),
      ENNReal.toReal_ofReal (integral_nonneg hnn)]
  have hbot : Filter.Tendsto S Filter.atBot (𝓝 1) := by
    have ht := (ENNReal.tendsto_toReal (measure_ne_top μ univ)).comp
      (tendsto_measure_Ici_atBot μ)
    change Filter.Tendsto (fun t => (μ (Ici t)).toReal) Filter.atBot
      (𝓝 ((μ univ).toReal)) at ht
    simpa only [htail, measure_univ, ENNReal.toReal_one] using ht
  have htop : Filter.Tendsto S Filter.atTop (𝓝 0) :=
    tendsto_integral_Ici_zero (μ := volume) (f := f) Filter.tendsto_id
  obtain ⟨lo, hlo⟩ := (htop.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  obtain ⟨hi, hhi⟩ := (hbot.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
  obtain ⟨m, hm⟩ := mem_range_of_exists_le_of_exists_ge hS
    ⟨lo, le_of_lt hlo⟩ ⟨hi, le_of_lt hhi⟩
  have hmright : μ (Ici m) = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (Ici m)), htail, hm]
  have hmleft : μ (Iic m) = ENNReal.ofReal (1 / 2) := by
    have he := lintegral_halfline_add μ (fun _ => 1) m
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, measure_univ] at he
    rw [hmright] at he
    have hr := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top] at hr
    norm_num at hr
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  have hpoint (D : Set ℝ) (hD : MeasurableSet D) (hμD : μ D = ENNReal.ofReal (1 / 2)) :
      ∃ x ∈ D, 0 < f x := by
    by_contra hn
    have he : μ D = 0 := by
      rw [withDensity_apply _ hD]
      apply (lintegral_eq_zero_iff hf.ennreal_ofReal).mpr
      filter_upwards [ae_restrict_mem hD] with x hx
      have hfx : f x ≤ 0 := le_of_not_gt (fun hp => hn ⟨x, hx, hp⟩)
      exact ENNReal.ofReal_eq_zero.mpr hfx
    rw [hμD] at he
    norm_num at he
  obtain ⟨l, hl, hfl⟩ := hpoint (Iic m) measurableSet_Iic hmleft
  obtain ⟨r, hr, hfr⟩ := hpoint (Ici m) measurableSet_Ici hmright
  have hseg : m ∈ segment ℝ l r := by
    rw [segment_eq_Icc (le_trans hl hr)]
    exact ⟨hl, hr⟩
  exact ⟨m, hlog.1.segment_subset hfl hfr hseg, hmleft, hmright⟩

/-- Supporting theorem for one-dimensional log-concavity estimates:
every density satisfying the log-concavity premises has a
positive-density median and smooth Poincaré coefficient `1 / f(m)²`.
The conversion of this coefficient to `12` times the variance is a
separate sharp estimate, not a hypothesis of this theorem. -/
theorem exists_median_poincare (f : ℝ → ℝ) (hf : Measurable f)
    (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hmass : (∫⁻ x, ENNReal.ofReal (f x)) = 1) :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
    ∃ m : ℝ, 0 < f m ∧ μ (Iic m) = ENNReal.ofReal (1 / 2) ∧
      μ (Ici m) = ENNReal.ofReal (1 / 2) ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → MemLp h 2 μ → MemLp (deriv h) 2 μ →
        (∫⁻ x, ENNReal.ofReal ((h x - ∫ y, h y ∂μ) ^ 2) ∂μ) ≤
          ENNReal.ofReal (1 / (f m) ^ 2) * ∫⁻ x, ENNReal.ofReal ((deriv h x) ^ 2) ∂μ := by
  dsimp only
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hprob : IsProbabilityMeasure μ := ⟨by
    simpa only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hmass⟩
  obtain ⟨m, hfm, hl, hr⟩ := exists_positive_density_median hf hnn hlog hprob
  exact ⟨m, hfm, hl, hr, fun h hh hL2 hdL2 =>
    poincare_of_median_internal hf hnn hlog hprob hh hL2 hdL2 m hfm hl hr⟩

end Riesz2.LogConcavePoincare

end
