/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ConvergesInLawAlong
public import Riesz2.ToMathlib.GeneralLogConcaveSurvival
public import Riesz2.ToMathlib.LogConcaveQuantileTail
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Quantiles and survival functions of log-concave laws

Weak convergence gives common quarter-quantile bounds. Reflection of a
log-concave density and its upper survival function then gives a global
exponential tail. The closed-set Portmanteau inequality avoids any boundary
regularity assumption on the limiting law.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace Riesz2.WeakLogConcaveMoments

/-- Every finite real measure has arbitrarily small two-sided tails. -/
theorem exists_small_abs_tail (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∃ A : ℝ, 0 < A ∧ ν {x : ℝ | A ≤ |x|} < ENNReal.ofReal (1 / 8) := by
  let E : ℕ → Set ℝ := fun n => {x | (n : ℝ) ≤ |x|}
  have hE : Antitone E := by
    intro m n hmn x hx
    exact le_trans (show (m : ℝ) ≤ n by exact_mod_cast hmn) hx
  have hempty : (⋂ n, E n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact (not_le.mpr hn) (mem_iInter.mp hx n)
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (isClosed_le continuous_const continuous_abs).measurableSet.nullMeasurableSet)
    hE ⟨0, measure_ne_top ν _⟩
  rw [hempty, measure_empty] at ht
  have hev := ht.eventually (eventually_lt_nhds
    (show (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 8) by norm_num))
  obtain ⟨n, hn, hnpos⟩ := (hev.and (eventually_ge_atTop 1)).exists
  exact ⟨n, by exact_mod_cast hnpos, hn⟩

/-- Weak convergence supplies common quarter-quantile bounds, with no
assumption that the limit has a density. -/
theorem eventually_quarter_quantiles {ι : Type*} {l : Filter ι}
    {μ : ι → Measure ℝ} {ν : Measure ℝ} (hw : ConvergesInLawAlong l μ ν) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ i in l,
      3 / 4 ≤ (μ i (Ici (-A))).toReal ∧
      (μ i (Ici A)).toReal ≤ 1 / 4 ∧
      3 / 4 ≤ (μ i (Iic A)).toReal ∧
      (μ i (Iic (-A))).toReal ≤ 1 / 4 := by
  have : ∀ i, IsProbabilityMeasure (μ i) := hw.1
  have : IsProbabilityMeasure ν := hw.2.1
  obtain ⟨A, hA, htail⟩ := exists_small_abs_tail ν
  let m : ι → ProbabilityMeasure ℝ := fun i => ⟨μ i, hw.1 i⟩
  let v : ProbabilityMeasure ℝ := ⟨ν, hw.2.1⟩
  have hm : Tendsto m l (𝓝 v) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hw.2.2
  have hclosed : IsClosed {x : ℝ | A ≤ |x|} :=
    isClosed_le continuous_const continuous_abs
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hm hclosed
  have hev : ∀ᶠ i in l, μ i {x : ℝ | A ≤ |x|} < ENNReal.ofReal (1 / 4) :=
    eventually_lt_of_limsup_lt (hlim.trans_lt (htail.trans (by norm_num)))
      (by isBoundedDefault)
  refine ⟨A, hA, hev.mono fun i hi => ?_⟩
  have hR : (μ i (Ici A)).toReal ≤ 1 / 4 := by
    have hb : μ i (Ici A) ≤ ENNReal.ofReal (1 / 4) :=
      (measure_mono fun x hx => hx.trans (le_abs_self x)).trans hi.le
    simpa using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hL : (μ i (Iic (-A))).toReal ≤ 1 / 4 := by
    have hb : μ i (Iic (-A)) ≤ ENNReal.ofReal (1 / 4) :=
      (measure_mono fun x (hx : x ≤ -A) =>
        (show A ≤ -x by linarith).trans (neg_le_abs x)).trans hi.le
    simpa using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hcover (a : ℝ) :
      1 ≤ (μ i (Ici a)).toReal + (μ i (Iic a)).toReal := by
    have hu : Ici a ∪ Iic a = univ := by
      ext x
      simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
      exact le_total a x
    have h := measure_union_le (μ := μ i) (Ici a) (Iic a)
    rw [hu, measure_univ] at h
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h
    simpa only [ENNReal.toReal_one, ENNReal.toReal_add
      (measure_ne_top _ _) (measure_ne_top _ _)] using ht
  exact ⟨by linarith [hcover (-A)], hR, by linarith [hcover A], hL⟩

/-- Reflection of a log-concave probability density gives concavity of
the logarithm of its actual lower-ray probabilities. -/
theorem probability_density_log_lower_survival (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ (Function.support f) (fun x => Real.log (f x)))
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ConcaveOn ℝ {t | 0 < (μ (Iic (-t))).toReal}
      (fun t => Real.log ((μ (Iic (-t))).toReal)) := by
  have hfi := (GeneralLogConcaveSurvival.probability_density_log_survival μ hf hnn hlog hμ).1
  have hneg : Integrable (fun x : ℝ => f (-x)) := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp
      hf.aestronglyMeasurable |>.mpr hfi
  have hlogneg : ConcaveOn ℝ (Function.support (fun x : ℝ => f (-x)))
      (fun x => Real.log (f (-x))) := by
    exact hlog.comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have h := GeneralLogConcaveSurvival.concaveOn_log_survival
    (hf.comp measurable_neg) hneg (fun x => hnn (-x)) hlogneg
  have heq (t : ℝ) : (μ (Iic (-t))).toReal = ∫ x in Ici t, f (-x) := by
    rw [hμ, withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
        (Eventually.of_forall hnn),
      ENNReal.toReal_ofReal (integral_nonneg fun x => hnn x),
      integral_Ici_eq_integral_Ioi, integral_comp_neg_Ioi]
  simpa only [heq, Function.comp_def] using h

/-- The two quarter-quantiles give a global exponential tail, including
thresholds below the quantile cutoff. -/
theorem global_tail_of_quarter_quantiles (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hlogR : ConcaveOn ℝ {x | 0 < (μ (Ici x)).toReal}
      (fun x => Real.log ((μ (Ici x)).toReal)))
    (hlogL : ConcaveOn ℝ {x | 0 < (μ (Iic (-x))).toReal}
      (fun x => Real.log ((μ (Iic (-x))).toReal)))
    {A : ℝ} (hA : 0 < A)
    (hRL : 3 / 4 ≤ (μ (Ici (-A))).toReal)
    (hRR : (μ (Ici A)).toReal ≤ 1 / 4)
    (hLL : 3 / 4 ≤ (μ (Iic A)).toReal)
    (hLR : (μ (Iic (-A))).toReal ≤ 1 / 4) :
    ∀ t : ℝ, 0 < t → μ {x : ℝ | t ≤ |x|} ≤
      ENNReal.ofReal (Real.exp ((Real.log 3 / (2 * A)) * A) *
        Real.exp (-(Real.log 3 / (2 * A)) * t)) := by
  let c := Real.log 3 / (2 * A)
  have hc : 0 < c := LogConcaveQuantileTail.quarter_quantile_rate_pos hA
  intro t _
  by_cases ht : A ≤ t
  · have h := LogConcaveQuantileTail.measure_abs_ge_le_internal μ hlogR hlogL
      hA hRL hRR hLL hLR ht
    apply h.trans (ENNReal.ofReal_le_ofReal _)
    have he : -(t - A) * Real.log 3 / (2 * A) = c * A + -c * t := by dsimp [c]; ring
    rw [he, Real.exp_add]
    nlinarith [Real.exp_pos (c * A), Real.exp_pos (-c * t)]
  · apply (prob_le_one (μ := μ)).trans
    rw [← Real.exp_add]
    have he : 1 ≤ Real.exp (c * A + -c * t) := Real.one_le_exp (by nlinarith)
    exact_mod_cast ENNReal.ofReal_le_ofReal he

end Riesz2.WeakLogConcaveMoments

end
