/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.RemovableGapBarrierPart2
public import Riesz2.Bridges.CyclicLabels
public import Riesz2.ToMathlib.LogConcaveBarrierTail
public import Riesz2.ToMathlib.ExponentialPowerMoments
public import Riesz2.ToMathlib.TailPowerMoments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Uniform single-gap tails and moments

See Lemma 2.1 of the paper and its proof. The estimates apply to the
particle law and microscopic gaps in both exponent regimes. Constants
precede volume, label, and temperature inside a compact positive
temperature interval.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.SingleGapTails

private theorem gap_mean (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    Integrable (fun X : Riesz1.Configuration N => gap X j) (gibbsMeasure p N) ∧
      (∫ X, gap X j ∂gibbsMeasure p N) = 1 := by
  have hV : Measurable (@gapVector N) := Riesz1.measurable_gapVector N
  have h := RemovableGapBarrier.gap_mean_one p N hN (Riesz1.labelOf N j)
  rw [gapLaw] at h
  have hi := (integrable_map_measure (measurable_pi_apply _).aestronglyMeasurable
    hV.aemeasurable).mp h.1
  have he := h.2
  rw [integral_map hV.aemeasurable (measurable_pi_apply _).aestronglyMeasurable] at he
  refine ⟨hi.congr (Filter.Eventually.of_forall (fun X => (gap_eq_gapVector_labelOf X j).symm)), ?_⟩
  simpa only [← gap_eq_gapVector_labelOf] using he

private theorem density_data (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    ∃ f h : ℝ → ℝ,
      (gibbsMeasure p N).map (fun X => gap X j) =
        volume.withDensity (fun u => ENNReal.ofReal (f u)) ∧
      Measurable f ∧ (∀ u, 0 ≤ f u) ∧
      (∀ u ∉ Ioo (0 : ℝ) (N : ℝ), f u = 0) ∧
      (∀ u ∈ Ioo (0 : ℝ) (N : ℝ), 0 < f u ∧ 0 < h u) ∧
      (∀ u ∈ Ioo (0 : ℝ) (N : ℝ),
        f u = Real.exp (-(2 * p.val.1) * u ^ (-p.val.2)) * h u) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (N : ℝ)) (fun u => Real.log (f u)) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (N : ℝ)) (fun u => Real.log (h u)) ∧
      Integrable f ∧ Integrable (fun u => u * f u) ∧
      (∫ u, f u) = 1 ∧ (∫ u, u * f u) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat :=
    ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  let N := (n + 1).succPNat
  obtain ⟨f, h, hlaw, hf, hp, hfac, hlog, hhlog⟩ := RemovableGapBarrier.gap_density p n j
  have hcast : (N : ℝ) = n + 2 := by
    simp only [N, Nat.succPNat_coe, Nat.cast_succ]; ring
  rw [← hcast] at hlaw hf hp hfac hlog hhlog
  change (gibbsMeasure p N).map (fun X => gap X j) = _ at hlaw
  let F := (Ioo (0 : ℝ) (N : ℝ)).indicator f
  have hFm : Measurable F := Riesz1.measurable_indicator_of_continuousOn isOpen_Ioo hf
  have hFp (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) (N : ℝ)) : 0 < F u := by
    simpa only [F, indicator_of_mem hu] using (hp u hu).1
  have hFz (u : ℝ) (hu : u ∉ Ioo (0 : ℝ) (N : ℝ)) : F u = 0 := indicator_of_notMem hu f
  have hFn := Riesz1.logConcave_nonneg hFp hFz
  have hlawF : (gibbsMeasure p N).map (fun X => gap X j) =
      volume.withDensity (fun u => ENNReal.ofReal (F u)) := by
    rw [hlaw, ← withDensity_indicator measurableSet_Ioo]
    congr 1
    funext u
    by_cases hu : u ∈ Ioo (0 : ℝ) (N : ℝ) <;> simp [F, hu]
  have hprob := gibbsMeasure_probability p N
  have hmassE : ∫⁻ u, ENNReal.ofReal (F u) = 1 := by
    rw [← Measure.restrict_univ (μ := volume), ← withDensity_apply _ MeasurableSet.univ,
      ← hlawF, measure_univ]
  have hFi : Integrable F := ⟨hFm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hFn)).mpr
      (hmassE.trans_lt ENNReal.one_lt_top)⟩
  have htransfer (g : ℝ → ℝ) (hg : Measurable g) :
      (∫ X : Riesz1.Configuration N, g (gap X j) ∂gibbsMeasure p N) =
        ∫ u, g u * F u := by
    rw [← integral_map (show Measurable (fun X : Riesz1.Configuration N => gap X j) from Riesz1.measurable_gap j).aemeasurable hg.aestronglyMeasurable, hlawF,
      integral_withDensity_eq_integral_toReal_smul hFm.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hFn _), smul_eq_mul, mul_comm]
  have hmean : ∫ u, u * F u = 1 :=
    (htransfer id measurable_id).symm.trans (gap_mean p N hN j).2
  have hxFi : Integrable (fun u => u * F u) := Integrable.of_integral_ne_zero (by rw [hmean]; norm_num)
  have hmass : ∫ u, F u = 1 := by simpa using (htransfer (fun _ => 1) measurable_const).symm
  refine ⟨F, h, hlawF, hFm, hFn, hFz, fun u hu => ⟨hFp u hu, (hp u hu).2⟩,
    ?_, ?_, hhlog, hFi, hxFi, hmass, hmean⟩
  · intro u hu
    rw [show F u = f u from indicator_of_mem hu f]
    exact hfac u hu
  · exact hlog.congr (fun u hu => congrArg Real.log (indicator_of_mem hu f).symm)

/-- Exponential integrability.
This holds in both regimes with numerical
constants independent even of temperature and exponent. -/
theorem exponential_moment (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    Integrable (fun X : Riesz1.Configuration N => Real.exp (Real.log 2 / 4 * gap X j))
      (gibbsMeasure p N) ∧
    (∫ X, Real.exp (Real.log 2 / 4 * gap X j) ∂gibbsMeasure p N) ≤ 3 := by
  obtain ⟨f, _, hlaw, hfm, hfn, hfz, hfp, _, hlog, _, hfi, _, hmass, hmean⟩ :=
    density_data p N hN j
  have he := Riesz1.logConcave_exp_moment_le (by exact_mod_cast N.pos) f
    (fun u hu => (hfp u hu).1) hfz hlog hmass hmean
  have hm : Measurable (fun u : ℝ => Real.exp (Real.log 2 / 4 * u)) := by fun_prop
  have hi : Integrable (fun u : ℝ => Real.exp (Real.log 2 / 4 * u))
      (volume.withDensity (fun u => ENNReal.ofReal (f u))) := by
    rw [integrable_withDensity_iff_integrable_smul' hfm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul, mul_comm] using he.1
  rw [← hlaw] at hi
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable (show Measurable (fun X : Riesz1.Configuration N => gap X j) from Riesz1.measurable_gap j).aemeasurable).mp hi, ?_⟩
  rw [← integral_map (show Measurable (fun X : Riesz1.Configuration N => gap X j) from Riesz1.measurable_gap j).aemeasurable hm.aestronglyMeasurable, hlaw,
    integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul, mul_comm] using he.2

/-- A uniform inverse exponential moment, with constants chosen before
all temperatures in a compact positive interval, volumes, and labels.
This follows from the residual bound in the proof of Lemma 2.1. -/
theorem inverse_exponential_moment (s βlo βhi : ℝ) (hs : 0 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
      Integrable (fun X : Riesz1.Configuration N => Real.exp (βlo * gap X j ^ (-s)))
        (gibbsMeasure p N) ∧
      (∫ X, Real.exp (βlo * gap X j ^ (-s)) ∂gibbsMeasure p N) ≤ A := by
  obtain ⟨B, hB, hbound⟩ := BarrierTail.exists_residual_bound hs
    (show 0 ≤ 2 * βhi by linarith)
  refine ⟨B / 4 + Real.exp (βlo * (4 : ℝ) ^ s), by positivity, ?_⟩
  intro p hps hpl hph N hN j
  obtain ⟨f, h, hlaw, hfm, hfn, hfz, hfp, hfac, hlog, hhlog, hfi, hxfi, hmass, hmean⟩ :=
    density_data p N hN j
  rw [hps] at hfac
  have hgapm : Measurable (fun X : Riesz1.Configuration N => gap X j) := Riesz1.measurable_gap j
  have hbb := hbound (by exact_mod_cast hN)
    (show 0 ≤ 2 * p.val.1 from mul_nonneg (by norm_num) p.property.1.le)
    (show 2 * p.val.1 ≤ 2 * βhi by linarith) hfm hfn (fun u hu => (hfp u hu).1)
    hfz hlog hfi hxfi hmass hmean (fun u hu => (hfp u hu).2) hfac hhlog
  have hinv := BarrierTail.inverse_exponential_integral hs hlo.le
    (show βlo ≤ 2 * p.val.1 by linarith) hB.le hfm hfn hfz hfi hmass hfac
    (fun u hu hu4 => hbb u hu (by linarith))
  have hm : Measurable (fun u : ℝ => Real.exp (βlo * u ^ (-s))) := by fun_prop
  have himap : Integrable (fun u : ℝ => Real.exp (βlo * u ^ (-s)))
      ((gibbsMeasure p N).map (fun X => gap X j)) := by
    rw [hlaw, integrable_withDensity_iff hfm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hfn _)] using hinv.1
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable hgapm.aemeasurable).mp himap, ?_⟩
  rw [← integral_map hgapm.aemeasurable hm.aestronglyMeasurable, hlaw,
    integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul, mul_comm] using hinv.2

/-- The paper's lower tail: bound the residual at one half by the
survival tangent and the slope/mean contradiction, then integrate the density. -/
private theorem lower_tail (s βlo βhi : ℝ) (hs : 0 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
      ∀ u : ℝ, 0 < u → u ≤ 1 →
        (gibbsMeasure p N) {X | gap X j ≤ u} ≤
          ENNReal.ofReal (A * Real.exp (-βlo * u ^ (-s))) := by
  obtain ⟨B, hB, hbound⟩ := BarrierTail.exists_residual_bound hs
    (show 0 ≤ 2 * βhi by linarith)
  refine ⟨B + Real.exp (βlo * (2 : ℝ) ^ s), by positivity, ?_⟩
  intro p hps hpl hph N hN j u hu hu1
  obtain ⟨f, h, hlaw, hfm, hfn, hfz, hfp, hfac, hlog, hhlog, hfi, hxfi, hmass, hmean⟩ :=
    density_data p N hN j
  rw [hps] at hfac
  have hbb := hbound (by exact_mod_cast hN)
    (show 0 ≤ 2 * p.val.1 from mul_nonneg (by norm_num) p.property.1.le)
    (show 2 * p.val.1 ≤ 2 * βhi by linarith) hfm hfn (fun v hv => (hfp v hv).1)
    hfz hlog hfi hxfi hmass hmean (fun v hv => (hfp v hv).2) hfac hhlog
  have ht := BarrierTail.lower_tail_integral hs hlo.le
    (show βlo ≤ 2 * p.val.1 by linarith) hB.le hfn hfz hfi hmass hfac hbb u hu hu1
  have he : (gibbsMeasure p N) {X | gap X j ≤ u} =
      ENNReal.ofReal (∫ v in Iic u, f v) := by
    have hgapm : Measurable (fun X : Riesz1.Configuration N => gap X j) := Riesz1.measurable_gap j
    change (gibbsMeasure p N) ((fun X => gap X j) ⁻¹' Iic u) = _
    rw [← Measure.map_apply hgapm measurableSet_Iic, hlaw,
      withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
        (Filter.Eventually.of_forall hfn)]
  rw [he]
  exact ENNReal.ofReal_le_ofReal ht

private theorem upper_tail (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ)
    (u : ℝ) (hu : 0 ≤ u) :
    (gibbsMeasure p N) {X | u ≤ gap X j} ≤
      ENNReal.ofReal (2 * Real.exp (-(Real.log 2) * u / 2)) := by
  obtain ⟨f, _, hlaw, hfm, hfn, hfz, hfp, _, hlog, _, hfi, _, hmass, hmean⟩ :=
    density_data p N hN j
  -- This library proof uses Markov at 2 and concavity of log survival
  -- between 0, 2, and u, including the zero tail beyond the support.
  have ht := Riesz1.logConcave_survival_le (by exact_mod_cast N.pos) f
    (fun v hv => (hfp v hv).1) hfz hlog hmass hmean u hu
  have he : (gibbsMeasure p N) {X | u ≤ gap X j} =
      ENNReal.ofReal (∫ v in Ici u, f v) := by
    have hgapm : Measurable (fun X : Riesz1.Configuration N => gap X j) := Riesz1.measurable_gap j
    change (gibbsMeasure p N) ((fun X => gap X j) ⁻¹' Ici u) = _
    rw [← Measure.map_apply hgapm measurableSet_Ici, hlaw,
      withDensity_apply _ measurableSet_Ici,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
        (Filter.Eventually.of_forall hfn)]
  rw [he]
  exact ENNReal.ofReal_le_ofReal ht

/-- See the proof of Lemma 2.1 in the paper: both one-gap tails,
uniform over every closed positive temperature interval, every volume
`N ≥ 2` and every integer label, in both exponent regimes. -/
theorem single_gap_tails_density (s βlo βhi : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
      (∀ u : ℝ, 0 < u → u ≤ 1 →
        (gibbsMeasure p N) {X | gap X j ≤ u} ≤
          ENNReal.ofReal (C * Real.exp (-c * u ^ (-s)))) ∧
      (∀ u : ℝ, 1 ≤ u →
        (gibbsMeasure p N) {X | u ≤ gap X j} ≤
          ENNReal.ofReal (C * Real.exp (-c * u))) := by
  let d := Real.log 2 / 4
  have hd : 0 < d := div_pos (Real.log_pos one_lt_two) (by norm_num)
  obtain ⟨A, hA, htail⟩ := lower_tail s βlo βhi hs hlo hle
  let C := max A 3
  let c := min βlo d
  have hC : 0 < C := lt_of_lt_of_le hA (le_max_left _ _)
  have hc : 0 < c := lt_min hlo hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro p hps hpl hph N hN j
  have := gibbsMeasure_probability p N
  constructor
  · intro u hu hu1
    have ht := htail p hps hpl hph N hN j u hu hu1
    refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul (le_max_left A 3)
    · exact Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right (min_le_left βlo d) (Real.rpow_nonneg hu.le (-s))
        linarith)
    · exact (Real.exp_pos _).le
    · exact hC.le
  · intro u hu
    have ht := upper_tail p N hN j u (by linarith)
    refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul (show (2 : ℝ) ≤ C by dsimp [C]; linarith [le_max_right A 3])
    · exact Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right (min_le_right βlo d) (show 0 ≤ u by linarith)
        have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
        dsimp [d] at hh
        dsimp [c, d]
        nlinarith [mul_nonneg hlog.le (by linarith : 0 ≤ u)])
    · exact (Real.exp_pos _).le
    · exact hC.le

/-- See Lemma 2.1 of the paper, the positive and inverse power
norm bounds. The same constant works for every real norm exponent
`q ≥ 1`, all volumes and labels, and the whole temperature interval. -/
theorem single_gap_moments (s βlo βhi : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (r : ℝ) (hr : 0 < r) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
      ∀ q : ℝ, 1 ≤ q →
      eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ r) (ENNReal.ofReal q) (gibbsMeasure p N) +
        eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ (-r)) (ENNReal.ofReal q) (gibbsMeasure p N) ≤
          ENNReal.ofReal (Cr * (q ^ r + q ^ (r / s))) ∧
      Cr * (q ^ r + q ^ (r / s)) ≤ 2 * Cr * q ^ (max r (r / s)) := by
  obtain ⟨C, c, hC, hc, ht⟩ := single_gap_tails_density s βlo βhi hs _hs1 hlo hle
  let D := max C (Real.exp c)
  have hD : 0 < D := lt_of_lt_of_le hC (le_max_left _ _)
  let Kp := max (2 * D) 1 * (2 * r / (Real.exp 1 * c)) ^ r
  let Ki := max (2 * D) 1 * (2 * (r / s) / (Real.exp 1 * c)) ^ (r / s)
  have hKp : 0 < Kp := by dsimp [Kp]; positivity
  have hKi : 0 < Ki := by dsimp [Ki]; positivity
  refine ⟨Kp + Ki, by positivity, ?_⟩
  intro p hps hpl hph N hN j q hq
  have hm : Measurable (fun X : Riesz1.Configuration N => gap X j) := Riesz1.measurable_gap j
  have hpos (X : Riesz1.Configuration N) : 0 < gap X j := Riesz1.gap_pos X j
  have := gibbsMeasure_probability p N
  have htail := ht p hps hpl hph N hN j
  have hp := TailPower.power_eLpNorm_le hm (fun X => (hpos X).le) hD.le hc hr
    (TailPower.extend_tail hc htail.2) hq
  have hnegative : ∀ v : ℝ, 1 ≤ v →
      (gibbsMeasure p N) {X | v ≤ gap X j ^ (-s)} ≤ ENNReal.ofReal (C * Real.exp (-c * v)) := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
    have hvpow : 0 < v ^ (-1 / s) := Real.rpow_pos_of_pos hv0 _
    have hv1 : v ^ (-1 / s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hs.le)
    have hcancel : (v ^ (-1 / s)) ^ (-s) = v := by
      rw [← Real.rpow_mul hv0.le]
      have he : (-1 / s) * (-s) = (1 : ℝ) := by field_simp
      rw [he, Real.rpow_one]
    have hset : {X : Riesz1.Configuration N | v ≤ gap X j ^ (-s)} =
        {X | gap X j ≤ v ^ (-1 / s)} := by
      ext X
      have hh := Real.rpow_le_rpow_iff_of_neg hvpow (hpos X) (neg_neg_of_pos hs)
      rwa [hcancel] at hh
    rw [hset]
    simpa only [hcancel] using htail.1 (v ^ (-1 / s)) hvpow hv1
  have hinv := TailPower.power_eLpNorm_le (hm.pow_const (-s))
    (fun X => Real.rpow_nonneg (hpos X).le (-s)) hD.le hc (div_pos hr hs)
    (TailPower.extend_tail hc hnegative) hq
  have hpow (X : Riesz1.Configuration N) : (gap X j ^ (-s)) ^ (r / s) = gap X j ^ (-r) := by
    rw [← Real.rpow_mul (hpos X).le]
    congr 1
    field_simp
  simp_rw [hpow] at hinv
  have hsum := add_le_add hp hinv
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqp : 0 ≤ q ^ r := Real.rpow_nonneg hq0.le _
  have hqi : 0 ≤ q ^ (r / s) := Real.rpow_nonneg hq0.le _
  constructor
  · refine hsum.trans ?_
    change ENNReal.ofReal (Kp * q ^ r) + ENNReal.ofReal (Ki * q ^ (r / s)) ≤ _
    rw [← ENNReal.ofReal_add (mul_nonneg hKp.le hqp) (mul_nonneg hKi.le hqi)]
    apply ENNReal.ofReal_le_ofReal
    change Kp * q ^ r + Ki * q ^ (r / s) ≤ (Kp + Ki) * (q ^ r + q ^ (r / s))
    nlinarith [mul_nonneg hKp.le hqi, mul_nonneg hKi.le hqp]
  · have hpmax := Real.rpow_le_rpow_of_exponent_le hq (le_max_left r (r / s))
    have himax := Real.rpow_le_rpow_of_exponent_le hq (le_max_right r (r / s))
    have hh := mul_le_mul_of_nonneg_left (add_le_add hpmax himax) (show 0 ≤ Kp + Ki by positivity)
    nlinarith

/-- See Lemma 2.1 of the paper, complete statement: uniform lower
and upper tails and every positive and inverse power norm, with both
inequalities of the displayed moment estimate. Temperature uniformity is
expressed on an arbitrary closed positive interval, including singletons. -/
theorem single_gap_tails (s βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
        (∀ u : ℝ, 0 < u → u ≤ 1 →
          (gibbsMeasure p N) {X | gap X j ≤ u} ≤
            ENNReal.ofReal (C * Real.exp (-c * u ^ (-s)))) ∧
        (∀ u : ℝ, 1 ≤ u →
          (gibbsMeasure p N) {X | u ≤ gap X j} ≤
            ENNReal.ofReal (C * Real.exp (-c * u)))) ∧
      ∀ r : ℝ, 0 < r → ∃ Cr : ℝ, 0 < Cr ∧
        ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ, ∀ q : ℝ, 1 ≤ q →
        eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ r) (ENNReal.ofReal q) (gibbsMeasure p N) +
          eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ (-r)) (ENNReal.ofReal q) (gibbsMeasure p N) ≤
            ENNReal.ofReal (Cr * (q ^ r + q ^ (r / s))) ∧
        Cr * (q ^ r + q ^ (r / s)) ≤ 2 * Cr * q ^ (max r (r / s)) := by
  obtain ⟨C, c, hC, hc, ht⟩ := single_gap_tails_density s βlo βhi hs hs1 hlo hle
  exact ⟨C, c, hC, hc, ht, single_gap_moments s βlo βhi hs hs1 hlo hle⟩

/-- See Lemma 2.1 of the paper, an integral interface for every
fixed positive and inverse moment. Both integrabilities and a uniform
bound on the sum of nonnegative integrals are explicit. -/
theorem single_gap_moment_integrals (s βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
      Integrable (fun X : Riesz1.Configuration N => gap X j ^ r) (gibbsMeasure p N) ∧
      Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-r)) (gibbsMeasure p N) ∧
      (∫⁻ X : Riesz1.Configuration N, ENNReal.ofReal (gap X j ^ r) ∂gibbsMeasure p N) +
        (∫⁻ X : Riesz1.Configuration N, ENNReal.ofReal (gap X j ^ (-r)) ∂gibbsMeasure p N) ≤
          ENNReal.ofReal D := by
  obtain ⟨Cr, hCr, hb⟩ := single_gap_moments s βlo βhi hs hs1 hlo hle r hr
  refine ⟨Cr * 2, by positivity, ?_⟩
  intro p hps hpl hph N hN j
  have h := (hb p hps hpl hph N hN j 1 le_rfl).1
  simp only [ENNReal.ofReal_one, Real.one_rpow, one_add_one_eq_two] at h
  have hp : eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ r) 1 (gibbsMeasure p N) < ∞ :=
    ((le_add_of_nonneg_right (by positivity)).trans h).trans_lt ENNReal.ofReal_lt_top
  have hn : eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ (-r)) 1 (gibbsMeasure p N) < ∞ :=
    ((le_add_of_nonneg_left (by positivity)).trans h).trans_lt ENNReal.ofReal_lt_top
  have hm : Measurable (fun X : Riesz1.Configuration N => gap X j) := Riesz1.measurable_gap j
  refine ⟨memLp_one_iff_integrable.mp hp, memLp_one_iff_integrable.mp hn, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm (hm.pow_const r).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm (hm.pow_const (-r)).aestronglyMeasurable] at h
  have habs (X : Riesz1.Configuration N) (t : ℝ) : |gap X j ^ t| = gap X j ^ t :=
    abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ gap X j from (Riesz1.gap_pos X j).le) t)
  simpa only [Real.enorm_eq_ofReal_abs, habs] using h

end Riesz2.SingleGapTails
