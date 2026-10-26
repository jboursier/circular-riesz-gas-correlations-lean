/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CountMoments

/-!
# First-particle length bias and cyclic averaging

Steps in Subsection 6.4 and the proof of Corollary 1.1. Sampling uses the suspension
strip, and labelled spans use `gapSequenceSpan`.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local instance stationaryBiasConfigurationMeasurableSpace : MeasurableSpace LineConfiguration :=
  configurationMeasurableSpace
local notation "Gaps" => (ℤ → Ioi (0 : ℝ))

/-- See the proof of Corollary 1.1 in the paper: integrating out the
suspension offset gives exactly the distinguished-gap length bias. -/
theorem suspensionStrip_map_fst (q : Measure reconstructibleGapSequences) [SFinite q] :
    ((q.prod volume).restrict gapSuspensionStrip).map Prod.fst =
      q.withDensity (fun y => ENNReal.ofReal (y.val 0 : ℝ)) := by
  ext E hE
  rw [Measure.map_apply measurable_fst hE, Measure.restrict_apply
    (measurable_fst hE), withDensity_apply _ hE]
  rw [← lintegral_indicator_one ((measurable_fst hE).inter measurableSet_gapSuspensionStrip)]
  change (∫⁻ p, (Prod.fst ⁻¹' E ∩ gapSuspensionStrip).indicator
    (fun _ => (1 : ℝ≥0∞)) p ∂q.prod volume) = _
  rw [lintegral_prod _ (measurable_const.indicator
    ((measurable_fst hE).inter measurableSet_gapSuspensionStrip)).aemeasurable]
  rw [← lintegral_indicator hE]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ E
  · simp only [indicator_of_mem hy]
    have he : (fun u : ℝ => (Prod.fst ⁻¹' E ∩ gapSuspensionStrip).indicator
        (fun _ => (1 : ℝ≥0∞)) (y, u)) =
        (Ico (0 : ℝ) (y.val 0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext u
      by_cases hu : u ∈ Ico (0 : ℝ) (y.val 0 : ℝ)
      · have hm : (y, u) ∈ Prod.fst ⁻¹' E ∩ gapSuspensionStrip := ⟨hy, hu⟩
        simp only [indicator_of_mem hm, indicator_of_mem hu]
      · have hm : (y, u) ∉ Prod.fst ⁻¹' E ∩ gapSuspensionStrip := fun h => hu h.2
        simp only [indicator_of_notMem hm, indicator_of_notMem hu]
    rw [he, lintegral_indicator measurableSet_Ico]
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero, one_mul]
  · simp only [indicator_of_notMem hy]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ fun u => by
      have hm : (y, u) ∉ Prod.fst ⁻¹' E ∩ gapSuspensionStrip := fun h => hy h.1
      exact indicator_of_notMem hm _

/-- See the proof of Corollary 1.1 in the paper: the real expectation
formula for any observable independent of the offset. The formula itself is
valid for every observable. Applications below separately prove integrability. -/
theorem integral_suspensionStrip_independent_offset
    (q : Measure reconstructibleGapSequences) [SFinite q]
    (f : reconstructibleGapSequences → ℝ) (hf : Measurable f) :
    (∫ p, f p.1 ∂(q.prod volume).restrict gapSuspensionStrip) =
      ∫ y, (y.val 0 : ℝ) * f y ∂q := by
  have hw : Measurable (fun y : reconstructibleGapSequences => ENNReal.ofReal (y.val 0 : ℝ)) :=
    (measurable_subtype_coe.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)).ennreal_ofReal
  rw [← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    suspensionStrip_map_fst,
    integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    rw [ENNReal.toReal_ofReal (y.val 0).property.le, smul_eq_mul]

/-- See the proof of Corollary 1.1 in the paper: the spatial image of the
finite sampling strip is the finite periodic spatial law. -/
theorem finite_suspensionStrip_spatial_law (p : Parameters) (N : ℕ+) :
    ((((gibbsMeasure p N).map configurationReconstructionGaps).prod volume).restrict
      gapSuspensionStrip).map gapSuspensionConfiguration = periodicSpatialLaw p N :=
  gapSuspensionMeasure_finite p N

/-- The finite-volume coordinates have square integrability and uniformly
bounded second moments, as consequences of the one-gap theorem. -/
theorem periodicGapLaw_coordinate_second_moments (p : Parameters) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ i : ℤ,
      MemLp (fun y : Gaps => (y i : ℝ)) 2 (periodicGapLaw p N).toMeasure ∧
      (∫ y : Gaps, (y i : ℝ) ^ 2 ∂periodicGapLaw p N) ≤ D := by
  obtain ⟨D, hD, hb⟩ := periodicGapLaw_moment_bound p 2 (by norm_num)
  refine ⟨D, hD, fun N hN i => ?_⟩
  have hm : Measurable (fun y : Gaps => (y i : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply i)
  have he : (∫⁻ y : Gaps, ENNReal.ofReal ((y i : ℝ) ^ (2 : ℝ))
      ∂periodicGapLaw p N) ≤ ENNReal.ofReal D :=
    (le_add_right le_rfl).trans (hb N hN i)
  have ha (y : Gaps) : |(y i : ℝ)| = (y i : ℝ) := abs_of_pos (y i).property
  obtain ⟨hi, hle⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    hm hD.le (by simpa only [ha] using he)
  have hi' : Integrable (fun y : Gaps => (y i : ℝ) ^ 2) (periodicGapLaw p N).toMeasure := by
    simpa only [ha, Real.rpow_two] using hi
  exact ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi',
    by simpa only [ha, Real.rpow_two] using hle⟩

/-- Finite spans inherit square integrability from their actual coordinates. -/
theorem gapSequenceSpan_memLp_two (μ : Measure Gaps) (i : ℤ) (k : ℕ)
    (hcoord : ∀ j : ℤ, MemLp (fun y : Gaps => (y j : ℝ)) 2 μ) :
    MemLp (fun y => gapSequenceSpan y i k) 2 μ :=
  memLp_finsetSum _ fun _ _ => hcoord _

/-- A pair of gap coordinates has integrable product and a common moment
bound, without any independence assumption. -/
theorem gap_coordinate_pair_integral_le_internal (μ : Measure Gaps)
    (hcoord : ∀ j : ℤ, MemLp (fun y : Gaps => (y j : ℝ)) 2 μ)
    (D : ℝ) (hsecond : ∀ j : ℤ, (∫ y : Gaps, (y j : ℝ) ^ 2 ∂μ) ≤ D)
    (i j : ℤ) :
    Integrable (fun y : Gaps => (y i : ℝ) * (y j : ℝ)) μ ∧
      (∫ y : Gaps, (y i : ℝ) * (y j : ℝ) ∂μ) ≤ D := by
  have hi := (hcoord i).integrable_mul (hcoord j)
  have hs j := (memLp_two_iff_integrable_sq (hcoord j).aestronglyMeasurable).mp (hcoord j)
  refine ⟨hi, ?_⟩
  have hb : (∫ y : Gaps, (y i : ℝ) * (y j : ℝ) ∂μ) ≤
      ∫ y : Gaps, ((y i : ℝ) ^ 2 + (y j : ℝ) ^ 2) / 2 ∂μ := by
    apply integral_mono hi (((hs i).add (hs j)).div_const 2)
    intro y
    change (y i : ℝ) * (y j : ℝ) ≤ ((y i : ℝ) ^ 2 + (y j : ℝ) ^ 2) / 2
    nlinarith [sq_nonneg ((y i : ℝ) - (y j : ℝ))]
  rw [integral_div, integral_add (hs i) (hs j)] at hb
  linarith [hsecond i, hsecond j]

/-- See the proof of Corollary 1.1 in the paper, finite averaging inequality.
This general internal helper exposes the exact cyclic integral identity. Its finite-gap application supplies that identity from invariance of the law. -/
theorem length_bias_averaging_internal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y X : ℕ → Ω → ℝ) (h : ℕ) (hh : 0 < h)
    (hY : ∀ i, MemLp (Y i) 2 μ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hYpos : ∀ i ω, 0 ≤ Y i ω) (f : ℝ → ℝ)
    (hf : LipschitzWith 1 f) (hfb : ∀ x, |f x| ≤ 1)
    (hinv : ∀ i < h, (∫ ω, Y i ω * f (X i ω) ∂μ) =
      ∫ ω, Y 0 ω * f (X 0 ω) ∂μ) :
    |(∫ ω, Y 0 ω * f (X 0 ω) ∂μ) - ∫ ω, f (X 0 ω) ∂μ| ≤
      (∫ ω, |(h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1| ∂μ) +
      (h : ℝ)⁻¹ * ∑ i ∈ Finset.range h,
        ∫ ω, Y i ω * |X i ω - X 0 ω| ∂μ := by
  have hhm : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hfm i : AEStronglyMeasurable (fun ω => f (X i ω)) μ :=
    hf.continuous.comp_aestronglyMeasurable (hX i).aestronglyMeasurable
  have hfi i : Integrable (fun ω => f (X i ω)) μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) (hfm i)
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hfb (X i ω))
  have hprod i j : Integrable (fun ω => Y i ω * f (X j ω)) μ := by
    apply ((hY i).integrable (by norm_num)).abs.mono'
      ((hY i).aestronglyMeasurable.mul (hfm j))
    exact ae_of_all _ fun ω => by
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hfb _)
  have hdiff i : Integrable (fun ω => Y i ω * (f (X i ω) - f (X 0 ω))) μ := by
    apply ((hprod i i).sub (hprod i 0)).congr
    exact ae_of_all _ fun ω => by
      change Y i ω * f (X i ω) - Y i ω * f (X 0 ω) = Y i ω * (f (X i ω) - f (X 0 ω))
      ring
  have herr i : Integrable (fun ω => Y i ω * |X i ω - X 0 ω|) μ :=
    (hY i).integrable_mul ((hX i).sub (hX 0)).norm
  have hsum : Integrable (fun ω => ∑ i ∈ Finset.range h, Y i ω) μ :=
    integrable_finsetSum _ fun i _ => (hY i).integrable (by norm_num)
  have havg : Integrable (fun ω => (h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1) μ :=
    (hsum.const_mul _).sub (integrable_const _)
  have hmain : Integrable (fun ω =>
      ((h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1) * f (X 0 ω)) μ := by
    apply havg.abs.mono' (havg.aestronglyMeasurable.mul (hfm 0))
    exact ae_of_all _ fun ω => by
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hfb _)
  have hid : (∫ ω, Y 0 ω * f (X 0 ω) ∂μ) - (∫ ω, f (X 0 ω) ∂μ) =
      (∫ ω, ((h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1) * f (X 0 ω) ∂μ) +
      (h : ℝ)⁻¹ * ∑ i ∈ Finset.range h,
        ∫ ω, Y i ω * (f (X i ω) - f (X 0 ω)) ∂μ := by
    have hp : (fun ω => ((h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1) * f (X 0 ω)) =
        (fun ω => (h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω * f (X 0 ω)) - f (X 0 ω)) := by
      ext ω
      rw [← Finset.sum_mul]
      ring
    rw [hp, integral_sub ((integrable_finsetSum _ fun i _ => hprod i 0).const_mul _) (hfi 0),
      integral_const_mul, integral_finsetSum _ (fun i _ => hprod i 0)]
    simp_rw [mul_sub, integral_sub (hprod _ _) (hprod _ _)]
    rw [Finset.sum_sub_distrib]
    have hinvsum : (∑ i ∈ Finset.range h, ∫ ω, Y i ω * f (X i ω) ∂μ) =
        (h : ℝ) * ∫ ω, Y 0 ω * f (X 0 ω) ∂μ := by
      simp only [Finset.sum_congr rfl (fun i hi => hinv i (Finset.mem_range.mp hi)),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hinvsum]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |∫ ω, ((h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1) * f (X 0 ω) ∂μ| +
        |(h : ℝ)⁻¹ * ∑ i ∈ Finset.range h,
          ∫ ω, Y i ω * (f (X i ω) - f (X 0 ω)) ∂μ| := abs_add_le _ _
    _ ≤ (∫ ω, |(h : ℝ)⁻¹ * (∑ i ∈ Finset.range h, Y i ω) - 1| ∂μ) +
        (h : ℝ)⁻¹ * ∑ i ∈ Finset.range h,
          ∫ ω, Y i ω * |X i ω - X 0 ω| ∂μ := by
      apply add_le_add
      · exact abs_integral_le_integral_abs.trans (integral_mono hmain.abs havg.abs fun ω => by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hfb _))
      · rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg h))]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg h))
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        apply abs_integral_le_integral_abs.trans
        apply integral_mono (hdiff i).abs (herr i)
        intro ω
        dsimp only
        rw [abs_mul, abs_of_nonneg (hYpos i ω)]
        apply mul_le_mul_of_nonneg_left _ (hYpos i ω)
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul (X i ω) (X 0 ω)

/-- See the proof of Corollary 1.1 in the paper, its first displayed
inequality on the actual periodic gap law. Scaling is arbitrary. Take
`t = K ^ (-s/2)` for the normalized variable in the paper. -/
theorem periodicGapLaw_length_bias_averaging
    (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K h : ℕ) (hh : 0 < h)
    (t : ℝ) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (hfb : ∀ x, |f x| ≤ 1) :
    |(∫ y : Gaps, (y 0 : ℝ) * f (t * (gapSequenceSpan y 1 K - K)) ∂periodicGapLaw p N) -
        ∫ y : Gaps, f (t * (gapSequenceSpan y 1 K - K)) ∂periodicGapLaw p N| ≤
      (∫ y : Gaps, |(h : ℝ)⁻¹ * gapSequenceSpan y 0 h - 1| ∂periodicGapLaw p N) +
      (h : ℝ)⁻¹ * ∑ i ∈ Finset.range h,
        ∫ y : Gaps, (y (i : ℤ) : ℝ) *
          |t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
            t * (gapSequenceSpan y 1 K - K)| ∂periodicGapLaw p N := by
  obtain ⟨D, _, hcoord⟩ := periodicGapLaw_coordinate_second_moments p
  have hX (i : ℕ) : MemLp (fun y : Gaps =>
      t * (gapSequenceSpan y ((i : ℤ) + 1) K - K)) 2 (periodicGapLaw p N).toMeasure :=
    ((gapSequenceSpan_memLp_two _ _ _ (fun j => (hcoord N hN j).1)).sub
      (memLp_const (K : ℝ))).const_mul t
  have hinv (i : ℕ) :
      (∫ y : Gaps, (y (i : ℤ) : ℝ) *
        f (t * (gapSequenceSpan y ((i : ℤ) + 1) K - K)) ∂periodicGapLaw p N) =
      ∫ y : Gaps, (y 0 : ℝ) * f (t * (gapSequenceSpan y 1 K - K)) ∂periodicGapLaw p N := by
    have hm : Measurable (fun y : Gaps =>
        (y 0 : ℝ) * f (t * (gapSequenceSpan y 1 K - K))) :=
      (measurable_subtype_coe.comp (measurable_pi_apply 0)).mul
        (hf.continuous.measurable.comp
          (((continuous_gapSequenceSpan 1 K).measurable.sub_const _).const_mul _))
    have he := integral_map (μ := (periodicGapLaw p N).toMeasure)
      (gapIndexShift (i : ℤ)).continuous.measurable.aemeasurable hm.aestronglyMeasurable
    have hs := congrArg ProbabilityMeasure.toMeasure (periodicGapLaw_shift_all p N (i : ℤ))
    rw [ProbabilityMeasure.toMeasure_map] at hs
    rw [hs] at he
    simpa only [gapIndexShift_apply, add_zero, gapSequenceSpan, add_assoc] using he.symm
  have hb := length_bias_averaging_internal (periodicGapLaw p N).toMeasure
    (fun i y => (y (i : ℤ) : ℝ))
    (fun i y => t * (gapSequenceSpan y ((i : ℤ) + 1) K - K)) h hh
    (fun i => (hcoord N hN i).1) hX (fun i y => (y _).property.le) f hf hfb
    (fun i _ => hinv i)
  simpa only [Nat.cast_zero, zero_add, gapSequenceSpan] using hb

/-- The difference between two translated spans consists of their two
endpoint blocks. No bound on the span length relative to the period is used. -/
theorem translated_gapSequenceSpan_difference (y : Gaps) (i K : ℕ) :
    gapSequenceSpan y ((i : ℤ) + 1) K - gapSequenceSpan y 1 K =
      gapSequenceSpan y ((K : ℤ) + 1) i - gapSequenceSpan y 1 i := by
  simp only [gapSequenceSpan, ← gapPosition_sub_eq_sum]
  rw [show (i : ℤ) + 1 + K = (K : ℤ) + 1 + i by ring,
    show (1 : ℤ) + K = (K : ℤ) + 1 by ring,
    show (1 : ℤ) + i = (i : ℤ) + 1 by ring]
  ring

/-- See the proof of Corollary 1.1 in the paper: the displacement term
costs only `2 D i t`, from the common second coordinate moment `D`.
The explicit `MemLp` hypotheses make the internal integral estimate valid. -/
theorem weighted_translated_span_difference_le_internal
    (μ : Measure Gaps) (hcoord : ∀ j : ℤ, MemLp (fun y : Gaps => (y j : ℝ)) 2 μ)
    (D : ℝ) (hsecond : ∀ j : ℤ, (∫ y : Gaps, (y j : ℝ) ^ 2 ∂μ) ≤ D)
    (i K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ y : Gaps, (y (i : ℤ) : ℝ) *
      |t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
        t * (gapSequenceSpan y 1 K - K)| ∂μ) ≤ 2 * D * i * t := by
  have hs a k := gapSequenceSpan_memLp_two μ a k hcoord
  have herr : Integrable (fun y : Gaps => (y (i : ℤ) : ℝ) *
      |t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
        t * (gapSequenceSpan y 1 K - K)|) μ := by
    have hd : MemLp (fun y => t * (gapSequenceSpan y ((i : ℤ) + 1) K -
        gapSequenceSpan y 1 K)) 2 μ := ((hs _ _).sub (hs _ _)).const_mul t
    have he : (fun y : Gaps => t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
        t * (gapSequenceSpan y 1 K - K)) =
        (fun y : Gaps => t * (gapSequenceSpan y ((i : ℤ) + 1) K - gapSequenceSpan y 1 K)) := by
      ext y; ring
    apply ((hcoord i).integrable_mul hd.norm).congr
    exact ae_of_all _ fun y => by
      change (y (i : ℤ) : ℝ) * |t * (gapSequenceSpan y ((i : ℤ) + 1) K - gapSequenceSpan y 1 K)| = _
      rw [← congrFun he y]
  have hpair a j := gap_coordinate_pair_integral_le_internal μ hcoord D hsecond a j
  have hi a : Integrable (fun y : Gaps =>
      (y (i : ℤ) : ℝ) * gapSequenceSpan y a i) μ := (hcoord i).integrable_mul (hs a i)
  have hbound a : (∫ y : Gaps, (y (i : ℤ) : ℝ) * gapSequenceSpan y a i ∂μ) ≤ (i : ℝ) * D := by
    simp only [gapSequenceSpan, Finset.mul_sum]
    rw [integral_finsetSum _ (fun (j : ℕ) _ => (hpair (i : ℤ) (a + j)).1)]
    calc
      _ ≤ ∑ _j ∈ Finset.range i, D := Finset.sum_le_sum fun j _ => (hpair _ _).2
      _ = _ := by simp
  calc
    _ ≤ ∫ y : Gaps, t * ((y (i : ℤ) : ℝ) * gapSequenceSpan y ((K : ℤ) + 1) i +
        (y (i : ℤ) : ℝ) * gapSequenceSpan y 1 i) ∂μ := by
      apply integral_mono herr (((hi _).add (hi _)).const_mul t)
      intro y
      dsimp only [Pi.mul_apply, Pi.add_apply]
      rw [show t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
          t * (gapSequenceSpan y 1 K - K) =
          t * (gapSequenceSpan y ((i : ℤ) + 1) K - gapSequenceSpan y 1 K) by ring,
        abs_mul, abs_of_nonneg ht, translated_gapSequenceSpan_difference]
      have hp a k : 0 ≤ gapSequenceSpan y a k :=
        Finset.sum_nonneg fun j _ => (y _).property.le
      have hb : |gapSequenceSpan y ((K : ℤ) + 1) i - gapSequenceSpan y 1 i| ≤
          gapSequenceSpan y ((K : ℤ) + 1) i + gapSequenceSpan y 1 i :=
        abs_sub_le_iff.mpr ⟨by linarith [hp 1 i], by linarith [hp ((K : ℤ) + 1) i]⟩
      nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (y (i : ℤ)).property.le ht)]
    _ = t * ((∫ y : Gaps, (y (i : ℤ) : ℝ) * gapSequenceSpan y ((K : ℤ) + 1) i ∂μ) +
        ∫ y : Gaps, (y (i : ℤ) : ℝ) * gapSequenceSpan y 1 i ∂μ) := by
      rw [integral_const_mul, integral_add (hi _) (hi _)]
    _ ≤ 2 * D * i * t := by nlinarith [mul_le_mul_of_nonneg_left (add_le_add (hbound ((K : ℤ) + 1)) (hbound 1)) ht]

/-- The centered second moment of an `h`-span is bounded by a constant
 times `h²`, from the common coordinate second moment. -/
theorem gapSequenceSpan_centered_second_moment_internal
    (μ : Measure Gaps) [IsProbabilityMeasure μ]
    (hcoord : ∀ j : ℤ, MemLp (fun y : Gaps => (y j : ℝ)) 2 μ)
    (D : ℝ) (_hD : 0 ≤ D)
    (hsecond : ∀ j : ℤ, (∫ y : Gaps, (y j : ℝ) ^ 2 ∂μ) ≤ D) (a : ℤ) (h : ℕ) :
    Integrable (fun y => (gapSequenceSpan y a h - h) ^ 2) μ ∧
      (∫ y, (gapSequenceSpan y a h - h) ^ 2 ∂μ) ≤ (2 * D + 2) * (h : ℝ) ^ 2 := by
  have hs := gapSequenceSpan_memLp_two μ a h hcoord
  have hsq := (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs
  have hc := hs.sub (memLp_const (h : ℝ))
  have hcsq := (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mp hc
  have hcoordsq j := (memLp_two_iff_integrable_sq (hcoord j).aestronglyMeasurable).mp (hcoord j)
  have hssq : (∫ y, gapSequenceSpan y a h ^ 2 ∂μ) ≤ (h : ℝ) ^ 2 * D := by
    have hbound : (∫ y, gapSequenceSpan y a h ^ 2 ∂μ) ≤
        ∫ y : Gaps, (h : ℝ) * ∑ j ∈ Finset.range h, (y (a + j) : ℝ) ^ 2 ∂μ := by
      apply integral_mono hsq ((integrable_finsetSum _ fun (j : ℕ) _ => hcoordsq (a + j)).const_mul _)
      intro y
      have hb := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range h)
        (fun _ : ℕ => (1 : ℝ)) (fun j : ℕ => (y (a + j) : ℝ))
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, gapSequenceSpan] using hb
    rw [integral_const_mul, integral_finsetSum _ (fun (j : ℕ) _ => hcoordsq (a + j))] at hbound
    have hle : (∑ j ∈ Finset.range h, ∫ y : Gaps, (y (a + j) : ℝ) ^ 2 ∂μ) ≤ (h : ℝ) * D := by
      calc
        _ ≤ ∑ _j ∈ Finset.range h, D := Finset.sum_le_sum fun j _ => hsecond _
        _ = _ := by simp
    nlinarith [mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg h)]
  refine ⟨hcsq, ?_⟩
  have hb : (∫ y, (gapSequenceSpan y a h - h) ^ 2 ∂μ) ≤
      ∫ y, 2 * gapSequenceSpan y a h ^ 2 + 2 * (h : ℝ) ^ 2 ∂μ := by
    apply integral_mono hcsq ((hsq.const_mul 2).add (integrable_const _))
    intro y
    change (gapSequenceSpan y a h - h) ^ 2 ≤ 2 * gapSequenceSpan y a h ^ 2 + 2 * (h : ℝ) ^ 2
    nlinarith [sq_nonneg (gapSequenceSpan y a h + h)]
  rw [integral_add (hsq.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hb
  nlinarith

/-- An `L²` bound controls the tail part of the absolute first moment.
This internal analytic lemma supplies the rigidity-to-mean passage. -/
theorem integral_abs_le_threshold_add_tail_internal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (hF2 : MemLp F 2 μ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, |F ω| ∂μ) ≤ T +
      Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (μ.real {ω | T < |F ω|}) := by
  let E := {ω | T < |F ω|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hF.abs
  have hi := (hF2.integrable (by norm_num)).abs
  have hsq := (memLp_two_iff_integrable_sq hF2.aestronglyMeasurable).mp hF2
  have hb : (∫ ω, |F ω| ∂μ) ≤ ∫ ω, T + E.indicator (fun x => |F x|) ω ∂μ := by
    apply integral_mono hi ((integrable_const T).add (hi.indicator hE))
    intro ω
    dsimp only [Pi.add_apply]
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]; linarith
    · rw [indicator_of_notMem hω]
      simpa only [add_zero] using (le_of_not_gt hω : |F ω| ≤ T)
  rw [integral_add (integrable_const T) (hi.indicator hE), integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul, integral_indicator hE] at hb
  have hcs := Riesz1.integral_on_event_le_second_moment hF.abs.aestronglyMeasurable
    (fun ω => abs_nonneg (F ω)) (by simpa only [sq_abs] using hsq) hE
  have hcs' : (∫ ω in E, |F ω| ∂μ) ≤
      Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (μ.real E) := by
    simpa only [sq_abs, ← Real.sqrt_eq_rpow] using hcs
  exact hb.trans (add_le_add le_rfl hcs')

/-- See the proof of Corollary 1.1 in the paper: rigidity implies the
uniform mean deviation bound for spans. Its constants precede the volume,
label and span length. Both exponent regimes are covered. -/
theorem periodicGapLaw_span_mean_deviation (p : Parameters) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ min p.val.2 1 / 2 + η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ A : ℝ, 0 < A ∧
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ h : ℕ, 1 ≤ h → h ≤ (N : ℕ) / 2 → ∀ a : ℤ,
          (∫ y : Gaps, |gapSequenceSpan y a h - h| ∂periodicGapLaw p N) ≤
            A * (h : ℝ) ^ (min p.val.2 1 / 2 + η) := by
  obtain ⟨η₀, hη₀, hη₀small, hrig⟩ := periodicGapLaw_finite_rigidity p
  obtain ⟨D, hD, hmom⟩ := periodicGapLaw_coordinate_second_moments p
  refine ⟨η₀, hη₀, hη₀small, fun η hη hηsmall => ?_⟩
  obtain ⟨C, c, hC, hc, htail⟩ := hrig η hη hηsmall
  let α := min p.val.2 1 / 2 + η
  let δ := η / (4 * (p.val.2 + 2))
  have hδ : 0 < δ := div_pos hη (by linarith [p.property.2.1])
  obtain ⟨B, hB, hBbound⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1 - α) (c := c / 2) (c' := 0) hδ (half_pos hc)
  let A := 1 + Real.sqrt (2 * D + 2) * Real.sqrt C * B
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, fun N hN h hh hhN a => ?_⟩
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  let μ := (periodicGapLaw p N).toMeasure
  have hcoord j := (hmom N hN j).1
  have hs := (gapSequenceSpan_memLp_two μ a h hcoord).sub (memLp_const (h : ℝ))
  have hF : Measurable (fun y : Gaps => gapSequenceSpan y a h - h) :=
    (continuous_gapSequenceSpan a h).measurable.sub_const _
  have hbase := integral_abs_le_threshold_add_tail_internal μ _ hF hs ((h : ℝ) ^ α)
    (Real.rpow_nonneg hhpos.le _)
  have hsecond := (gapSequenceSpan_centered_second_moment_internal μ hcoord D hD.le
    (fun j => (hmom N hN j).2) a h).2
  have hprob : μ.real {y | (h : ℝ) ^ α < |gapSequenceSpan y a h - h|} ≤
      C * Real.exp (-c * (h : ℝ) ^ δ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (htail N hN h hh hhN a)
  have hsqrt : Real.sqrt ((2 * D + 2) * (h : ℝ) ^ 2) *
      Real.sqrt (C * Real.exp (-c * (h : ℝ) ^ δ)) =
      Real.sqrt (2 * D + 2) * Real.sqrt C *
        ((h : ℝ) * Real.exp (-(c / 2) * (h : ℝ) ^ δ)) := by
    have he : Real.sqrt (Real.exp (-c * (h : ℝ) ^ δ)) =
        Real.exp (-(c / 2) * (h : ℝ) ^ δ) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1
      ring
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hhpos.le,
      Real.sqrt_mul hC.le, he]
    ring
  have hpow : (h : ℝ) * Real.exp (-(c / 2) * (h : ℝ) ^ δ) ≤ B * (h : ℝ) ^ α := by
    have hb := hBbound (h : ℝ) hh1
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at hb
    have hp : (h : ℝ) ^ α * (h : ℝ) ^ (1 - α) = h := by
      rw [← Real.rpow_add hhpos, add_sub_cancel, Real.rpow_one]
    have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hhpos.le α)
    rw [← mul_assoc, hp] at hm
    simpa only [mul_comm] using hm
  have hcs := mul_le_mul (Real.sqrt_le_sqrt hsecond) (Real.sqrt_le_sqrt hprob)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [hsqrt] at hcs
  have hf := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (Real.sqrt_nonneg (2 * D + 2)) (Real.sqrt_nonneg C))
  dsimp only [A]
  nlinarith

/-- See the proof of Corollary 1.1 in the paper, the quantitative estimate
before fixing the normalization. It is uniform in the volume, span length,
and bounded one-Lipschitz test. -/
theorem periodicGapLaw_stationary_bias_bound (p : Parameters) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ min p.val.2 1 / 2 + η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ K h : ℕ, 1 ≤ h → h ≤ (N : ℕ) / 2 →
          ∀ t : ℝ, 0 ≤ t → ∀ f : ℝ → ℝ, LipschitzWith 1 f → (∀ x, |f x| ≤ 1) →
          |(∫ y : Gaps, (y 0 : ℝ) * f (t * (gapSequenceSpan y 1 K - K)) ∂periodicGapLaw p N) -
              ∫ y : Gaps, f (t * (gapSequenceSpan y 1 K - K)) ∂periodicGapLaw p N| ≤
            C * ((h : ℝ) ^ (-1 + min p.val.2 1 / 2 + η) + (h : ℝ) * t) := by
  obtain ⟨η₀, hη₀, hη₀small, hmean⟩ := periodicGapLaw_span_mean_deviation p
  obtain ⟨D, hD, hmom⟩ := periodicGapLaw_coordinate_second_moments p
  refine ⟨η₀, hη₀, hη₀small, fun η hη hηsmall => ?_⟩
  obtain ⟨A, hA, hmean⟩ := hmean η hη hηsmall
  refine ⟨max A (2 * D), lt_of_lt_of_le hA (le_max_left _ _),
    fun N hN K h hh hhN t ht f hf hfb => ?_⟩
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast hh
  have havg : (∫ y : Gaps, |(h : ℝ)⁻¹ * gapSequenceSpan y 0 h - 1| ∂periodicGapLaw p N) ≤
      A * (h : ℝ) ^ (-1 + min p.val.2 1 / 2 + η) := by
    have he (y : Gaps) : |(h : ℝ)⁻¹ * gapSequenceSpan y 0 h - 1| =
        (h : ℝ)⁻¹ * |gapSequenceSpan y 0 h - h| := by
      rw [show (h : ℝ)⁻¹ * gapSequenceSpan y 0 h - 1 =
        (h : ℝ)⁻¹ * (gapSequenceSpan y 0 h - h) by field_simp,
        abs_mul, abs_of_pos (inv_pos.mpr hhpos)]
    simp_rw [he]
    rw [integral_const_mul]
    have hepow : (h : ℝ)⁻¹ * (h : ℝ) ^ (min p.val.2 1 / 2 + η) =
        (h : ℝ) ^ (-1 + min p.val.2 1 / 2 + η) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hhpos]
      congr 1
      ring
    have hb := mul_le_mul_of_nonneg_left (hmean N hN h hh hhN 0) (inv_nonneg.mpr hhpos.le)
    calc
      _ ≤ (h : ℝ)⁻¹ * (A * (h : ℝ) ^ (min p.val.2 1 / 2 + η)) := hb
      _ = _ := by rw [← mul_assoc, mul_comm _ A, mul_assoc, hepow]
  have hdispl : (h : ℝ)⁻¹ * (∑ i ∈ Finset.range h,
        ∫ y : Gaps, (y (i : ℤ) : ℝ) *
          |t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
            t * (gapSequenceSpan y 1 K - K)| ∂periodicGapLaw p N) ≤ 2 * D * h * t := by
    have hsum : (∑ i ∈ Finset.range h,
        ∫ y : Gaps, (y (i : ℤ) : ℝ) *
          |t * (gapSequenceSpan y ((i : ℤ) + 1) K - K) -
            t * (gapSequenceSpan y 1 K - K)| ∂periodicGapLaw p N) ≤
          (h : ℝ) * (2 * D * h * t) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range h, 2 * D * h * t := by
          apply Finset.sum_le_sum
          intro i hi
          have hb := weighted_translated_span_difference_le_internal (periodicGapLaw p N).toMeasure
            (fun j => (hmom N hN j).1) D (fun j => (hmom N hN j).2) i K t ht
          have hih : (i : ℝ) ≤ h := by exact_mod_cast (Finset.mem_range.mp hi).le
          exact hb.trans (by nlinarith [mul_nonneg hD.le ht])
        _ = _ := by simp
    have hb := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hhpos.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hhpos.ne', one_mul] using hb
  have hb := (periodicGapLaw_length_bias_averaging p N hN K h (by omega) t f hf hfb).trans
    (add_le_add havg hdispl)
  apply hb.trans
  have hfirst := mul_le_mul_of_nonneg_right (le_max_left A (2 * D))
    (Real.rpow_nonneg hhpos.le (-1 + min p.val.2 1 / 2 + η))
  have hsecond := mul_le_mul_of_nonneg_right (le_max_right A (2 * D))
    (mul_nonneg hhpos.le ht)
  nlinarith

/-- See the proof of Corollary 1.1 in the paper, its stated long-range
normalization and parameter ranges. -/
theorem hyper_riesz_bias_removal (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ s.val / 2 + η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ+) (K h : ℕ), 1 ≤ K → 8 * K ≤ (N : ℕ) → 1 ≤ h → h ≤ K →
          ∀ f : ℝ → ℝ, LipschitzWith 1 f → (∀ x, |f x| ≤ 1) →
          |(∫ y : Gaps, (y 0 : ℝ) *
              f ((K : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 K - K))
                ∂periodicGapLaw (ofLong β s) N) -
            ∫ y : Gaps, f ((K : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 K - K))
              ∂periodicGapLaw (ofLong β s) N| ≤
            C * ((h : ℝ) ^ (-1 + s.val / 2 + η) + (h : ℝ) * (K : ℝ) ^ (-s.val / 2)) := by
  obtain ⟨η₀, hη₀, hη₀small, hb⟩ := periodicGapLaw_stationary_bias_bound (ofLong β s)
  have hmin : min (ofLong β s).val.2 1 = s.val := min_eq_left s.property.2.le
  rw [hmin] at hη₀small hb
  refine ⟨η₀, hη₀, hη₀small, fun η hη hηsmall => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb η hη hηsmall
  exact ⟨C, hC, fun N K h hK hKN hh hhK f hf hfb =>
    hb N (by omega) K h hh (by omega) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) f hf hfb⟩

/-- The finite first-particle sampling strip is a probability, using the
finite inversion identity rather than assuming a normalization. -/
theorem finite_suspensionStrip_probability (p : Parameters) (N : ℕ+) :
    IsProbabilityMeasure
      ((((gibbsMeasure p N).map configurationReconstructionGaps).prod volume).restrict
        gapSuspensionStrip) := by
  constructor
  have he := congrArg (fun μ : Measure LineConfiguration => μ univ)
    (finite_suspensionStrip_spatial_law p N)
  rw [Measure.map_apply measurable_gapSuspensionConfiguration MeasurableSet.univ,
    preimage_univ] at he
  rw [he]
  exact (periodicSpatialLaw_probability p N).measure_univ

/-- See the proof of Corollary 1.1 in the paper: the exact normalized-span
sampling formula, together with integrability of the selected observable.
The two gap laws are the existing finite reconstruction and periodic laws. -/
theorem hyper_riesz_first_particle (p : Parameters) (N : ℕ+) (K : ℕ) (t : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (_hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M) :
    Integrable (fun z : reconstructibleGapSequences × ℝ =>
        f (t * (gapSequenceSpan z.1.val 1 K - K)))
      ((((gibbsMeasure p N).map configurationReconstructionGaps).prod volume).restrict
        gapSuspensionStrip) ∧
    (∫ z : reconstructibleGapSequences × ℝ, f (t * (gapSequenceSpan z.1.val 1 K - K))
      ∂(((gibbsMeasure p N).map configurationReconstructionGaps).prod volume).restrict
        gapSuspensionStrip) =
      ∫ y : Gaps, (y 0 : ℝ) * f (t * (gapSequenceSpan y 1 K - K)) ∂periodicGapLaw p N := by
  have firstParticleBaseProbability := gibbsMeasure_probability p N
  let q := (gibbsMeasure p N).map configurationReconstructionGaps
  have firstParticleReconstructionProbability : IsProbabilityMeasure q := by
    dsimp only [q]
    infer_instance
  have hprob := finite_suspensionStrip_probability p N
  have firstParticleFiniteStripProbability : IsProbabilityMeasure
      ((q.prod volume).restrict gapSuspensionStrip) := hprob
  have hm : Measurable (fun y : Gaps => f (t * (gapSequenceSpan y 1 K - K))) :=
    hf.comp (((continuous_gapSequenceSpan 1 K).measurable.sub_const _).const_mul _)
  have hi : Integrable (fun z : reconstructibleGapSequences × ℝ =>
      f (t * (gapSequenceSpan z.1.val 1 K - K))) ((q.prod volume).restrict gapSuspensionStrip) := by
    apply (integrable_const M).mono'
      (hm.comp (measurable_subtype_coe.comp measurable_fst)).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      change |f (t * (gapSequenceSpan z.1.val 1 K - K))| ≤ M
      exact hfb _
  refine ⟨hi, ?_⟩
  rw [integral_suspensionStrip_independent_offset q
    (fun y => f (t * (gapSequenceSpan y.val 1 K - K))) (hm.comp measurable_subtype_coe)]
  dsimp only [q]
  rw [integral_map (f := fun y : reconstructibleGapSequences =>
      (y.val 0 : ℝ) * f (t * (gapSequenceSpan y.val 1 K - K)))
    (measurable_configurationReconstructionGaps N).aemeasurable
    ((measurable_subtype_coe.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)).mul
      (hm.comp measurable_subtype_coe)).aestronglyMeasurable,
    integral_periodicGapLaw p N (f := fun y : Gaps =>
      (y 0 : ℝ) * f (t * (gapSequenceSpan y 1 K - K)))
      ((measurable_subtype_coe.comp (measurable_pi_apply 0)).mul hm)]
  rfl

/-- See the proof of Corollary 1.1 in the paper: a gap-dependent bad
event loses only a square root under first-particle length bias. -/
theorem length_biased_event_le_sqrt_internal
    (q : Measure reconstructibleGapSequences) [IsProbabilityMeasure q]
    (A : ℝ) (hA : 0 ≤ A)
    (hsecond : (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤ ENNReal.ofReal A)
    (E : Set reconstructibleGapSequences) (hE : MeasurableSet E) :
    ((q.prod volume).restrict gapSuspensionStrip) (Prod.fst ⁻¹' E) ≤
      ENNReal.ofReal (Real.sqrt A * Real.sqrt (q.real E)) := by
  have hw : Measurable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) :=
    measurable_subtype_coe.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have habs (y : reconstructibleGapSequences) : |(y.val 0 : ℝ)| = (y.val 0 : ℝ) :=
    abs_of_pos (y.val 0).property
  obtain ⟨hi, hb⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le hw hA
    (by simpa only [habs] using hsecond)
  have hi' : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ) ^ 2) q := by
    simpa only [habs, Real.rpow_two] using hi
  have hb' : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ^ 2 ∂q) ≤ A := by
    simpa only [habs, Real.rpow_two] using hb
  have hcs := MomentEvent.abs_integral_mul_le_sqrt_mul_sqrt
    (g := fun _ : reconstructibleGapSequences => (1 : ℝ)) (M := 1)
    measurable_const hw zero_le_one (fun _ => by norm_num) hi' hE
  simp only [one_mul] at hcs
  have he := congrArg (fun μ : Measure reconstructibleGapSequences => μ E) (suspensionStrip_map_fst q)
  rw [Measure.map_apply measurable_fst hE, withDensity_apply _ hE] at he
  rw [he, ← ofReal_integral_eq_lintegral_ofReal
    (MomentEvent.integrable_of_integrable_sq hw hi').integrableOn
    (ae_of_all _ fun y => (y.val 0).property.le)]
  apply ENNReal.ofReal_le_ofReal
  exact ((le_abs_self _).trans hcs).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hb') (Real.sqrt_nonneg _))

/-- The two powers in the averaging bound vanish for the paper's integer
choice `h = floor (K^a)`. This also checks that rounding does not change the rate. -/
theorem floor_power_bias_rate_tendsto (a b c : ℝ) (ha : 0 < a) (hb : b < 0) (hac : a + c < 0) :
    Tendsto (fun k : ℕ => (⌊(k : ℝ) ^ a⌋₊ : ℝ) ^ b +
      (⌊(k : ℝ) ^ a⌋₊ : ℝ) * (k : ℝ) ^ c) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hfloor : Tendsto (fun k : ℕ => ⌊(k : ℝ) ^ a⌋₊) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [hpow.eventually (eventually_ge_atTop (n : ℝ))] with k hk
    exact Nat.le_floor hk
  have hfirst : Tendsto (fun k : ℕ => (⌊(k : ℝ) ^ a⌋₊ : ℝ) ^ b) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hb)).comp
        (tendsto_natCast_atTop_atTop.comp hfloor)
  have hupper : Tendsto (fun k : ℕ => (k : ℝ) ^ (a + c)) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hac)).comp tendsto_natCast_atTop_atTop
  have hsecond : Tendsto (fun k : ℕ => (⌊(k : ℝ) ^ a⌋₊ : ℝ) * (k : ℝ) ^ c) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_ hupper
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
    calc
      _ ≤ (k : ℝ) ^ a * (k : ℝ) ^ c :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := (Real.rpow_add hkpos a c).symm
  simpa only [add_zero] using hfirst.add hsecond

/-- See the proof of Corollary 1.1 in the paper: the selected and ordinary
span expectations agree asymptotically along every mesoscopic pair. -/
theorem hyper_riesz_bias_removal_tendsto
    (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ → ℕ+) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0))
    (a : ℝ) (ha : 0 < a) (has : a < s.val / 2)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (hfb : ∀ x, |f x| ≤ 1) :
    Tendsto (fun j =>
      (∫ y : Gaps, (y 0 : ℝ) *
          f ((K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 (K j) - K j))
            ∂periodicGapLaw (ofLong β s) (N j)) -
        ∫ y : Gaps, f ((K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 (K j) - K j))
          ∂periodicGapLaw (ofLong β s) (N j)) atTop (𝓝 0) := by
  obtain ⟨η₀, hη₀, hη₀small, hb⟩ := hyper_riesz_bias_removal s β
  obtain ⟨C, hC, hbound⟩ := hb (η₀ / 2) (half_pos hη₀) (half_lt_self hη₀)
  let h : ℕ → ℕ := fun k => ⌊(k : ℝ) ^ a⌋₊
  have hα : -1 + s.val / 2 + η₀ / 2 < 0 := by linarith
  have hrate := (floor_power_bias_rate_tendsto a (-1 + s.val / 2 + η₀ / 2)
    (-s.val / 2) ha hα (by linarith)).comp hK
  have hrateC := hrate.const_mul C
  simp only [mul_zero] at hrateC
  have hlarge : ∀ᶠ j in atTop, 1 ≤ K j ∧ 8 * K j ≤ (N j : ℕ) := by
    filter_upwards [hK.eventually_ge_atTop 1,
      hKN.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8)] with j hj hratio
    refine ⟨hj, ?_⟩
    have hn : 0 < (N j : ℝ) := by exact_mod_cast (N j).pos
    have hp := (div_lt_iff₀ hn).mp hratio
    exact_mod_cast (show (8 : ℝ) * K j ≤ (N j : ℝ) by linarith)
  apply squeeze_zero_norm' ?_ hrateC
  filter_upwards [hlarge] with j hj
  have hk1 : (1 : ℝ) ≤ K j := by exact_mod_cast hj.1
  have hh1 : 1 ≤ h (K j) := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hk1 ha.le
  have hhk : h (K j) ≤ K j := by
    apply Nat.floor_le_of_le
    calc
      (K j : ℝ) ^ a ≤ (K j : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [s.property.2])
      _ = _ := Real.rpow_one _
  simpa only [Real.norm_eq_abs, h, Function.comp_def] using
    hbound (N j) (K j) (h (K j)) hj.1 hj.2 hh1 hhk f hf hfb

end Riesz2
