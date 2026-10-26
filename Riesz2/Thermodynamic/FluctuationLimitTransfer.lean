/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CountMoments
public import Riesz2.Thermodynamic.StationaryBias
public import Riesz2.Thermodynamic.GapNondegeneracyPart3
public import Riesz2.Thermodynamic.FiniteCountLimitsPart2
public import Riesz2.Thermodynamic.MesoscopicGapLimitsPart3
public import Riesz2.ToMathlib.MesoscopicDiagonalJoint
public import Riesz2.ToMathlib.WeightedTotalVariation
public import Riesz2.Thermodynamic.GapTotalVariation
public import Riesz2.ToMathlib.FluctuationVarianceTransfer
public import Riesz2.Frozen.NumberVariance
public import Riesz2.Frozen.PalmSpanVariance
public import Riesz2.Frozen.HyperuniformityRatio
public import Riesz1.ToMathlib.VarianceTwoErrors

/-!
# Fixed-window fluctuation transfer

Steps of the proof of Corollary 1.1. Fixed-window passages use spatial count moments and
truncation under finite-block total variation for Palm span moments. Counts and spans
share a joint law/variance diagonal, applied to the finite mesoscopic central limit
theorems.
-/

public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

local instance fluctuationLimitTransferConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace
local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local notation "spanProj" => (fun (k : ℕ) (y : Gaps) =>
  (WithLp.toLp 2 (fun j : Fin k => (y (0 + (Fin.val j : ℤ)) : ℝ)) : EuclideanSpace ℝ (Fin k)))

local instance fluctuationPositiveRadiusCountablyGenerated :
    (atTop : Filter {R : ℝ // 0 < R}).IsCountablyGenerated := by
  rw [show (atTop : Filter {R : ℝ // 0 < R}) =
    comap (Subtype.val : {R : ℝ // 0 < R} → ℝ) atTop from atTop_Ioi_eq (0 : ℝ)]
  infer_instance

/-- See the proof of Corollary 1.1 in the paper: inside a strict quarter-period,
the finite periodic spatial count is the literal finite interval statistic.
This includes the right endpoint and does not discard any configurations. -/
theorem periodicSpatial_intervalCount_eq_finiteIntervalCount
    (N : ℕ+) (R : ℝ) (hR : 0 < R) (hRN : R / (N : ℝ) < 1 / 4)
    (X : Riesz1.Configuration N) :
    intervalCount 0 R (periodicSpatialConfiguration X) = finiteIntervalCount N R X := by
  have hsub : Ioc (0 : ℝ) R ⊆ Icc (-R) R := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  rw [← intervalCount_restrictConfiguration 0 R R hsub,
    periodicSpatialConfiguration_restrict_eq_microscopic X R
      (by have := (div_lt_iff₀ (show (0 : ℝ) < N by positivity)).mp hRN; linarith),
    intervalCount_restrictConfiguration 0 R R hsub,
    finiteIntervalCount_eq_intervalCount N R hR hRN]

/-- See the proof of Corollary 1.1 in the paper: the finite periodic count law
agrees with the finite interval-count law on every admissible window. -/
theorem periodicSpatial_intervalCount_law_eq
    (p : Parameters) (N : ℕ+) (R : ℝ) (hR : 0 < R)
    (hRN : R / (N : ℝ) < 1 / 4) :
    (periodicSpatialLaw p N).map (intervalCount 0 R) =
      (gibbsMeasure p N).map (finiteIntervalCount N R) := by
  rw [periodicSpatialLaw, Measure.map_map (measurable_intervalCount 0 R)
    (measurable_periodicSpatialConfiguration N)]
  congr 1
  exact funext (periodicSpatial_intervalCount_eq_finiteIntervalCount N R hR hRN)

/-- The strict quarter-period condition eventually holds at each fixed positive
radius. This is a fixed-window assertion, before any diagonal choice. -/
theorem eventually_fixed_radius_admissible (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, R / (n.succPNat : ℝ) < 1 / 4 := by
  have ht : Tendsto (fun n : ℕ => R / (n.succPNat : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
  exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))

/-- See the proof of Corollary 1.1 in the paper, fixed spatial windows. The gap-limit
and suspension conclusions imply square integrability of every bounded interval
count and convergence of its first and second moments. No moment estimate is
assumed. The periodic local total variation convergence is a hypothesis. -/
theorem fixed_window_count_moments_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (P : PointProcess)
    (hP : (P : Measure LineConfiguration) =
      gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure))
    (hlocal : LocalConverges (periodicSpatialLaw p) P) (a b : ℝ) :
    MemLp (intervalCount a b) 2 (P : Measure LineConfiguration) ∧
      Tendsto (fun n : ℕ => ∫ C, intervalCount a b C ∂periodicSpatialLaw p n.succPNat)
        atTop (𝓝 (∫ C, intervalCount a b C ∂P)) ∧
      Tendsto (fun n : ℕ => ∫ C, intervalCount a b C ^ 2 ∂periodicSpatialLaw p n.succPNat)
        atTop (𝓝 (∫ C, intervalCount a b C ^ 2 ∂P)) := by
  obtain ⟨C, hC, hf⟩ := periodic_spatial_interval_count_moment_bound p a b 4 (by norm_num)
  obtain ⟨D, hD, hl⟩ :=
    limiting_suspension_interval_count_moments_from_gap_limit_internal p q hq a b 4 (by norm_num)
  let B := max C D
  have hB : 0 ≤ B := hC.le.trans (le_max_left _ _)
  have hf' (N : ℕ+) (hN : 2 ≤ (N : ℕ)) : (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ 4)
      ∂periodicSpatialLaw p N) ≤ ENNReal.ofReal B := by
    simpa only [Real.rpow_ofNat] using
      (hf N hN).trans (ENNReal.ofReal_le_ofReal (le_max_left C D))
  have hl' : (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ 4) ∂P) ≤ ENNReal.ofReal B := by
    rw [hP]
    simpa only [Real.rpow_ofNat] using hl.trans (ENNReal.ofReal_le_ofReal (le_max_right C D))
  have ht := intervalCount_first_second_moments_tendsto_internal
    (periodicSpatialLaw p) P hlocal a b B hB hf' hl'
  exact ⟨(memLp_two_iff_integrable_sq (measurable_intervalCount a b).aestronglyMeasurable).mpr
    ht.2.2.1, ht.2.2.2⟩

/-- See the proof of Corollary 1.1 in the paper: fixed-window normalized finite
counts converge in law to the stationary count, for any real centering
and multiplier. Local TV permits discontinuous counts and their endpoints. -/
theorem fixed_window_count_law_internal
    (p : Parameters) (P : PointProcess)
    (hlocal : LocalConverges (periodicSpatialLaw p) P)
    (R a b : ℝ) (hR : 0 < R) :
    ConvergesInLawAlong atTop
      (fun n : ℕ => (gibbsMeasure p n.succPNat).map
        (fun X => a * (finiteIntervalCount n.succPNat R X - b)))
      ((P : Measure LineConfiguration).map (fun C => a * (intervalCount 0 R C - b))) := by
  let μ : ℕ → Measure ℝ := fun n => (periodicSpatialLaw p n.succPNat).map (intervalCount 0 R)
  let ν : Measure ℝ := (P : Measure LineConfiguration).map (intervalCount 0 R)
  have μprob (n : ℕ) : IsProbabilityMeasure (μ n) := by
    let periodicSpatialProbability : IsProbabilityMeasure (periodicSpatialLaw p n.succPNat) :=
      periodicSpatialLaw_probability p _
    exact Measure.isProbabilityMeasure_map_iff (measurable_intervalCount 0 R).aemeasurable |>.mpr inferInstance
  have νprob : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map_iff (measurable_intervalCount 0 R).aemeasurable |>.mpr inferInstance
  have htv := intervalCount_law_totalVariation_tendsto_from_local_internal
    (periodicSpatialLaw p) P hlocal 0 R
  have hw := probabilityMeasure_tendsto_of_totalVariation
    (fun n => ⟨μ n, μprob n⟩) ⟨ν, νprob⟩ htv
  have haff := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (⟨μ n, μprob n⟩ : ProbabilityMeasure ℝ)) ⟨ν, νprob⟩ hw
    (f := fun x : ℝ => a * (x - b)) (by fun_prop)
  refine ⟨fun n => ?_, ?_, fun f => ?_⟩
  · let finiteGibbsProbability : IsProbabilityMeasure (gibbsMeasure p n.succPNat) :=
      gibbsMeasure_probability p _
    exact Measure.isProbabilityMeasure_map_iff
      (((measurable_finiteIntervalCount _ _).sub_const _).const_mul _).aemeasurable |>.mpr inferInstance
  · exact Measure.isProbabilityMeasure_map_iff
      (((measurable_intervalCount _ _).sub_const _).const_mul _).aemeasurable |>.mpr inferInstance
  · have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp haff f
    change Tendsto (fun n => ∫ x, f x ∂(μ n).map (fun x => a * (x - b))) atTop
      (𝓝 (∫ x, f x ∂ν.map (fun x => a * (x - b)))) at ht
    simp only [μ, ν, Measure.map_map
      (by fun_prop : Measurable (fun x : ℝ => a * (x - b)))
        (measurable_intervalCount 0 R), Function.comp_def] at ht
    apply ht.congr'
    filter_upwards [eventually_fixed_radius_admissible R] with n hn
    have he := congrArg (fun ρ : Measure ℝ => ∫ x, f x ∂ρ.map (fun x => a * (x - b)))
      (periodicSpatial_intervalCount_law_eq p n.succPNat R hR hn)
    simpa only [Measure.map_map (by fun_prop : Measurable (fun x : ℝ => a * (x - b)))
      (measurable_intervalCount 0 R),
      Measure.map_map (by fun_prop : Measurable (fun x : ℝ => a * (x - b)))
        (measurable_finiteIntervalCount _ _), Function.comp_def] using he

/-- See the proof of Corollary 1.1 in the paper: the first two finite interval-count
moments converge at a fixed positive radius. The pointwise quarter-period
bridge removes the distinction between finite circle and periodic counts. -/
theorem fixed_window_finite_count_moments_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (P : PointProcess)
    (hP : (P : Measure LineConfiguration) =
      gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure))
    (hlocal : LocalConverges (periodicSpatialLaw p) P) (R : ℝ) (hR : 0 < R) :
    MemLp (intervalCount 0 R) 2 (P : Measure LineConfiguration) ∧
      Tendsto (fun n : ℕ => ∫ X, finiteIntervalCount n.succPNat R X ∂gibbsMeasure p n.succPNat)
        atTop (𝓝 (∫ C, intervalCount 0 R C ∂P)) ∧
      Tendsto (fun n : ℕ => ∫ X, finiteIntervalCount n.succPNat R X ^ 2 ∂gibbsMeasure p n.succPNat)
        atTop (𝓝 (∫ C, intervalCount 0 R C ^ 2 ∂P)) := by
  obtain ⟨hc, hfirst, hsecond⟩ := fixed_window_count_moments_internal p q hq P hP hlocal 0 R
  have he (n : ℕ) (hn : R / (n.succPNat : ℝ) < 1 / 4) (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ C, f (intervalCount 0 R C) ∂periodicSpatialLaw p n.succPNat) =
        ∫ X, f (finiteIntervalCount n.succPNat R X) ∂gibbsMeasure p n.succPNat := by
    have hh := congrArg (fun ρ : Measure ℝ => ∫ x, f x ∂ρ)
      (periodicSpatial_intervalCount_law_eq p n.succPNat R hR hn)
    simpa only [integral_map (measurable_intervalCount 0 R).aemeasurable hf.aestronglyMeasurable,
      integral_map (measurable_finiteIntervalCount _ _).aemeasurable hf.aestronglyMeasurable] using hh
  refine ⟨hc, hfirst.congr' ?_, hsecond.congr' ?_⟩
  · filter_upwards [eventually_fixed_radius_admissible R] with n hn
    exact he n hn id measurable_id
  · filter_upwards [eventually_fixed_radius_admissible R] with n hn
    exact he n hn (fun x => x ^ 2) (by fun_prop)

/-- See the proof of Corollary 1.1 in the paper, fixed-window number variance.
Both the real value and the extended variance converge, and the limit
count is square integrable. The integrability certificate is a conclusion. -/
theorem fixed_window_count_variance_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw (ofLong β s) n.succPNat) atTop (𝓝 q))
    (P : PointProcess)
    (hP : (P : Measure LineConfiguration) =
      gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure))
    (hlocal : LocalConverges (periodicSpatialLaw (ofLong β s)) P)
    (R : ℝ) (hR : 0 < R) :
    ∃ hc : MemLp (intervalCount 0 R) 2 (P : Measure LineConfiguration),
      Tendsto (fun n : ℕ => (Riesz1.variance (gibbsMeasure (ofLong β s) n.succPNat)
        (finiteIntervalCount n.succPNat R) (integrable_finiteIntervalCount β s n.succPNat R)).toReal)
        atTop (𝓝 (numberVariance P R (hc.integrable one_le_two)).toReal) ∧
      Tendsto (fun n : ℕ => Riesz1.variance (gibbsMeasure (ofLong β s) n.succPNat)
        (finiteIntervalCount n.succPNat R) (integrable_finiteIntervalCount β s n.succPNat R))
        atTop (𝓝 (numberVariance P R (hc.integrable one_le_two))) := by
  obtain ⟨hc, hfirst, hsecond⟩ := fixed_window_finite_count_moments_internal
    (ofLong β s) q hq P hP hlocal R hR
  let fluctuationCountGibbsProbability (n : ℕ) :
      IsProbabilityMeasure (gibbsMeasure (ofLong β s) n.succPNat) := gibbsMeasure_probability _ _
  have ht := variance_tendsto_of_first_second_moments
    (fun n : ℕ => gibbsMeasure (ofLong β s) n.succPNat) (P : Measure LineConfiguration)
    (fun n : ℕ => finiteIntervalCount n.succPNat R) (intervalCount 0 R)
    (fun n : ℕ => memLp_finiteIntervalCount β s n.succPNat R) hc hfirst hsecond
  refine ⟨hc, ?_, ?_⟩
  · exact ht.1
  · exact ht.2

/-- Corollary 1.1, the final Palm paragraph: truncate each fixed
span and its square under block TV. Uniform fourth gap moments bound both tails. No weak-convergence moment-passage theorem is used. -/
theorem fixed_window_gap_span_moments_of_totalVariation_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) (K : ℕ)
    (hTV : Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
      (q.toMeasure.map (spanProj K))) atTop (𝓝 0)) :
    MemLp (fun y => gapSequenceSpan y 0 K) 2 q ∧
      Tendsto (fun n : ℕ => ∫ y, gapSequenceSpan y 0 K ∂periodicGapLaw p n.succPNat)
        atTop (𝓝 (∫ y, gapSequenceSpan y 0 K ∂q)) ∧
      Tendsto (fun n : ℕ => ∫ y, gapSequenceSpan y 0 K ^ 2 ∂periodicGapLaw p n.succPNat)
        atTop (𝓝 (∫ y, gapSequenceSpan y 0 K ^ 2 ∂q)) := by
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  obtain ⟨D, hD, hf, hl⟩ := periodicGapLaw_limit_all_moments p V
    (fun n => by simp [V]) q ((tendsto_add_atTop_iff_nat 1).mpr hq) 4 (by norm_num)
  let a : EuclideanSpace ℝ (Fin K) := WithLp.toLp 2 (fun _ => 1)
  have he (y : Gaps) : (∑ i : Fin K, a i * (y i.val : ℝ)) = gapSequenceSpan y 0 K := by
    change (∑ i : Fin K, 1 * (y (i.val : ℤ) : ℝ)) = _
    simp only [one_mul, gapSequenceSpan, zero_add]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (y (j : ℤ) : ℝ)) K
  let C := (∑ i, a i ^ 2) ^ 2 * (K : ℝ) * ((K : ℝ) * D)
  have h4 (ρ : ProbabilityMeasure Gaps)
      (hρ : ∀ i : Fin K, (∫⁻ y : Gaps, ENNReal.ofReal ((y i.val : ℝ) ^ (4 : ℝ)) ∂ρ) ≤
        ENNReal.ofReal D) :
      MemLp (fun y => gapSequenceSpan y 0 K ^ 2) 2 ρ ∧
        (∫ y, (gapSequenceSpan y 0 K ^ 2) ^ 2 ∂ρ) ≤ C := by
    simpa only [he] using GapNondegeneracy.weighted_block_fourth_bound_internal ρ K a hD.le hρ
  have hfin (n : ℕ) := h4 (periodicGapLaw p n.succPNat)
    (fun i => (le_add_right le_rfl).trans (hf _ _))
  have hlim := h4 q (fun i => (le_add_right le_rfl).trans (hl _))
  have hm := (continuous_gap_block_projection_internal K 0).measurable
  let A : EuclideanSpace ℝ (Fin K) → ℝ := fun x => ∑ i, x i
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hspan (y : Gaps) : A (spanProj K y) = gapSequenceSpan y 0 K := by
    change (∑ i : Fin K, (y (0 + (i.val : ℤ)) : ℝ)) = _
    simpa only [a, zero_add, one_mul] using he y
  have hmap (ρ : ProbabilityMeasure Gaps)
      (hi : MemLp (fun y => gapSequenceSpan y 0 K ^ 2) 2 ρ) :
      MemLp (fun x => A x ^ 2) 2 (ρ.toMeasure.map (spanProj K)) := by
    apply (memLp_map_measure_iff (hA.pow_const 2).aestronglyMeasurable hm.aemeasurable).mpr
    simpa only [Function.comp_def, hspan] using hi
  have hi (ρ : ProbabilityMeasure Gaps) (j : ℕ) :
      (∫ x, A x ^ j ∂ρ.toMeasure.map (spanProj K)) =
        ∫ y, gapSequenceSpan y 0 K ^ j ∂ρ := by
    rw [integral_map hm.aemeasurable (hA.pow_const j).aestronglyMeasurable]
    simp only [hspan]
  have ht := first_second_moments_tendsto_of_totalVariation_fourth_internal
    (fun n => (periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
    (q.toMeasure.map (spanProj K)) hA (fun n => hmap _ (hfin n).1) (hmap _ hlim.1) hTV
    (C := C) (Eventually.of_forall fun n => by
      rw [integral_map hm.aemeasurable ((hA.pow_const 2).pow_const 2).aestronglyMeasurable]
      simpa only [hspan] using (hfin n).2)
  refine ⟨(memLp_two_iff_integrable_sq
    (continuous_gapSequenceSpan 0 K).measurable.aestronglyMeasurable).mpr
      (hlim.1.integrable one_le_two), ?_⟩
  have hid (ρ : ProbabilityMeasure Gaps) :
      (∫ x, A x ∂ρ.toMeasure.map (spanProj K)) = ∫ y, gapSequenceSpan y 0 K ∂ρ := by
    rw [integral_map hm.aemeasurable hA.aestronglyMeasurable]
    simp only [hspan]
  simpa only [hid, hi] using ht

/-- See the proof of Corollary 1.1 in the paper: the actual finite block sum and
the positive periodic span have the same complete law, also for repeated blocks. -/
theorem finiteGapBlock_sum_law_eq_periodic_span (p : Parameters) (N K : ℕ+) :
    (gibbsMeasure p N).map (fun X => ∑ j : Fin (K : ℕ), finiteGapBlock X j) =
      (periodicGapLaw p N).toMeasure.map (fun y => gapSequenceSpan y 0 K) := by
  rw [periodicGapLaw_toMeasure, Measure.map_map
    (continuous_gapSequenceSpan 0 K).measurable (measurable_periodicGapSequence N)]
  congr 1
  funext X
  rw [MesoscopicVariance.finiteGapBlock_sum_eq_blockLength, Function.comp_apply,
    gapSequenceSpan_periodic]

/-- See the proof of Corollary 1.1 in the paper: the fixed-window CLT transfer for
labelled finite spans, with arbitrary fixed multiplier and centering. -/
theorem fixed_window_gap_span_law_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (K : ℕ+) (a b : ℝ)
    (hTV : Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
      (q.toMeasure.map (spanProj K))) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun n : ℕ => (gibbsMeasure p n.succPNat).map
        (fun X => a * ((∑ j : Fin (K : ℕ), finiteGapBlock X j) - b)))
      (q.toMeasure.map (fun y => a * (gapSequenceSpan y 0 K - b))) := by
  have hc : Continuous (fun y : Gaps => a * (gapSequenceSpan y 0 K - b)) :=
    ((continuous_gapSequenceSpan 0 K).sub continuous_const).const_mul a
  let A : EuclideanSpace ℝ (Fin (K : ℕ)) → ℝ := fun x => a * ((∑ i, x i) - b)
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hspan (y : Gaps) : A (spanProj K y) = a * (gapSequenceSpan y 0 K - b) := by
    dsimp [A, gapSequenceSpan]
    simp only [zero_add]
    exact congrArg (fun x : ℝ => a * (x - b))
      (Fin.sum_univ_eq_sum_range (fun j : ℕ => (y (j : ℤ) : ℝ)) (K : ℕ))
  have hm := (continuous_gap_block_projection_internal K 0).measurable
  have htv : Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw p n.succPNat).toMeasure.map (fun y => a * (gapSequenceSpan y 0 K - b)))
      (q.toMeasure.map (fun y => a * (gapSequenceSpan y 0 K - b)))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTV (fun _ => bot_le)
    intro n
    have hb := NonnegativeTilt.totalVariation_map_le
      ((periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
      (q.toMeasure.map (spanProj K)) A hA
    simpa only [Measure.map_map hA hm, Function.comp_def, hspan] using hb
  have ht := probabilityMeasure_tendsto_of_totalVariation
    (fun n => ProbabilityMeasure.map (periodicGapLaw p n.succPNat)
      (fun y => a * (gapSequenceSpan y 0 K - b)))
    (ProbabilityMeasure.map q (fun y => a * (gapSequenceSpan y 0 K - b))) htv
  refine ⟨fun n => ?_, ?_, fun f => ?_⟩
  · let fluctuationSpanGibbsProbability : IsProbabilityMeasure (gibbsMeasure p n.succPNat) :=
      gibbsMeasure_probability _ _
    exact Measure.isProbabilityMeasure_map_iff (by
      apply Measurable.aemeasurable
      simp_rw [MesoscopicVariance.finiteGapBlock_sum_eq_blockLength]
      exact ((Riesz1.measurable_blockLength 0 K).sub_const _).const_mul _)
      |>.mpr inferInstance
  · exact Measure.isProbabilityMeasure_map_iff hc.measurable.aemeasurable |>.mpr inferInstance
  · have hf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht f
    have he (n : ℕ) :
        (periodicGapLaw p n.succPNat).toMeasure.map
          (fun y => a * (gapSequenceSpan y 0 K - b)) =
        (gibbsMeasure p n.succPNat).map
          (fun X => a * ((∑ j : Fin (K : ℕ), finiteGapBlock X j) - b)) := by
      rw [periodicGapLaw_toMeasure, Measure.map_map hc.measurable
        (measurable_periodicGapSequence n.succPNat)]
      congr 1
      funext X
      simp only [Function.comp_apply, gapSequenceSpan_periodic,
        MesoscopicVariance.finiteGapBlock_sum_eq_blockLength]
    simp only [ProbabilityMeasure.toMeasure_map] at hf
    simp_rw [he] at hf
    exact hf

/-- See the proof of Corollary 1.1 in the paper: first and second moments of a
finite particle block converge to those of its labelled limiting gap span. -/
theorem fixed_window_finite_span_moments_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) (K : ℕ+)
    (hTV : Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
      (q.toMeasure.map (spanProj K))) atTop (𝓝 0)) :
    MemLp (fun y => gapSequenceSpan y 0 K) 2 q ∧
      Tendsto (fun n : ℕ => ∫ X, (∑ j : Fin (K : ℕ), finiteGapBlock X j)
        ∂gibbsMeasure p n.succPNat) atTop (𝓝 (∫ y, gapSequenceSpan y 0 K ∂q)) ∧
      Tendsto (fun n : ℕ => ∫ X, (∑ j : Fin (K : ℕ), finiteGapBlock X j) ^ 2
        ∂gibbsMeasure p n.succPNat) atTop (𝓝 (∫ y, gapSequenceSpan y 0 K ^ 2 ∂q)) := by
  obtain ⟨hspan, hfirst, hsecond⟩ := fixed_window_gap_span_moments_of_totalVariation_internal p q hq K hTV
  have he (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ y, f (gapSequenceSpan y 0 K) ∂periodicGapLaw p n.succPNat) =
        ∫ X, f (∑ j : Fin (K : ℕ), finiteGapBlock X j) ∂gibbsMeasure p n.succPNat := by
    have ht := integral_periodicGapLaw p n.succPNat
      (f := fun y => f (gapSequenceSpan y 0 K))
      (hf.comp (continuous_gapSequenceSpan 0 K).measurable)
    simpa only [gapSequenceSpan_periodic, MesoscopicVariance.finiteGapBlock_sum_eq_blockLength] using ht
  refine ⟨hspan, ?_, ?_⟩
  · exact hfirst.congr' (Eventually.of_forall fun n => he n id measurable_id)
  · simpa only [he _ (fun x => x ^ 2) (by fun_prop)] using hsecond

/-- See the proof of Corollary 1.1 in the paper: the extended variance and its
real value converge for each fixed positive labelled span. -/
theorem fixed_window_gap_span_variance_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) (K : ℕ+)
    (hTV : Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
      (q.toMeasure.map (spanProj K))) atTop (𝓝 0)) :
    ∃ hs : MemLp (fun y => gapSequenceSpan y 0 K) 2 q,
      Tendsto (fun n : ℕ => (Riesz1.variance (gibbsMeasure p n.succPNat)
        (fun X => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
        (MesoscopicVariance.integrable_finiteGapBlock_sum p n.succPNat K)).toReal)
        atTop (𝓝 (Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          (hs.integrable one_le_two)).toReal) ∧
      Tendsto (fun n : ℕ => Riesz1.variance (gibbsMeasure p n.succPNat)
        (fun X => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
        (MesoscopicVariance.integrable_finiteGapBlock_sum p n.succPNat K))
        atTop (𝓝 (Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          (hs.integrable one_le_two))) := by
  obtain ⟨hs, hfirst, hsecond⟩ := fixed_window_finite_span_moments_internal p q hq K hTV
  let fluctuationFixedSpanGibbsProbability (n : ℕ) :
      IsProbabilityMeasure (gibbsMeasure p n.succPNat) := gibbsMeasure_probability _ _
  have ht := variance_tendsto_of_first_second_moments
    (fun n : ℕ => gibbsMeasure p n.succPNat) q.toMeasure
    (fun _ X => ∑ j : Fin (K : ℕ), finiteGapBlock X j) (fun y => gapSequenceSpan y 0 K)
    (fun n => MesoscopicVariance.finiteGapBlock_sum_memLp p n.succPNat K 2) hs hfirst hsecond
  exact ⟨hs, ht⟩

/-- See the proof of Corollary 1.1 in the paper: the reconstructed Palm point
and the limiting labelled span have exactly the same law. This is the bridge
to the rooted carrier, rather than a second definition of a Palm span. -/
theorem rootedPoint_law_eq_gapSequenceSpan_internal
    (q : ProbabilityMeasure Gaps) (hsupport : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences)
    (P : PointProcess)
    (hroot : rootedPalmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructRootedConfiguration)
    (K : ℕ) :
    (rootedPalmMeasure P).map (fun C => rootedPoint C (K : ℤ)) =
      q.toMeasure.map (fun y => gapSequenceSpan y 0 K) := by
  rw [hroot, Measure.map_map (measurable_rootedPoint _) measurable_reconstructRootedConfiguration]
  have he (y : reconstructibleGapSequences) :
      rootedPoint (reconstructRootedConfiguration y) (K : ℤ) = gapSequenceSpan y.val 0 K := by
    rw [rootedPoint_reconstructRootedConfiguration]
    have ht := gapPosition_sub_eq_sum y.val 0 K
    simpa only [zero_add, gapPosition_zero, sub_zero, gapSequenceSpan] using ht
  simp only [Function.comp_def, he]
  have hm : Measurable (fun y : Gaps => gapSequenceSpan y 0 K) :=
    (continuous_gapSequenceSpan 0 K).measurable
  have ht := Measure.map_map (μ := reconstructionGapMeasure q.toMeasure)
    hm (measurable_subtype_coe (p := (· ∈ reconstructibleGapSequences)))
  rw [map_reconstructionGapMeasure q.toMeasure hsupport] at ht
  exact ht.symm

/-- See the proof of Corollary 1.1 in the paper: second moments and the Palm span variance are transported by the actual reconstructed Palm law. -/
theorem palm_span_moments_variance_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (hsupport : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences)
    (P : PointProcess) (hprob : IsProbabilityMeasure (rootedPalmMeasure P))
    (hroot : rootedPalmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructRootedConfiguration)
    (K : ℕ+)
    (hTV : Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw p n.succPNat).toMeasure.map (spanProj K))
      (q.toMeasure.map (spanProj K))) atTop (𝓝 0)) :
    ∃ hs : MemLp (fun C => rootedPoint C (K : ℕ)) 2 (rootedPalmMeasure P),
      palmSpanVariance P K (hs.integrable one_le_two) =
        Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          ((fixed_window_gap_span_moments_of_totalVariation_internal p q hq K hTV).1.integrable one_le_two) := by
  let fluctuationPalmProbability : IsProbabilityMeasure (rootedPalmMeasure P) := hprob
  have he := rootedPoint_law_eq_gapSequenceSpan_internal q hsupport P hroot K
  have hm : Measurable (fun y : Gaps => gapSequenceSpan y 0 K) :=
    (continuous_gapSequenceSpan 0 K).measurable
  have hq2 := (fixed_window_gap_span_moments_of_totalVariation_internal p q hq K hTV).1
  have hi : MemLp (id : ℝ → ℝ) 2 (q.toMeasure.map (fun y => gapSequenceSpan y 0 K)) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr hq2
  rw [← he] at hi
  have hs : MemLp (fun C => rootedPoint C (K : ℕ)) 2 (rootedPalmMeasure P) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (measurable_rootedPoint _).aemeasurable).mp hi
  refine ⟨hs, ?_⟩
  unfold palmSpanVariance
  rw [Riesz1.variance_eq_lintegral_map (measurable_rootedPoint _),
    Riesz1.variance_eq_lintegral_map hm, he]

/-- Corollary 1.1, the stationary paragraph: choose one mesoscopic
volume for the complete normalized count law and the normalized variance. -/
theorem stationary_count_fluctuation_limits_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw (ofLong β s) n.succPNat) atTop (𝓝 q))
    (P : PointProcess)
    (hP : (P : Measure LineConfiguration) =
      gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure))
    (hlocal : LocalConverges (periodicSpatialLaw (ofLong β s)) P) :
    ∃ hc : ∀ a b : ℝ, MemLp (intervalCount a b) 2 (P : Measure LineConfiguration),
      ConvergesInLawAlong (atTop : Filter {R : ℝ // 0 < R})
        (fun R => (P : Measure LineConfiguration).map
          (fun C => R.val ^ (-s.val / 2) * (intervalCount 0 R.val C - R.val)))
        (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) ∧
      Tendsto (fun R : {R : ℝ // 0 < R} => R.val ^ (-s.val) *
        (numberVariance P R.val ((hc 0 R.val).integrable one_le_two)).toReal)
        atTop (𝓝 (Riesz1.countVariance (longParameters β s))) ∧
      Tendsto (fun R : {R : ℝ // 0 < R} => ENNReal.ofReal (R.val ^ (-s.val)) *
        numberVariance P R.val ((hc 0 R.val).integrable one_le_two))
        atTop (𝓝 (ENNReal.ofReal (Riesz1.countVariance (longParameters β s)))) := by
  let hc (a b : ℝ) := (fixed_window_count_moments_internal (ofLong β s) q hq P hP hlocal a b).1
  have hpair := joint_real_law_variance_mesoscopic_limit_internal
    (l := (atTop : Filter {R : ℝ // 0 < R}))
    (F := fun R N => (gibbsMeasure (ofLong β s) N).map
      (fun X => R.val ^ (-s.val / 2) * (finiteIntervalCount N R.val X - R.val)))
    (G := fun R => (P : Measure LineConfiguration).map
      (fun C => R.val ^ (-s.val / 2) * (intervalCount 0 R.val C - R.val)))
    (V := fun R N => R.val ^ (-s.val) *
      (Riesz1.variance (gibbsMeasure (ofLong β s) N) (finiteIntervalCount N R.val)
        (integrable_finiteIntervalCount β s N R.val)).toReal)
    (v := fun R => R.val ^ (-s.val) *
      (numberVariance P R.val ((hc 0 R.val).integrable one_le_two)).toReal)
    (size := fun R => R.val) (scale := fun _ => 1)
    (hscale := fun _ => by norm_num) (hsize := fun R => R.property.le)
    (hfixed := fun R => fixed_window_count_law_internal (ofLong β s) P hlocal
      R.val (R.val ^ (-s.val / 2)) R.val R.property)
    (hvar := fun R => ((fixed_window_count_variance_internal β s q hq P hP hlocal
      R.val R.property).choose_spec.1).const_mul (R.val ^ (-s.val)))
    (Q := Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s))))
    (hQ := by unfold Riesz1.normalLaw; infer_instance)
    (a := Riesz1.countVariance (longParameters β s))
    (hfinite := fun R N hR hratio => by
      have ht := finiteIntervalCount_pairs_limit β s N (fun j => (R j).val)
        (fun j => (R j).property) (tendsto_Ioi_atTop.mp hR) hratio
      exact ⟨ht.2.1, by simpa only [one_mul] using ht.2.2.2⟩)
  have ht := hpair.2
  simp only [one_mul] at ht
  refine ⟨hc, hpair.1, ht, ?_⟩
  have he (R : {R : ℝ // 0 < R}) :
      ENNReal.ofReal (R.val ^ (-s.val) *
        (numberVariance P R.val ((hc 0 R.val).integrable one_le_two)).toReal) =
      ENNReal.ofReal (R.val ^ (-s.val)) *
        numberVariance P R.val ((hc 0 R.val).integrable one_le_two) := by
    unfold numberVariance
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg R.property.le _),
      ENNReal.ofReal_toReal (Riesz1.variance_ne_top_of_memLp _ (hc 0 R.val))]
  simpa only [Function.comp_def, he] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

/-- See the proof of Corollary 1.1 in the paper, the last power comparison.
A finite real number-variance asymptotic with exponent below one gives the
hyperuniformity ratio limit. Square integrability excludes infinite
variances before division by the positive radius. -/
theorem hyperuniformityRatio_tendsto_from_variance_internal
    (P : PointProcess) (s v : ℝ) (hs : s < 1)
    (hc : ∀ R : ℝ, MemLp (intervalCount 0 R) 2 (P : Measure LineConfiguration))
    (hvar : Tendsto (fun R : {R : ℝ // 0 < R} => R.val ^ (-s) *
      (numberVariance P R.val ((hc R.val).integrable one_le_two)).toReal) atTop (𝓝 v)) :
    Tendsto (fun R : {R : ℝ // 0 < R} =>
      hyperuniformityRatio P R ((hc R.val).integrable one_le_two)) atTop (𝓝 0) := by
  have hpower : Tendsto (fun R : {R : ℝ // 0 < R} => R.val ^ (s - 1)) atTop (𝓝 0) := by
    have ht := tendsto_rpow_neg_atTop (sub_pos.mpr hs)
    rw [neg_sub] at ht
    exact tendsto_comp_val_Ioi_atTop.mpr ht
  have ht := hpower.mul hvar
  rw [zero_mul] at ht
  have he (R : {R : ℝ // 0 < R}) :
      ENNReal.ofReal (R.val ^ (s - 1) * (R.val ^ (-s) *
        (numberVariance P R.val ((hc R.val).integrable one_le_two)).toReal)) =
      hyperuniformityRatio P R ((hc R.val).integrable one_le_two) := by
    have hp : R.val ^ (s - 1) * R.val ^ (-s) = R.val⁻¹ := by
      rw [← Real.rpow_add R.property, show s - 1 + -s = -1 by ring, Real.rpow_neg_one]
    unfold hyperuniformityRatio numberVariance
    rw [← mul_assoc, hp, mul_comm R.val⁻¹, ← div_eq_mul_inv, ENNReal.ofReal_div_of_pos R.property,
      ENNReal.ofReal_toReal (Riesz1.variance_ne_top_of_memLp _ (hc R.val))]
  simpa only [Function.comp_def, he, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

/-- Corollary 1.1, the Palm paragraph: one mesoscopic volume
approximates the normalized span law and the unnormalized span variance. -/
theorem labelled_span_fluctuation_limits_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw (ofLong β s) n.succPNat) atTop (𝓝 q))
    (hTV : ∀ k : ℕ, Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw (ofLong β s) n.succPNat).toMeasure.map (spanProj k))
      (q.toMeasure.map (spanProj k))) atTop (𝓝 0)) :
    ∃ hs : ∀ K : ℕ+, MemLp (fun y => gapSequenceSpan y 0 K) 2 q,
      ConvergesInLawAlong (atTop : Filter ℕ+)
        (fun K => q.toMeasure.map
          (fun y => (K : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 0 K - (K : ℝ))))
        (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
          (companionCountVariance_nonneg β s))) ∧
      Tendsto (fun K : ℕ+ => (K : ℝ) ^ (-s.val) *
        (Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          ((hs K).integrable one_le_two)).toReal)
        atTop (𝓝 (Riesz1.countVariance (longParameters β s))) ∧
      Tendsto (fun K : ℕ+ => ENNReal.ofReal ((K : ℝ) ^ (-s.val)) *
        Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          ((hs K).integrable one_le_two))
        atTop (𝓝 (ENNReal.ofReal (Riesz1.countVariance (longParameters β s)))) := by
  let hs (K : ℕ+) := (fixed_window_gap_span_moments_of_totalVariation_internal (ofLong β s) q hq K (hTV K)).1
  have hpair := joint_real_law_variance_mesoscopic_limit_internal
    (l := (atTop : Filter ℕ+))
    (F := fun K N => (gibbsMeasure (ofLong β s) N).map
      (fun X => (K : ℝ) ^ (-s.val / 2) *
        ((∑ j : Fin (K : ℕ), finiteGapBlock X j) - (K : ℝ))))
    (G := fun K => q.toMeasure.map
      (fun y => (K : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 0 K - (K : ℝ))))
    (V := fun K N => (Riesz1.variance (gibbsMeasure (ofLong β s) N)
      (fun X => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
      (MesoscopicVariance.integrable_finiteGapBlock_sum (ofLong β s) N K)).toReal)
    (v := fun K => (Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
      ((hs K).integrable one_le_two)).toReal)
    (size := fun K => (K : ℝ)) (scale := fun K => (K : ℝ) ^ (-s.val))
    (hscale := fun K => by
      rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ (K : ℕ) from K.pos)) (by linarith [s.property.1]))
    (hsize := fun _ => by positivity)
    (hfixed := fun K => fixed_window_gap_span_law_internal (ofLong β s) q K
      ((K : ℝ) ^ (-s.val / 2)) (K : ℝ) (hTV K))
    (hvar := fun K => (fixed_window_gap_span_variance_internal (ofLong β s) q hq K (hTV K)).choose_spec.1)
    (Q := Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
      (companionCountVariance_nonneg β s)))
    (hQ := by unfold Riesz1.normalLaw; infer_instance)
    (a := Riesz1.countVariance (longParameters β s))
    (hfinite := fun K N hK hratio => by
      have hK' := tendsto_PNat_val_atTop_atTop.comp hK
      have hclt := mesoscopic_gapCLT_pairs β s N (fun j => (K j : ℕ)) hK' hratio
      have ht := mesoscopic_finiteGapBlock_variance_limit β s N K hK' hratio
      have he (K : ℕ+) (x : ℝ) : (K : ℝ) ^ (-s.val) * x = x / (K : ℝ) ^ s.val := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (K : ℝ)), div_eq_mul_inv]
        ring
      exact ⟨by simpa only [cyclicGapSum_zero_eq_finiteGapBlock] using hclt,
        by simpa only [he] using ht⟩)
  have ht := hpair.2
  refine ⟨hs, hpair.1, ht, ?_⟩
  have he (K : ℕ+) :
      ENNReal.ofReal ((K : ℝ) ^ (-s.val) *
        (Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          ((hs K).integrable one_le_two)).toReal) =
      ENNReal.ofReal ((K : ℝ) ^ (-s.val)) *
        Riesz1.variance q.toMeasure (fun y => gapSequenceSpan y 0 K)
          ((hs K).integrable one_le_two) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ENNReal.ofReal_toReal (Riesz1.variance_ne_top_of_memLp _ (hs K))]
  simpa only [Function.comp_def, he] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

/-- See the proof of Corollary 1.1 in the paper: both Palm limits in precisely
the companion natural-index convention used by the corollary. The Palm
probability and reconstruction identity are the conclusions of Palm inversion. All span second moments are concluded here. -/
theorem palm_span_fluctuation_limits_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw (ofLong β s) n.succPNat) atTop (𝓝 q))
    (hTV : ∀ k : ℕ, Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw (ofLong β s) n.succPNat).toMeasure.map (spanProj k))
      (q.toMeasure.map (spanProj k))) atTop (𝓝 0))
    (hsupport : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences)
    (P : PointProcess) (hprob : IsProbabilityMeasure (rootedPalmMeasure P))
    (hroot : rootedPalmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructRootedConfiguration) :
    ∃ hs : ∀ K : ℕ+, MemLp (fun C => rootedPoint C (K : ℕ)) 2 (rootedPalmMeasure P),
      Riesz1.ConvergesInLaw
        (fun n => let K := Riesz1.particleNumber n
          (rootedPalmMeasure P).map (fun C =>
            (K : ℝ) ^ (-s.val / 2) * (rootedPoint C (K : ℕ) - (K : ℝ))))
        (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
          (companionCountVariance_nonneg β s))) ∧
      Tendsto (fun n : ℕ => let K := Riesz1.particleNumber n
        ENNReal.ofReal ((K : ℝ) ^ (-s.val)) *
          palmSpanVariance P K ((hs K).integrable one_le_two)) atTop
        (𝓝 (ENNReal.ofReal (Riesz1.countVariance (longParameters β s)))) := by
  let hs (K : ℕ+) := (palm_span_moments_variance_internal
    (ofLong β s) q hq hsupport P hprob hroot K (hTV K)).choose
  have hvariance (K : ℕ+) := (palm_span_moments_variance_internal
    (ofLong β s) q hq hsupport P hprob hroot K (hTV K)).choose_spec
  have he (K : ℕ+) :
      (rootedPalmMeasure P).map (fun C =>
        (K : ℝ) ^ (-s.val / 2) * (rootedPoint C (K : ℕ) - (K : ℝ))) =
      q.toMeasure.map (fun y =>
        (K : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 0 K - (K : ℝ))) := by
    have hm : Measurable (fun x : ℝ => (K : ℝ) ^ (-s.val / 2) * (x - (K : ℝ))) := by fun_prop
    have ht := congrArg (fun ρ : Measure ℝ => ρ.map
      (fun x => (K : ℝ) ^ (-s.val / 2) * (x - (K : ℝ))))
      (rootedPoint_law_eq_gapSequenceSpan_internal q hsupport P hroot K)
    simpa only [Measure.map_map hm (measurable_rootedPoint _),
      Measure.map_map hm (continuous_gapSequenceSpan 0 K).measurable, Function.comp_def] using ht
  have hn : Tendsto Riesz1.particleNumber atTop (atTop : Filter ℕ+) := by
    apply tendsto_Ioi_atTop.mpr
    simpa only [Riesz1.particleNumber, PNat.mk_coe] using (tendsto_add_atTop_nat 1)
  obtain ⟨hg, hclt, _, hv⟩ := labelled_span_fluctuation_limits_internal β s q hq hTV
  refine ⟨hs, ?_, ?_⟩
  · unfold Riesz1.ConvergesInLaw
    simp only [he]
    exact ⟨fun n => hclt.1 _, hclt.2.1, fun f => (hclt.2.2 f).comp hn⟩
  · simpa only [Function.comp_def, hvariance] using hv.comp hn

/-- See the proof of Theorem 3 in the paper: its almost-sure average
clause puts the limiting gap law on the exact reconstruction carrier. This
uses only weak convergence to that law and the rigidity theorem. -/
theorem gap_limit_reconstructible_from_weak_limit_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) :
    ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences := by
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop := by
    simpa only [V, Nat.succPNat_coe, Nat.add_assoc, one_add_one_eq_two] using
      (tendsto_add_atTop_nat 2)
  have hqV := (tendsto_add_atTop_iff_nat 1).mpr hq
  filter_upwards [periodicGapLaw_limit_averages p V hV hVtop q hqV] with y hy
  exact mem_reconstructibleGapSequences_of_divergent_sums y
    (gapSequenceSpan_diverges_of_average_internal y (fun _ => 0) hy.1)
    (gapSequenceSpan_diverges_of_average_internal y (fun k => -(k : ℤ)) hy.2)

/-- The conclusion of Corollary 1.1 follows from weak gap convergence,
finite-block total variation convergence, suspension, periodic local total
variation convergence and rooted Palm identification. The variance parameter
can be `v` from the statement of the corollary. Count/span second moments,
both central limit theorems, both extended variance asymptotics and the
hyperuniformity ratio limit are conclusions. -/
theorem fixed_window_fluctuation_transfer_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw (ofLong β s) n.succPNat) atTop (𝓝 q))
    (hTV : ∀ k : ℕ, Tendsto (fun n : ℕ => totalVariation
      ((periodicGapLaw (ofLong β s) n.succPNat).toMeasure.map (spanProj k))
      (q.toMeasure.map (spanProj k))) atTop (𝓝 0))
    (P : PointProcess)
    (hP : (P : Measure LineConfiguration) =
      gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure))
    (hlocal : LocalConverges (periodicSpatialLaw (ofLong β s)) P)
    (hprob : IsProbabilityMeasure (rootedPalmMeasure P))
    (hroot : rootedPalmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructRootedConfiguration)
    (v : ℝ≥0) (hv : (v : ℝ) = Riesz1.countVariance (longParameters β s)) :
    ∃ hc : ∀ a b : ℝ, MemLp (intervalCount a b) 2 (P : Measure LineConfiguration),
    ∃ hs : ∀ K : ℕ+, MemLp (fun C => rootedPoint C (K : ℕ)) 2 (rootedPalmMeasure P),
      ConvergesInLawAlong (atTop : Filter {R : ℝ // 0 < R})
        (fun R => (P : Measure LineConfiguration).map
          (fun C => R.val ^ (-s.val / 2) * (intervalCount 0 R.val C - R.val)))
        (Riesz1.normalLaw v) ∧
      Tendsto (fun R : {R : ℝ // 0 < R} => ENNReal.ofReal (R.val ^ (-s.val)) *
        numberVariance P R.val ((hc 0 R.val).integrable one_le_two)) atTop (𝓝 (v : ℝ≥0∞)) ∧
      Riesz1.ConvergesInLaw
        (fun n => let K := Riesz1.particleNumber n
          (rootedPalmMeasure P).map (fun C =>
            (K : ℝ) ^ (-s.val / 2) * (rootedPoint C (K : ℕ) - (K : ℝ))))
        (Riesz1.normalLaw v) ∧
      Tendsto (fun n : ℕ => let K := Riesz1.particleNumber n
        ENNReal.ofReal ((K : ℝ) ^ (-s.val)) *
          palmSpanVariance P K ((hs K).integrable one_le_two)) atTop (𝓝 (v : ℝ≥0∞)) ∧
      Tendsto (fun R : {R : ℝ // 0 < R} =>
        hyperuniformityRatio P R ((hc 0 R.val).integrable one_le_two)) atTop (𝓝 0) := by
  have hsupport := gap_limit_reconstructible_from_weak_limit_internal (ofLong β s) q hq
  obtain ⟨hc, hcountCLT, hreal, hvariance⟩ := stationary_count_fluctuation_limits_internal β s q hq P hP hlocal
  obtain ⟨hs, hpalmCLT, hpalmVar⟩ :=
    palm_span_fluctuation_limits_internal β s q hq hTV hsupport P hprob hroot
  have hvn : Real.toNNReal (Riesz1.countVariance (longParameters β s)) = v := by
    rw [← hv, Real.toNNReal_coe]
  have hvmk : NNReal.mk (Riesz1.countVariance (longParameters β s))
      (companionCountVariance_nonneg β s) = v := by
    apply NNReal.coe_injective
    exact hv.symm
  have hve : ENNReal.ofReal (Riesz1.countVariance (longParameters β s)) = (v : ℝ≥0∞) := by
    rw [← hv]
    exact ENNReal.ofReal_coe_nnreal
  refine ⟨hc, hs, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hvn] using hcountCLT
  · simpa only [hve] using hvariance
  · simpa only [hvmk] using hpalmCLT
  · simpa only [hve] using hpalmVar
  · exact hyperuniformityRatio_tendsto_from_variance_internal P s.val _ s.property.2
      (fun R => hc 0 R) hreal

end Riesz2
