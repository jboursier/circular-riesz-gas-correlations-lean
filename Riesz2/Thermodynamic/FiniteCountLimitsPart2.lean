/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FiniteCountLimits
public import Riesz2.Bridges.GapFluctuations
public import Riesz2.Frozen.IntervalCount
public import Riesz2.Frozen.MicroscopicConfiguration
public import Riesz2.ToMathlib.SequenceExtensionLimits
public import Riesz1.CLT.GapsDiscCountsZero
public import Riesz1.CLT.GapsDiscRotation
public import Riesz1.CLT.GapsDiscStripsShift
public import Riesz2.ToMathlib.WeakLawScaling
public import Riesz1.ToMathlib.VarianceLawTransfer
import Riesz2.Sanity.FiniteLaws

/-!
# Arbitrary-pair interval central limit theorem

The full-volume companion CLT is transferred to arbitrary pairs of particle numbers and
scales, as required in the proof of Corollary 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal NNReal

namespace Riesz2

/-- Positive integer sizes tend to infinity as real numbers. -/
lemma tendsto_size_real : Tendsto (fun N : ℕ+ => (N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop

/-- The companion square-root filler scale tends to zero. -/
lemma sqrtScale_tendsto_zero :
    Tendsto (fun N : ℕ+ => (Riesz1.sqrtScale N).val) atTop (𝓝 0) := by
  simpa only [Riesz1.sqrtScale, one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_size_real)

/-- The companion square-root filler scale is mesoscopic. -/
lemma sqrtScale_mesoscopic :
    Tendsto (fun N : ℕ+ => (N : ℝ) * (Riesz1.sqrtScale N).val) atTop atTop := by
  convert Real.tendsto_sqrt_atTop.comp tendsto_size_real using 1
  funext N
  change (N : ℝ) * (1 / Real.sqrt (N : ℝ)) = Real.sqrt (N : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hs := Real.mul_self_sqrt hN.le
  have hp := (Real.sqrt_pos.mpr hN).ne'
  field_simp
  nlinarith [hs]

/-- A mesoscopic pair of positive scales forces the volumes to infinity. -/
lemma scale_pairs_sizes_tendsto (N : ℕ → ℕ+) (ℓ : ℕ → Riesz1.Scale)
    (hK : Tendsto (fun j => (N j : ℝ) * (ℓ j).val) atTop atTop) :
    Tendsto N atTop atTop := by
  have hNr : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun j => mul_le_of_le_one_right (by positivity) (ℓ j).property.2) hK
  have hNn := tendsto_natCast_atTop_iff.mp hNr
  exact tendsto_atTop.mpr fun M => hNn.eventually_ge_atTop (M : ℕ)

/-- See the proof of Corollary 1.1 in the paper: the centered interval CLT along arbitrary
pairs of volumes and admissible scales. No monotonicity of the volumes is assumed. -/
theorem intervalCLT_pairs (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (ℓ : ℕ → Riesz1.Scale)
    (hℓ : Tendsto (fun j => (ℓ j).val) atTop (𝓝 0))
    (hK : Tendsto (fun j => (N j : ℝ) * (ℓ j).val) atTop atTop) :
    ConvergesInLawAlong atTop
      (fun j => (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => ((N j : ℝ) * (ℓ j).val) ^ (-s.val / 2) *
          intervalFluctuation (ℓ j) (N j) X))
      (ProbabilityTheory.gaussianReal 0 (intervalLineVariance β s).toNNReal) := by
  refine ⟨fun j => ?_, by infer_instance, fun f => ?_⟩
  · dsimp only
    have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) (N j)) := by
      rw [gibbsMeasure_ofLong]
      exact (Riesz1.modelWellDefined (longParameters β s) (N j)).2.2
    exact (Measure.isProbabilityMeasure_map_iff
      ((memLp_intervalFluctuation β s (N j) (ℓ j)).aestronglyMeasurable.aemeasurable.const_mul _)).mpr
      inferInstance
  · exact tendsto_pairs_of_sections
      (fun (_ : ℕ+) (a : Riesz1.Scale) => a.val)
      (fun N (a : Riesz1.Scale) => (N : ℝ) * a.val)
      (fun N (a : Riesz1.Scale) => ∫ x, f x ∂((gibbsMeasure (ofLong β s) N).map
        (fun X => ((N : ℝ) * a.val) ^ (-s.val / 2) * intervalFluctuation a N X)))
      (𝓝 0) atTop _ Riesz1.sqrtScale sqrtScale_tendsto_zero sqrtScale_mesoscopic
      (fun a ha hNa => (intervalCLT β s a ha hNa).2.2 f)
      N ℓ (scale_pairs_sizes_tendsto N ℓ hK) hℓ hK

/-- The finite count of the paper on `(0,R/N]`, using the central circle representatives.
For `0 < R < N/2` this is the unambiguous positive half-circle interval. The same formula
counts the indicated interval for every real `R`. No exceptional-size convention is used. -/
def finiteIntervalCount (N : ℕ+) (R : ℝ) (X : Riesz1.Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), (Set.Ioc (0 : ℝ) (R / (N : ℝ))).indicator (fun _ => (1 : ℝ))
    (Riesz1.centralRep Riesz1.unitLength (X.val i : UnitAddCircle))

/-- Measurability of the literal central representative. -/
lemma measurable_unitCentralRep : Measurable (Riesz1.centralRep Riesz1.unitLength) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) (-(1 : ℝ) / 2)).measurable

/-- The positive half-open interval and its open arc differ only at their right endpoint. -/
lemma positiveIntervalProfile_ae_arc (t : ℝ) (ht : 0 < t) (ht1 : t < 1 / 2) :
    (fun x : UnitAddCircle => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ))
      (Riesz1.centralRep Riesz1.unitLength x)) =ᵐ[volume]
      Riesz1.arcIndicator ((t / 2 : ℝ) : UnitAddCircle) (t / 2) := by
  have hn : ∀ᵐ x : UnitAddCircle ∂volume, x ≠ (t : UnitAddCircle) :=
    measure_eq_zero_iff_ae_notMem.mp (Riesz1.addCircle_volume_singleton 1 _)
  filter_upwards [hn] with x hx
  let u := Riesz1.centralRep Riesz1.unitLength x
  have hu := centralRep_mem_Ico_unit x
  have hux : (u : UnitAddCircle) = x := FrozenSanity.centralRep_cast x
  have hne : u ≠ t := by intro h; exact hx (hux.symm.trans (congrArg (fun z : ℝ => (z : UnitAddCircle)) h))
  have hd : dist x ((t / 2 : ℝ) : UnitAddCircle) < t / 2 ↔ 0 < u ∧ u < t := by
    rw [← hux, Riesz1.dist_coe_lt_iff_abs_lt u (t / 2) (t / 2) hu.1 hu.2
      (by rw [abs_of_pos (by positivity)]; linarith) (by positivity), abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold Riesz1.arcIndicator
  by_cases h : 0 < u ∧ u < t
  · have hm : Riesz1.centralRep Riesz1.unitLength x ∈ Set.Ioc (0 : ℝ) t := ⟨h.1, h.2.le⟩
    rw [ite_eq_left (hd.mpr h), Set.indicator_of_mem hm]
  · rw [ite_eq_right (fun h' => h (hd.mp h')), Set.indicator_of_notMem]
    rintro ⟨h1, h2⟩
    exact h ⟨h1, lt_of_le_of_ne h2 hne⟩

/-- Every finite interval count has a finite second moment. -/
lemma memLp_finiteIntervalCount (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (R : ℝ) :
    MemLp (finiteIntervalCount N R) 2 (gibbsMeasure (ofLong β s) N) := by
  have hμ : gibbsMeasure (ofLong β s) N = Riesz1.gibbsMeasure (longParameters β s) N :=
    gibbsMeasure_ofLong β s N
  rw [hμ]
  have : IsProbabilityMeasure (Riesz1.gibbsMeasure (longParameters β s) N) :=
    (Riesz1.modelWellDefined (longParameters β s) N).2.2
  unfold finiteIntervalCount
  apply memLp_finsetSum
  intro i _
  have hm : Measurable (fun X : Riesz1.Configuration N =>
      (Set.Ioc (0 : ℝ) (R / (N : ℝ))).indicator (fun _ => (1 : ℝ))
        (Riesz1.centralRep Riesz1.unitLength (X.val i : UnitAddCircle))) :=
    ((measurable_const.indicator measurableSet_Ioc).comp measurable_unitCentralRep).comp
      (Riesz1.measurable_coord N i)
  exact MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun X => by
    simpa only [norm_one] using (norm_indicator_le_norm_self
      (s := Set.Ioc (0 : ℝ) (R / (N : ℝ))) (f := fun _ => (1 : ℝ))
      (a := Riesz1.centralRep Riesz1.unitLength (X.val i : UnitAddCircle))))

/-- Rotating an open arc preserves the law of its count. This reuses the companion's
rotation identity, including singleton systems. -/
lemma arcCount_law_eq_zero (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (c : UnitAddCircle) (a : ℝ) :
    (gibbsMeasure (ofLong β s) N).map (Riesz1.arcCount c a) =
      (gibbsMeasure (ofLong β s) N).map (Riesz1.arcCount 0 a) := by
  rw [gibbsMeasure_ofLong]
  let P := longParameters β s
  change (Riesz1.gibbsMeasure P N).map _ = (Riesz1.gibbsMeasure P N).map _
  have : IsProbabilityMeasure (Riesz1.gibbsMeasure P N) :=
    (Riesz1.modelWellDefined P N).2.2
  have hm (c : UnitAddCircle) : Measurable (Riesz1.arcCount (N := N) c a) := by
    change Measurable (Riesz1.linearStatistic (Riesz1.arcIndicator c a))
    exact Finset.measurable_sum _ fun i _ =>
      (Riesz1.measurable_arcIndicator c a).comp (Riesz1.measurable_coord N i)
  have : IsProbabilityMeasure ((Riesz1.gibbsMeasure P N).map (Riesz1.arcCount c a)) :=
    (Measure.isProbabilityMeasure_map_iff (hm c).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure ((Riesz1.gibbsMeasure P N).map (Riesz1.arcCount 0 a)) :=
    (Measure.isProbabilityMeasure_map_iff (hm 0).aemeasurable).mpr inferInstance
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (hm c).aemeasurable f.continuous.aestronglyMeasurable,
    integral_map (hm 0).aemeasurable f.continuous.aestronglyMeasurable]
  have h := Riesz1.integral_rotate_linearStatistic P N (Riesz1.arcIndicator 0 a) (-c)
    f f.continuous.measurable (Riesz1.measurable_arcIndicator 0 a)
  have he : (fun x => Riesz1.arcIndicator 0 a (x + -c)) = Riesz1.arcIndicator c a := by
    funext x
    simpa only [sub_eq_add_neg] using (Riesz1.arcIndicator_eq_arcIndicator_zero_sub a c x).symm
  rw [he] at h
  exact h

/-- See the proof of Corollary 1.1 in the paper: the law of the finite half-open count
is exactly that of the centered half-open count plus its deterministic centering. -/
theorem finiteIntervalCount_centered_law (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ℓ : Riesz1.Scale) (hℓ : ℓ.val < 1) :
    (gibbsMeasure (ofLong β s) N).map
      (fun X => finiteIntervalCount N ((N : ℝ) * ℓ.val / 2) X - (N : ℝ) * ℓ.val / 2) =
    (gibbsMeasure (ofLong β s) N).map (intervalFluctuation ℓ N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have he : ((N : ℝ) * ℓ.val / 2) / (N : ℝ) = ℓ.val / 2 := by field_simp
  have ha := Riesz1.linearStatistic_ae_eq (longParameters β s) N
    (positiveIntervalProfile_ae_arc (ℓ.val / 2) (by positivity [ℓ.property.1]) (by linarith))
  have hμ : gibbsMeasure (ofLong β s) N = Riesz1.gibbsMeasure (longParameters β s) N :=
    gibbsMeasure_ofLong β s N
  rw [← hμ] at ha
  have hcount : finiteIntervalCount N ((N : ℝ) * ℓ.val / 2) =ᵐ[gibbsMeasure (ofLong β s) N]
      Riesz1.arcCount ((ℓ.val / 4 : ℝ) : UnitAddCircle) (ℓ.val / 4) := by
    filter_upwards [ha] with X hX
    change (∑ i, (Set.Ioc (0 : ℝ) (((N : ℝ) * ℓ.val / 2) / (N : ℝ))).indicator
      (fun _ => (1 : ℝ)) (Riesz1.centralRep Riesz1.unitLength (X.val i : UnitAddCircle))) = _
    rw [he]
    change Riesz1.linearStatistic (fun x => (Set.Ioc (0 : ℝ) (ℓ.val / 2)).indicator
      (fun _ => (1 : ℝ)) (Riesz1.centralRep Riesz1.unitLength x)) X =
      Riesz1.linearStatistic (Riesz1.arcIndicator ((ℓ.val / 4 : ℝ) : UnitAddCircle) (ℓ.val / 4)) X
    simpa only [show ℓ.val / 2 / 2 = ℓ.val / 4 by ring] using hX
  have hcenter := Riesz1.linearStatistic_ae_eq (longParameters β s) N
    (intervalProfile_ae_arcIndicator ℓ)
  rw [← hμ] at hcenter
  have hm (c : UnitAddCircle) : Measurable (Riesz1.arcCount (N := N) c (ℓ.val / 4)) := by
    change Measurable (Riesz1.linearStatistic (Riesz1.arcIndicator c (ℓ.val / 4)))
    exact Finset.measurable_sum _ fun i _ =>
      (Riesz1.measurable_arcIndicator c (ℓ.val / 4)).comp (Riesz1.measurable_coord N i)
  calc
    _ = ((gibbsMeasure (ofLong β s) N).map
        (Riesz1.arcCount ((ℓ.val / 4 : ℝ) : UnitAddCircle) (ℓ.val / 4))).map
          (fun x => x - (N : ℝ) * ℓ.val / 2) := by
      rw [Measure.map_map (by fun_prop) (hm _)]
      exact Measure.map_congr (hcount.mono (fun X hX => congrArg (fun x : ℝ => x - (N : ℝ) * ℓ.val / 2) hX))
    _ = ((gibbsMeasure (ofLong β s) N).map (Riesz1.arcCount 0 (ℓ.val / 4))).map
          (fun x => x - (N : ℝ) * ℓ.val / 2) := by rw [arcCount_law_eq_zero]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (hm _)]
      apply Measure.map_congr
      filter_upwards [hcenter] with X hX
      exact congrArg (fun x => x - (N : ℝ) * ℓ.val / 2) hX.symm

/-- The finite count is measurable for every interval, including empty intervals. -/
lemma measurable_finiteIntervalCount (N : ℕ+) (R : ℝ) :
    Measurable (finiteIntervalCount N R) := by
  unfold finiteIntervalCount
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_const.indicator measurableSet_Ioc).comp measurable_unitCentralRep).comp
      (Riesz1.measurable_coord N i)

/-- The finite count has its first moment before any variance is formed. -/
lemma integrable_finiteIntervalCount (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (R : ℝ) :
    Integrable (finiteIntervalCount N R) (gibbsMeasure (ofLong β s) N) := by
  have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) N) := by
    rw [gibbsMeasure_ofLong]
    exact (Riesz1.modelWellDefined (longParameters β s) N).2.2
  exact (memLp_finiteIntervalCount β s N R).integrable one_le_two

/-- Measurability of the half-open fluctuation. -/
lemma measurable_intervalFluctuation (N : ℕ+) (ℓ : Riesz1.Scale) :
    Measurable (intervalFluctuation ℓ N) := by
  have hp : Measurable (intervalProfile ℓ) := by
    have he : intervalProfile ℓ = fun x =>
        (Set.Ioc (-(ℓ.val / 4)) (ℓ.val / 4)).indicator (fun _ => (1 : ℝ))
          (Riesz1.centralRep Riesz1.unitLength x) := funext (intervalProfile_eq_indicator ℓ)
    rw [he]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_unitCentralRep
  unfold intervalFluctuation
  exact (Finset.measurable_sum _ fun i _ => hp.comp (Riesz1.measurable_coord N i)).sub_const _

/-- Subtracting a constant and rotating the interval preserves its variance. -/
theorem finiteIntervalCount_variance_eq (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ℓ : Riesz1.Scale) (hℓ : ℓ.val < 1) :
    Riesz1.variance (gibbsMeasure (ofLong β s) N)
      (finiteIntervalCount N ((N : ℝ) * ℓ.val / 2))
      (integrable_finiteIntervalCount β s N _) =
    Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N)
      (integrable_intervalFluctuation β s N ℓ) := by
  let μ := gibbsMeasure (ofLong β s) N
  have : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [gibbsMeasure_ofLong]
    exact (Riesz1.modelWellDefined (longParameters β s) N).2.2
  have hC := memLp_finiteIntervalCount β s N ((N : ℝ) * ℓ.val / 2)
  have hI := integrable_finiteIntervalCount β s N ((N : ℝ) * ℓ.val / 2)
  change MemLp (finiteIntervalCount N ((N : ℝ) * ℓ.val / 2)) 2 μ at hC
  have hCs := hC.sub (memLp_const ((N : ℝ) * ℓ.val / 2))
  change MemLp (fun X => finiteIntervalCount N ((N : ℝ) * ℓ.val / 2) X -
    (N : ℝ) * ℓ.val / 2) 2 μ at hCs
  have hIs := hI.sub (integrable_const ((N : ℝ) * ℓ.val / 2))
  have hc : Riesz1.variance μ (finiteIntervalCount N ((N : ℝ) * ℓ.val / 2)) hI =
      Riesz1.variance μ (fun X => finiteIntervalCount N ((N : ℝ) * ℓ.val / 2) X -
        (N : ℝ) * ℓ.val / 2) hIs := by
    rw [Riesz1.variance, Riesz1.variance,
      ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ← ProbabilityTheory.ofReal_variance hC, ← ProbabilityTheory.ofReal_variance hCs,
      ProbabilityTheory.variance_sub_const hC.aestronglyMeasurable]
  rw [hc]
  exact Riesz1.variance_eq_of_map_eq
    ((measurable_finiteIntervalCount N _).sub_const _) (measurable_intervalFluctuation N ℓ)
    (finiteIntervalCount_centered_law β s N ℓ hℓ) hIs (integrable_intervalFluctuation β s N ℓ)

/-- The deterministic scaling of the companion Gaussian gives exactly the source variance. -/
lemma intervalGaussian_map_radius (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    (ProbabilityTheory.gaussianReal 0 (intervalLineVariance β s).toNNReal).map
      (fun x => (2 : ℝ) ^ (s.val / 2) * x) =
      Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s))) := by
  have hC := companionCountVariance_nonneg β s
  have hV : (intervalLineVariance β s).toReal =
      (2 : ℝ) ^ (-s.val) * Riesz1.countVariance (longParameters β s) := by
    rw [intervalLineVariance_eq_cot]
    change (ENNReal.ofReal ((2 : ℝ) ^ (-s.val) *
      Riesz1.countVariance (longParameters β s))).toReal = _
    exact ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC)
  have hp : ((2 : ℝ) ^ (s.val / 2)) ^ 2 = (2 : ℝ) ^ s.val := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hn := Riesz1.normalLaw_map_mul_real ((2 : ℝ) ^ (s.val / 2))
    (intervalLineVariance β s).toReal (Riesz1.countVariance (longParameters β s))
    ENNReal.toReal_nonneg hC (by
      rw [hp, hV, ← mul_assoc, ← Real.rpow_add two_pos]
      simp)
  have he : Real.toNNReal (intervalLineVariance β s).toReal = (intervalLineVariance β s).toNNReal := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ ENNReal.toReal_nonneg
  simpa only [Riesz1.normalLaw, he] using hn

/-- The centered half-open count CLT with microscopic interval length `Nℓ/2`. -/
theorem intervalCLT_radius_pairs (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (ℓ : ℕ → Riesz1.Scale)
    (hℓ : Tendsto (fun j => (ℓ j).val) atTop (𝓝 0))
    (hK : Tendsto (fun j => (N j : ℝ) * (ℓ j).val) atTop atTop) :
    ConvergesInLawAlong atTop
      (fun j => (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => ((N j : ℝ) * (ℓ j).val / 2) ^ (-s.val / 2) *
          intervalFluctuation (ℓ j) (N j) X))
      (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) := by
  have h := convergesInLawAlong_map_mul (intervalCLT_pairs β s N ℓ hℓ hK)
    (tendsto_const_nhds (x := (2 : ℝ) ^ (s.val / 2)))
  rw [intervalGaussian_map_radius] at h
  convert h using 1
  funext j
  rw [Measure.map_map (by fun_prop) ((measurable_intervalFluctuation (N j) (ℓ j)).const_mul _)]
  congr 1
  funext X
  dsimp only [Function.comp_def]
  rw [Real.div_rpow (by positivity [(ℓ j).property.1] : 0 ≤ (N j : ℝ) * (ℓ j).val)
    (by norm_num : (0 : ℝ) ≤ 2), show -s.val / 2 = -(s.val / 2) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  ring

/-- See the proof of Corollary 1.1 in the paper, finite-count CLT and variance limit
for every pair of positive radii and positive integer volumes with `R → ∞` and `R/N → 0`.
First and second moments are supplied at every index, before the real variance limit. -/
theorem finiteIntervalCount_pairs_limit (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (R : ℕ → ℝ) (hR : ∀ j, 0 < R j)
    (hRTop : Tendsto R atTop atTop)
    (hRN : Tendsto (fun j => R j / (N j : ℝ)) atTop (𝓝 0)) :
    (∀ j, MemLp (finiteIntervalCount (N j) (R j)) 2 (gibbsMeasure (ofLong β s) (N j))) ∧
    ConvergesInLawAlong atTop
      (fun j => (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => (R j) ^ (-s.val / 2) * (finiteIntervalCount (N j) (R j) X - R j)))
      (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) ∧
    (∀ j, Riesz1.variance (gibbsMeasure (ofLong β s) (N j))
      (finiteIntervalCount (N j) (R j)) (integrable_finiteIntervalCount β s (N j) (R j)) < ⊤) ∧
    Tendsto (fun j => (R j) ^ (-s.val) *
      (Riesz1.variance (gibbsMeasure (ofLong β s) (N j))
        (finiteIntervalCount (N j) (R j)) (integrable_finiteIntervalCount β s (N j) (R j))).toReal)
      atTop (𝓝 (Riesz1.countVariance (longParameters β s))) := by
  have hN : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast (N j).pos
  let ℓ : ℕ → Riesz1.Scale := fun j =>
    ⟨min (2 * (R j / (N j : ℝ))) 1, lt_min (mul_pos two_pos (div_pos (hR j) (hN j))) zero_lt_one, min_le_right _ _⟩
  have he : ∀ᶠ j in atTop, (ℓ j).val = 2 * (R j / (N j : ℝ)) ∧ (ℓ j).val < 1 := by
    filter_upwards [hRN.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
      with j hj
    have hsmall : 2 * (R j / (N j : ℝ)) < 1 := by linarith
    exact ⟨min_eq_left hsmall.le, by change min _ 1 < 1; rw [min_eq_left hsmall.le]; exact hsmall⟩
  have hℓ : Tendsto (fun j => (ℓ j).val) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => 2 * (R j / (N j : ℝ))) atTop (𝓝 0) := by
      simpa using hRN.const_mul 2
    apply ht.congr'
    exact he.mono fun _ h => h.1.symm
  have hprod : ∀ᶠ j in atTop, (N j : ℝ) * (ℓ j).val = 2 * R j := by
    filter_upwards [he] with j hj
    rw [hj.1]
    field_simp
  have hmass : Tendsto (fun j => (N j : ℝ) * (ℓ j).val) atTop atTop :=
    (hRTop.const_mul_atTop two_pos).congr' (hprod.mono fun _ h => h.symm)
  have heR : ∀ᶠ j in atTop, (N j : ℝ) * (ℓ j).val / 2 = R j := by
    filter_upwards [hprod] with j hj
    rw [hj]
    ring
  have hc := intervalCLT_radius_pairs β s N ℓ hℓ hmass
  have hv := (intervalVariance_radius_pairs_limit β s N ℓ hℓ hmass).2
  refine ⟨fun j => memLp_finiteIntervalCount β s (N j) (R j),
    ⟨fun j => ?_, hc.2.1, fun f => ?_⟩, fun j => ?_, ?_⟩
  · dsimp only
    have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) (N j)) := by
      rw [gibbsMeasure_ofLong]
      exact (Riesz1.modelWellDefined (longParameters β s) (N j)).2.2
    exact (Measure.isProbabilityMeasure_map_iff
      (((measurable_finiteIntervalCount (N j) (R j)).sub_const _).const_mul _).aemeasurable).mpr
      inferInstance
  · apply (hc.2.2 f).congr'
    filter_upwards [he, heR] with j hj hRj
    have hlaw := congrArg (fun μ : Measure ℝ => μ.map (fun x => (R j) ^ (-s.val / 2) * x))
      (finiteIntervalCount_centered_law β s (N j) (ℓ j) hj.2)
    rw [Measure.map_map (by fun_prop) ((measurable_finiteIntervalCount (N j) _).sub_const _),
      Measure.map_map (by fun_prop) (measurable_intervalFluctuation (N j) (ℓ j))] at hlaw
    simpa only [hRj, Function.comp_def] using congrArg (fun μ : Measure ℝ => ∫ x, f x ∂μ) hlaw.symm
  · have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) (N j)) := by
      rw [gibbsMeasure_ofLong]
      exact (Riesz1.modelWellDefined (longParameters β s) (N j)).2.2
    exact (Riesz1.variance_ne_top_of_memLp _ (memLp_finiteIntervalCount β s (N j) (R j))).lt_top
  · apply hv.congr'
    filter_upwards [he, heR] with j hj hRj
    have hvj := finiteIntervalCount_variance_eq β s (N j) (ℓ j) hj.2
    simpa only [hRj, hvj] using congrArg
      (fun v : ℝ≥0∞ => (R j) ^ (-s.val) * v.toReal) hvj.symm

/-- See the proof of Corollary 1.1 in the paper, including the Fourier integral,
unit-profile normalization, and both limits along every mesoscopic pair. -/
theorem hyper_riesz_finite_counts (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    (Integrable (fun u : ℝ => |u| ^ (1 - s.val) *
      ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2) ∧
      (∫ u : ℝ, |u| ^ (1 - s.val) *
        ‖𝓕 (fun x : ℝ => (unitIntervalIndicator x : ℂ)) u‖ ^ 2) =
      (2 * Real.pi) ^ s.val /
        (2 * Real.pi * Real.Gamma (1 + s.val) * Real.sin (Real.pi * s.val / 2))) ∧
    (Riesz1.lineVariance (longParameters β s) unitIntervalL2 =
      ENNReal.ofReal (Riesz1.countVariance (longParameters β s)) ∧
      Riesz1.lineVariance (longParameters β s) unitIntervalL2 < ⊤) ∧
    (∀ (R : ℕ → ℝ) (N : ℕ → ℕ+), (∀ j, 0 < R j) → Tendsto R atTop atTop →
      Tendsto (fun j => R j / (N j : ℝ)) atTop (𝓝 0) →
      (∀ j, MemLp (finiteIntervalCount (N j) (R j)) 2 (gibbsMeasure (ofLong β s) (N j))) ∧
      ConvergesInLawAlong atTop
        (fun j => (gibbsMeasure (ofLong β s) (N j)).map
          (fun X => (R j) ^ (-s.val / 2) * (finiteIntervalCount (N j) (R j) X - R j)))
        (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) ∧
      (∀ j, Riesz1.variance (gibbsMeasure (ofLong β s) (N j))
        (finiteIntervalCount (N j) (R j)) (integrable_finiteIntervalCount β s (N j) (R j)) < ⊤) ∧
      Tendsto (fun j => (R j) ^ (-s.val) *
        (Riesz1.variance (gibbsMeasure (ofLong β s) (N j))
          (finiteIntervalCount (N j) (R j)) (integrable_finiteIntervalCount β s (N j) (R j))).toReal)
        atTop (𝓝 (Riesz1.countVariance (longParameters β s)))) :=
  ⟨unitInterval_fourier_integral s, unitInterval_lineVariance β s,
    fun R N hR hTop hRN => finiteIntervalCount_pairs_limit β s N R hR hTop hRN⟩

/-- See the proof of Corollary 1.1 in the paper: inside the strict quarter-circle cut,
the finite count of the paper is the configuration interval count. The bridge is pointwise,
so it also covers configurations having a particle at the included right endpoint. -/
theorem finiteIntervalCount_eq_intervalCount (N : ℕ+) (R : ℝ) (_hR : 0 < R)
    (hRN : R / (N : ℝ) < 1 / 4) (X : Riesz1.Configuration N) :
    finiteIntervalCount N R X = intervalCount 0 R (microscopicConfiguration 0 X) := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  let r : Fin (N : ℕ) → ℝ := fun i =>
    Riesz1.centralRep Riesz1.unitLength (X.val i : UnitAddCircle)
  let f : Fin (N : ℕ) → ℝ := fun i => (N : ℝ) * r i
  let S : Finset (Fin (N : ℕ)) := Finset.univ.filter (fun i => r i ∈ Set.Ioc (0 : ℝ) (R / (N : ℝ)))
  have hf : Function.Injective f := by
    intro i j hij
    have hr : r i = r j := mul_left_cancel₀ hN.ne' hij
    have hc : (X.val i : UnitAddCircle) = (X.val j : UnitAddCircle) := by
      rw [← FrozenSanity.centralRep_cast (X.val i : UnitAddCircle),
        ← FrozenSanity.centralRep_cast (X.val j : UnitAddCircle)]
      exact congrArg (fun z : ℝ => (z : UnitAddCircle)) hr
    by_contra hne
    apply Riesz1.coe_sub_ne_zero_of_mem_orderedDomain X.property hne
    rw [AddCircle.coe_sub, hc, sub_self]
  have hset : (microscopicConfiguration 0 X).val ∩ Set.Ioc (0 : ℝ) R =
      f '' (S : Set (Fin (N : ℕ))) := by
    ext x
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hx⟩
      refine ⟨i, ?_, by simp only [f, r, sub_zero]⟩
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      change 0 < r i ∧ r i ≤ R / (N : ℝ)
      have hx' : 0 < (N : ℝ) * r i ∧ (N : ℝ) * r i ≤ R := by
        simpa only [sub_zero, Set.mem_Ioc, r] using hx
      exact ⟨(mul_pos_iff_of_pos_left hN).mp hx'.1,
        (le_div_iff₀ hN).mpr (by nlinarith [hx'.2])⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : 0 < r i ∧ r i ≤ R / (N : ℝ) := by
        simpa only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioc] using hi
      constructor
      · refine ⟨i, ?_, ?_⟩
        · have hri : |r i| < 1 / 4 := by
            rw [abs_of_pos hi'.1]
            exact hi'.2.trans_lt hRN
          simpa only [r, sub_zero] using hri
        · simp only [f, r, sub_zero]
      · change 0 < (N : ℝ) * r i ∧ (N : ℝ) * r i ≤ R
        exact ⟨mul_pos hN hi'.1, by have := (le_div_iff₀ hN).mp hi'.2; nlinarith⟩
  unfold intervalCount count
  rw [hset, hf.encard_image, Set.encard_coe_eq_coe_finsetCard]
  have he : finiteIntervalCount N R X = (S.card : ℝ) := by
    simp only [finiteIntervalCount, Set.indicator_apply, S, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rfl
  rw [he]
  simp

end Riesz2

end
