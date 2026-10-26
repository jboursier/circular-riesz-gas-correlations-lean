/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PairGibbsMeasure
public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.Frozen.IntrinsicGapLaw
public import Riesz2.Frozen.FullIntrinsicTiltedGapLaw
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Riesz1.Gibbs.WellDefined
public import Riesz1.Rigidity.Gaps

/-! # Unconditional normalization of the actual tilted particle laws -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace Riesz2.DefinitionSanity

/-- Model validity gives normalization of the tilted law. -/
theorem particle_law_probability (p : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (gibbsMeasure p N) := by
  unfold gibbsMeasure
  split_ifs with hs
  · exact (Riesz1.modelWellDefined ⟨p.val, p.property.1, p.property.2.1, hs⟩ N).2.2
  · let s : ShortExponent := ⟨p.val.2,
      lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm p.property.2.2)⟩
    have hE : Measurable (@shortEnergy s N) := by
      unfold shortEnergy
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      apply Finset.measurable_sum
      intro j _
      change Measurable (fun X : Riesz1.Configuration N =>
        ∑' k : ℤ, 1 / |(k : ℝ) + (X.val i - X.val j.val)| ^ s.val)
      apply Measurable.tsum
      intro k
      have hcoord (i : Fin (N : ℕ)) : Measurable (fun X : Riesz1.Configuration N => X.val i) :=
        (measurable_pi_apply i).comp measurable_subtype_coe
      exact measurable_const.div
        ((measurable_const.add ((hcoord i).sub (hcoord j.val))).abs.pow_const s.val)
    have hm : Measurable (fun X : Riesz1.Configuration N =>
        ENNReal.ofReal (Real.exp (-p.val.1 * shortEnergy s X))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hE))
    have hZ : shortPartitionFunction ⟨p.val.1, p.property.1⟩ s N =
        ∫⁻ X : Riesz1.Configuration N,
          ENNReal.ofReal (Real.exp (-p.val.1 * shortEnergy s X)) ∂Riesz1.configurationVolume N := by
      simp [shortPartitionFunction, shortGibbsWeight, withDensity_apply]
    have hpos : 0 < shortPartitionFunction ⟨p.val.1, p.property.1⟩ s N := by
      rw [hZ, lintegral_pos_iff_support hm]
      have hsupport : Function.support (fun X : Riesz1.Configuration N =>
          ENNReal.ofReal (Real.exp (-p.val.1 * shortEnergy s X))) = univ := by
        ext X
        simp [Real.exp_pos]
      rw [hsupport, Riesz1.configurationVolume_univ]
      positivity
    have hfinite : shortPartitionFunction ⟨p.val.1, p.property.1⟩ s N < ⊤ := by
      rw [hZ]
      calc
        _ ≤ ∫⁻ _ : Riesz1.Configuration N, (1 : ℝ≥0∞) ∂Riesz1.configurationVolume N := by
          apply lintegral_mono
          intro X
          apply ENNReal.ofReal_le_one.mpr
          apply Real.exp_le_one_iff.mpr
          apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
          unfold shortEnergy shortKernelLift
          positivity
        _ < ⊤ := by simp [Riesz1.configurationVolume_univ]
    apply isProbabilityMeasure_iff.mpr
    change ((shortPartitionFunction ⟨p.val.1, p.property.1⟩ s N)⁻¹ •
      shortGibbsWeight ⟨p.val.1, p.property.1⟩ s N) univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpos.ne' hfinite.ne

theorem gap_positive {N : ℕ+} (X : Riesz1.Configuration N) (i : ℤ) : 0 < gap X i := by
  exact Riesz1.gap_pos X i

theorem gap_measurable {N : ℕ+} (i : ℤ) : Measurable (fun X : Riesz1.Configuration N => gap X i) := by
  exact Riesz1.measurable_gap i

theorem penalty_nonneg (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) (X : Riesz1.Configuration N) :
    0 ≤ physicalGapPenalty N n hn θ ε b X := by
  apply Finset.sum_nonneg
  intro i _
  apply add_nonneg
  · exact θ.property.2.2.1 _ (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gap_positive X i.val).le)
  · cases b
    · exact le_rfl
    · exact θ.property.2.2.1 _ (mul_nonneg (Real.rpow_nonneg (by positivity) _) (inv_nonneg.mpr (gap_positive X i.val).le))

theorem penalty_measurable (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    Measurable (physicalGapPenalty N n hn θ ε b) := by
  have hθ : Continuous (fun t : Ici (0 : ℝ) => θ.val t.val) :=
    continuousOn_iff_continuous_domRestrict.mp θ.property.1.continuousOn
  have hup (i : Fin (n : ℕ)) : Measurable (fun X : Riesz1.Configuration N =>
      θ.val ((n : ℝ) ^ (-ε) * gap X i.val)) := by
    let f : Riesz1.Configuration N → Ici (0 : ℝ) := fun X =>
      ⟨(n : ℝ) ^ (-ε) * gap X i.val,
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (gap_positive X i.val).le⟩
    have hf : Measurable f := (measurable_const.mul (gap_measurable _)).subtype_mk
    exact hθ.measurable.comp hf
  have hdown (i : Fin (n : ℕ)) : Measurable (fun X : Riesz1.Configuration N =>
      θ.val ((n : ℝ) ^ (-ε) * (gap X i.val)⁻¹)) := by
    let f : Riesz1.Configuration N → Ici (0 : ℝ) := fun X =>
      ⟨(n : ℝ) ^ (-ε) * (gap X i.val)⁻¹,
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (inv_nonneg.mpr (gap_positive X i.val).le)⟩
    have hf : Measurable f := (measurable_const.mul (gap_measurable _).inv).subtype_mk
    exact hθ.measurable.comp hf

  unfold physicalGapPenalty
  apply Finset.measurable_sum
  intro i _
  apply (hup i).add
  cases b
  · exact measurable_const
  · exact hdown i

theorem tilt_normalizer_valid (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    0 < tiltNormalizer p N n hn θ ε b ∧ tiltNormalizer p N n hn θ ε b ≤ 1 := by
  have : IsProbabilityMeasure (gibbsMeasure p N) := particle_law_probability p N
  have hm : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε b X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (penalty_measurable N n hn θ ε b)))
  constructor
  · rw [tiltNormalizer, lintegral_pos_iff_support hm]
    have hs : Function.support (fun X : Riesz1.Configuration N =>
        ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε b X))) = univ := by
      ext X
      simp [Function.mem_support, Real.exp_pos]
    rw [hs]
    simp
  · calc
      tiltNormalizer p N n hn θ ε b ≤ ∫⁻ _ : Riesz1.Configuration N, (1 : ℝ≥0∞) ∂gibbsMeasure p N := by
        apply lintegral_mono
        intro X
        apply ENNReal.ofReal_le_one.mpr
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
          (penalty_nonneg N n hn θ ε b X)
      _ = 1 := by simp

theorem tilted_probability (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε b) := by
  apply isProbabilityMeasure_iff.mpr
  rw [tiltedParticleMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (tiltNormalizer p N n hn θ ε b)⁻¹ * tiltNormalizer p N n hn θ ε b = 1
  exact ENNReal.inv_mul_cancel (tilt_normalizer_valid p N n hn θ ε b).1.ne'
    (ne_of_lt ((tilt_normalizer_valid p N n hn θ ε b).2.trans_lt (by simp)))

theorem active_projection_measurable (N n : ℕ+) :
    Measurable (fun X : Riesz1.Configuration N => WithLp.toLp 2 (finiteGapBlock (K := n) X)) := by
  apply (WithLp.measurable_toLp 2 _).comp
  exact Measurable.of_eval (fun i : Fin (n : ℕ) => gap_measurable i.val)

theorem active_tilted_probability (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    IsProbabilityMeasure (activeTiltedGapLaw p N n hn θ ε b) := by
  have : IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε b) :=
    tilted_probability p N n hn θ ε b
  unfold activeTiltedGapLaw
  infer_instance

theorem centered_chart_continuous (N : ℕ+) : Continuous (centeredGapChart N) := by
  unfold centeredGapChart
  fun_prop

theorem intrinsic_projection_measurable (N : ℕ+) :
    Measurable (fun X : Riesz1.Configuration N => centeredGapChart N (WithLp.toLp 2 (gapVector X))) := by
  apply (centered_chart_continuous N).measurable.comp
  apply (WithLp.measurable_toLp 2 _).comp
  exact Measurable.of_eval (fun i : Fin (N : ℕ) => gap_measurable i.val)

theorem intrinsic_gap_probability {N : ℕ+} (μ : Measure (Riesz1.Configuration N))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (intrinsicGapLaw μ) := by
  unfold intrinsicGapLaw
  infer_instance

theorem actual_gap_sum {N : ℕ+} (X : Riesz1.Configuration N) :
    ∑ i : Fin (N : ℕ), gap X i.val = (N : ℝ) := by
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => gap X (j : ℤ)) (N : ℕ)).trans
    (Riesz1.sum_gap_eq X)

theorem full_chart_embedding (N : ℕ+) :
    MeasurableEmbedding (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)) := by
  have hc : Continuous (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)) := by
    fun_prop
  apply hc.measurableEmbedding
  intro a b hab
  apply Subtype.ext
  ext i
  have hi := congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i) hab
  change (1 : ℝ) + a.val i = 1 + b.val i at hi
  linarith

theorem actual_gap_in_chart {N : ℕ+} (X : Riesz1.Configuration N) :
    WithLp.toLp 2 (gapVector X) ∈ range
      (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)) := by
  refine ⟨centeredGapChart N (WithLp.toLp 2 (gapVector X)), ?_⟩
  ext i
  change (1 : ℝ) + (gap X i.val - (∑ j : Fin (N : ℕ), gap X j.val) / (N : ℝ)) = gap X i.val
  rw [actual_gap_sum]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt N.pos)
  rw [div_self hN]
  ring

theorem full_intrinsic_tilted_probability (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (ε : ℝ) (b : Bool) : IsProbabilityMeasure (fullIntrinsicTiltedGapLaw p N θ ε b) := by
  have : IsProbabilityMeasure (activeTiltedGapLaw p N N (le_refl _) θ ε b) :=
    active_tilted_probability p N N (le_refl _) θ ε b
  apply (full_chart_embedding N).isProbabilityMeasure_comap
  rw [activeTiltedGapLaw]
  apply (ae_map_iff (active_projection_measurable N N).aemeasurable
    (full_chart_embedding N).measurableSet_range).mpr
  exact Filter.Eventually.of_forall (fun X => actual_gap_in_chart X)

/-- Every point of the general Gibbs law's actual carrier normalizes, without a fallback value. -/
theorem pair_gibbs_probability {N : ℕ+} (χ : ParticlePairData N)
    (hm : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
    (hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤) :
    IsProbabilityMeasure (pairGibbsMeasure χ hm hZ) := by
  apply isProbabilityMeasure_iff.mpr
  rw [pairGibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (pairGibbsNormalizer χ)⁻¹ * pairGibbsNormalizer χ = 1
  exact ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne

/-- The general pair-law carrier has an actual two-particle uniform example. -/
theorem pair_zero_normalizer :
    pairGibbsNormalizer (N := 2) (fun _ _ => 0) = 1 := by
  norm_num [pairGibbsNormalizer, particlePairEnergy, Riesz1.configurationVolume_univ]

theorem pair_gibbs_carrier_nonempty :
    ∃ (χ : ParticlePairData 2)
      (hm : Measurable (fun X : Riesz1.Configuration 2 =>
        ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
      (hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤),
      IsProbabilityMeasure (pairGibbsMeasure χ hm hZ) := by
  have hm : Measurable (fun X : Riesz1.Configuration 2 =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy (fun _ _ => 0) (WithLp.toLp 2 X.val)))) := by
    simp only [particlePairEnergy, Finset.sum_const_zero, mul_zero, neg_zero, Real.exp_zero]
    exact measurable_const
  have hZ : 0 < pairGibbsNormalizer (N := 2) (fun _ _ => 0) ∧
      pairGibbsNormalizer (N := 2) (fun _ _ => 0) < ⊤ := by rw [pair_zero_normalizer]; simp
  exact ⟨fun _ _ => 0, hm, hZ, pair_gibbs_probability _ hm hZ⟩

end Riesz2.DefinitionSanity
end
end
