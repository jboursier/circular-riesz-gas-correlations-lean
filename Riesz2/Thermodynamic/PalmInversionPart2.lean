/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.PalmInversion
public import Riesz2.Thermodynamic.GapLimit
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Palm inversion and finite rotation compatibility

Reflection and positive dilation identify uniform averaging on the unit interval with
normalized averaging over a positive period, including reversed orientation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
open scoped ENNReal

namespace Riesz2

local instance : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- Reflection about the midpoint preserves the uniform unit-interval measure. -/
theorem map_unitInterval_reflection :
    (volume.restrict (Ico (0 : ℝ) 1)).map (fun t : ℝ => 1 - t) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have h := ((volume : Measure ℝ).measurePreserving_sub_left 1).restrict_preimage
    (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
  have he : (fun t : ℝ => 1 - t) ⁻¹' Ioc (0 : ℝ) 1 = Ico 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  rw [he] at h
  exact h.map_eq.trans (restrict_Ico_eq_restrict_Ioc (μ := (volume : Measure ℝ))).symm

/-- Positive dilation sends the uniform unit interval to normalized Lebesgue
measure on the interval of length `L`. -/
theorem map_unitInterval_dilation (L : ℝ) (hL : 0 < L) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (fun t : ℝ => L * t) =
      (ENNReal.ofReal L)⁻¹ • volume.restrict (Ico (0 : ℝ) L) := by
  have he : (fun t : ℝ => L * t) ⁻¹' Ico (0 : ℝ) L = Ico 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ico]
    constructor
    · intro ht
      exact ⟨(mul_nonneg_iff_of_pos_left hL).mp ht.1,
        (mul_lt_iff_lt_one_right hL).mp ht.2⟩
    · intro ht
      exact ⟨mul_nonneg hL.le ht.1, (mul_lt_iff_lt_one_right hL).mpr ht.2⟩
  have h := Measure.restrict_map (μ := (volume : Measure ℝ))
    (measurable_const_mul L) (s := Ico (0 : ℝ) L) measurableSet_Ico
  rw [he, Real.map_volume_mul_left hL.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hL), ENNReal.ofReal_inv_of_pos hL] at h
  exact h.symm

/-- Averaging a measurable periodic nonnegative function along the negatively
oriented unit interval is normalized averaging over one positive period. -/
theorem lintegral_periodic_negative_unitInterval (L : ℝ) (hL : 0 < L)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (hperiod : Function.Periodic f L) :
    (∫⁻ t in Ico (0 : ℝ) 1, f (-L * t)) =
      (ENNReal.ofReal L)⁻¹ * ∫⁻ u in Ico (0 : ℝ) L, f u := by
  have hg : Measurable (fun t : ℝ => f (L * t)) :=
    hf.comp (measurable_const.mul measurable_id)
  calc
    _ = ∫⁻ t in Ico (0 : ℝ) 1, f (L * (1 - t)) := by
      apply lintegral_congr
      intro t
      rw [show L * (1 - t) = -L * t + L by ring, hperiod]
    _ = ∫⁻ t in Ico (0 : ℝ) 1, f (L * t) := by
      rw [← lintegral_map hg (measurable_const_sub 1), map_unitInterval_reflection]
    _ = _ := by
      rw [← lintegral_map hf (measurable_const_mul L),
        map_unitInterval_dilation L hL, lintegral_smul_measure, smul_eq_mul]

/-- The finite gap lift is precisely the reconstruction-domain pullback of the
periodic gap law (Subsection 6.3, Subsection 6.3). -/
theorem reconstructionGapMeasure_periodicGapLaw (p : Parameters) (N : ℕ+) :
    reconstructionGapMeasure (periodicGapLaw p N).toMeasure =
      (gibbsMeasure p N).map configurationReconstructionGaps := by
  have hs : ∀ᵐ y ∂(periodicGapLaw p N).toMeasure, y ∈ reconstructibleGapSequences := by
    rw [periodicGapLaw_toMeasure]
    exact (ae_map_iff (measurable_periodicGapSequence N).aemeasurable
      measurableSet_reconstructibleGapSequences).mpr
        (ae_of_all _ fun X => finite_configuration_mem_reconstructibleGapSequences X)
  apply (MeasurableEmbedding.subtype_coe measurableSet_reconstructibleGapSequences).map_injective
  rw [map_reconstructionGapMeasure _ hs,
    Measure.map_map measurable_subtype_coe (measurable_configurationReconstructionGaps N)]
  rfl

/-- Finite gap laws are invariant under every integer shift even at the
one-particle boundary (the proof of Theorem 3). -/
theorem periodicGapLaw_shift_all (p : Parameters) (N : ℕ+) (a : ℤ) :
    (periodicGapLaw p N).map (gapIndexShift a) = periodicGapLaw p N := by
  by_cases hN : 2 ≤ (N : ℕ)
  · exact periodicGapLaw_shift p N hN a
  · have hN1 : N = 1 := PNat.eq (by simpa using (show (N : ℕ) = 1 by have := N.pos; omega))
    subst N
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, periodicGapLaw_toMeasure,
      Measure.map_map (gapIndexShift a).continuous.measurable (measurable_periodicGapSequence 1)]
    congr 1
    funext X j
    apply Subtype.ext
    change (periodicGapSequence X (a + j) : ℝ) = (periodicGapSequence X j : ℝ)
    exact (periodicGapSequence_one X (a + j)).trans (periodicGapSequence_one X j).symm

/-- The actual finite law on the reconstruction carrier is integer-shift
invariant (the proof of Theorem 3). -/
theorem configurationReconstructionGaps_law_shift (p : Parameters) (N : ℕ+) (a : ℤ) :
    ((gibbsMeasure p N).map configurationReconstructionGaps).map
      (reindexReconstructibleGaps a) = (gibbsMeasure p N).map configurationReconstructionGaps := by
  have hs : ∀ᵐ y ∂(periodicGapLaw p N).toMeasure, y ∈ reconstructibleGapSequences := by
    rw [periodicGapLaw_toMeasure]
    exact (ae_map_iff (measurable_periodicGapSequence N).aemeasurable
      measurableSet_reconstructibleGapSequences).mpr
        (ae_of_all _ fun X => finite_configuration_mem_reconstructibleGapSequences X)
  rw [← reconstructionGapMeasure_periodicGapLaw]
  apply reconstructionGapMeasure_shift _ hs a
  have h := congrArg ProbabilityMeasure.toMeasure (periodicGapLaw_shift_all p N a)
  rw [ProbabilityMeasure.toMeasure_map] at h
  change (periodicGapLaw p N).toMeasure.map (fun y j => y (a + j)) = _ at h
  simpa only [add_comm] using h

/-- The inverse finite chart has the same labelled gaps as the original
configuration (Subsection 1.7, Subsection 6.3), for every positive volume. -/
theorem configurationReconstructionGaps_chart (n : ℕ)
    (X : Riesz1.Configuration n.succPNat) :
    configurationReconstructionGaps (GapChart.reconstruct n (GapChart.gaps n X)) =
      configurationReconstructionGaps X := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  change Riesz1.gap _ j = Riesz1.gap X j
  rw [Riesz1.gap_eq_anchoredGapAt, Riesz1.gap_eq_anchoredGapAt,
    GapChart.anchorCoords_reconstruct, GapChart.anchored_gaps]

/-- Finite reconstruction is invariant under spatial translation by one
microscopic period (the proof of Theorem 3). -/
theorem reconstructConfiguration_finite_period {N : ℕ+} (X : Riesz1.Configuration N) :
    translateConfiguration (N : ℝ) (reconstructConfiguration (configurationReconstructionGaps X)) =
      reconstructConfiguration (configurationReconstructionGaps X) := by
  have hr : reindexReconstructibleGaps (N : ℤ) (configurationReconstructionGaps X) =
      configurationReconstructionGaps X := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact Riesz1.gap_add_N X j
  have h := reconstructConfiguration_reindex (configurationReconstructionGaps X) (N : ℤ)
  rw [hr, gapPosition_configurationReconstructionGaps_period] at h
  exact h.symm

/-- Independent uniform rotation in the actual finite chart gives the spatial
law by averaging the rooted reconstruction (the proof of Theorem 3). -/
theorem lintegral_periodicSpatialLaw_rotation (p : Parameters) (N : ℕ+)
    (f : LineConfiguration → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ C, f C ∂periodicSpatialLaw p N) =
      ∫⁻ X, ∫⁻ t in Ico (0 : ℝ) 1,
        f (translateConfiguration (-(N : ℝ) * t)
          (reconstructConfiguration (configurationReconstructionGaps X))) ∂volume ∂gibbsMeasure p N := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  let μ := gibbsMeasure p n.succPNat
  have := gibbsMeasure_probability p n.succPNat
  let H : ℝ × GapChart.Domain n → ℝ≥0∞ := fun z =>
    f (translateConfiguration (-(n.succPNat : ℝ) * z.1)
      (reconstructConfiguration (configurationReconstructionGaps (GapChart.reconstruct n z.2))))
  have hH : Measurable H := hf.comp (measurable_translateConfiguration.comp
    ((measurable_const.mul measurable_fst).prodMk
      (measurable_reconstructConfiguration.comp
        ((measurable_configurationReconstructionGaps _).comp
          ((GapChart.measurable_reconstruct n).comp measurable_snd)))))
  have hJ : Measurable (fun X : Riesz1.Configuration n.succPNat =>
      (X.val 0, GapChart.gaps n X)) :=
    ((measurable_pi_apply 0).comp measurable_subtype_coe).prodMk (GapChart.measurable_gaps n)
  have hcoords : μ.map (fun X => (X.val 0, GapChart.gaps n X)) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (μ.map (GapChart.gaps n)) := by
    dsimp only [μ]
    rw [GapChart.map_gibbsMeasure_coordinates_density, GapChart.map_gibbsMeasure_gaps_density]
  calc
    _ = ∫⁻ X, H (X.val 0, GapChart.gaps n X) ∂μ := by
      rw [periodicSpatialLaw, lintegral_map hf (measurable_periodicSpatialConfiguration _)]
      apply lintegral_congr
      intro X
      dsimp only [H, periodicSpatialConfiguration]
      rw [configurationReconstructionGaps_chart]
      congr 2
      exact congrArg (fun t : ℝ => -(n.succPNat : ℝ) * t)
        (Riesz1.cyclicLift_natCast X 0)
    _ = ∫⁻ z, H z ∂μ.map (fun X => (X.val 0, GapChart.gaps n X)) :=
      (lintegral_map hH hJ).symm
    _ = ∫⁻ y, ∫⁻ t in Ico (0 : ℝ) 1, H (t, y) ∂volume ∂μ.map (GapChart.gaps n) := by
      rw [hcoords, lintegral_prod_symm _ hH.aemeasurable]
    _ = ∫⁻ X, ∫⁻ t in Ico (0 : ℝ) 1, H (t, GapChart.gaps n X) ∂volume ∂μ :=
      lintegral_map hH.lintegral_prod_left' (GapChart.measurable_gaps n)
    _ = _ := by
      apply lintegral_congr
      intro X
      apply lintegral_congr
      intro t
      dsimp only [H]
      rw [configurationReconstructionGaps_chart]

/-- Uniform rotation of the finite labelled gaps is the actual periodic spatial
law, in both exponent regimes and at `N = 1`
(the proof of Theorem 3). -/
theorem uniformPeriodRotationMeasure_finite (p : Parameters) (N : ℕ+) :
    uniformPeriodRotationMeasure
      ((gibbsMeasure p N).map configurationReconstructionGaps) N = periodicSpatialLaw p N := by
  have := gibbsMeasure_probability p N
  let q := (gibbsMeasure p N).map configurationReconstructionGaps
  have hq : Measurable (fun X : Riesz1.Configuration N => configurationReconstructionGaps X) :=
    measurable_configurationReconstructionGaps N
  apply Measure.ext
  intro A hA
  let f : LineConfiguration → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hint : (∫⁻ C, f C ∂uniformPeriodRotationMeasure q N) =
      ∫⁻ C, f C ∂periodicSpatialLaw p N := by
    rw [lintegral_periodicSpatialLaw_rotation p N f hf]
    rw [uniformPeriodRotationMeasure, lintegral_smul_measure,
      lintegral_map hf measurable_gapSuspensionConfiguration, smul_eq_mul]
    change (N : ℝ≥0∞)⁻¹ *
      (∫⁻ z, (f ∘ gapSuspensionConfiguration) z
        ∂q.prod (volume.restrict (Ico (0 : ℝ) (N : ℝ)))) = _
    rw [lintegral_prod _ (hf.comp measurable_gapSuspensionConfiguration).aemeasurable]
    change (N : ℝ≥0∞)⁻¹ *
      (∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (N : ℝ),
        f (translateConfiguration u (reconstructConfiguration y)) ∂volume
        ∂(gibbsMeasure p N).map configurationReconstructionGaps) = _
    rw [lintegral_map (measurable_suspension_fixed_interval f hf 0 (N : ℝ)) hq]
    have hN : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast N.ne_zero
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hN)]
    apply lintegral_congr
    intro X
    have hp : Function.Periodic (fun u : ℝ =>
        f (translateConfiguration u (reconstructConfiguration (configurationReconstructionGaps X))))
        (N : ℝ) := by
      intro u
      change f (translateConfiguration (u + (N : ℝ))
        (reconstructConfiguration (configurationReconstructionGaps X))) = _
      rw [← translateConfiguration_add, reconstructConfiguration_finite_period]
    have hm : Measurable (fun u : ℝ =>
        f (translateConfiguration u (reconstructConfiguration (configurationReconstructionGaps X)))) :=
      hf.comp (measurable_translateConfiguration.comp (measurable_id.prodMk measurable_const))
    simpa only [ENNReal.ofReal_natCast] using
      (lintegral_periodic_negative_unitInterval (N : ℝ) (by exact_mod_cast N.pos)
        (fun u : ℝ => f (translateConfiguration u
          (reconstructConfiguration (configurationReconstructionGaps X)))) hm hp).symm
  calc
    _ = ∫⁻ C, f C ∂uniformPeriodRotationMeasure q N := (lintegral_indicator_one hA).symm
    _ = ∫⁻ C, f C ∂periodicSpatialLaw p N := hint
    _ = _ := lintegral_indicator_one hA

/-- See the proof of Theorem 3 in the paper, finite rotation compatibility:
the suspension of the actual labelled Gibbs gaps is the periodic spatial law,
for both exponent regimes and every positive volume, including one. -/
theorem gapSuspensionMeasure_finite (p : Parameters) (N : ℕ+) :
    gapSuspensionMeasure ((gibbsMeasure p N).map configurationReconstructionGaps) =
      periodicSpatialLaw p N := by
  have := gibbsMeasure_probability p N
  rw [← uniformPeriodRotationMeasure_eq_suspension_internal _
    (configurationReconstructionGaps_law_shift p N) N, uniformPeriodRotationMeasure_finite]
  exact (ae_map_iff (measurable_configurationReconstructionGaps N).aemeasurable
    (measurableSet_eq_fun
      ((measurable_gapPosition (N : ℕ)).comp measurable_subtype_coe) measurable_const)).mpr
    (ae_of_all _ fun X => gapPosition_configurationReconstructionGaps_period X)

/-- The Palm inversion step in the proof of Theorem 3, assuming the
ordinary-gap Cauchy estimate. The unique weak gap limit has a suspension
probability that is stationary of intensity one. Its Campbell Palm measure
is rooted reconstruction, and its Palm gaps have the original law.
For every positive finite volume the same inversion gives the periodic
spatial Gibbs law. -/
theorem convergence_palm_inversion_from_cauchy_internal
    (hcomparison :
  ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
      ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
        MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
        Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
          (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
          (gibbsMeasure p N') ∧
        |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
          (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
          C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (p : Parameters) :
    ∃! q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)),
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) ∧
      ∃ P : PointProcess,
        (P : Measure LineConfiguration) =
          gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure) ∧
        IsStationary P ∧ HasIntensity P 1 ∧
        palmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructConfiguration ∧
        rootedPalmMeasure P =
          (reconstructionGapMeasure q.toMeasure).map reconstructRootedConfiguration ∧
        (rootedPalmMeasure P).map rootedGap =
          q.toMeasure.map (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)) ∧
        ∀ N : ℕ+,
          gapSuspensionMeasure (reconstructionGapMeasure (periodicGapLaw p N).toMeasure) =
            periodicSpatialLaw p N := by
  obtain ⟨q, hq, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  have hs (a : ℤ) : q.toMeasure.map (fun y j => y (j + a)) = q.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure (hq.2.1 a)
    rw [ProbabilityMeasure.toMeasure_map] at h
    change q.toMeasure.map (fun y j => y (a + j)) = _ at h
    simpa only [add_comm] using h
  have hd : ∀ᵐ y ∂q.toMeasure,
      Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (0 + (j : ℤ)) : ℝ)) atTop atTop ∧
      Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (-(k : ℤ) + (j : ℤ)) : ℝ)) atTop atTop := by
    simpa only [gapSequenceSpan] using hq.2.2.2.2.2.2
  obtain ⟨P, hP, hstat, hint, hpalm, hroot, hgap⟩ :=
    palm_inversion_from_gap_limit_internal q hs hq.2.2.1 hd
  refine ⟨q, ⟨hq.1, P, hP, hstat, hint, hpalm, hroot, hgap, ?_⟩, ?_⟩
  · intro N
    rw [reconstructionGapMeasure_periodicGapLaw, gapSuspensionMeasure_finite]
  · intro q' hq'
    exact tendsto_nhds_unique hq'.1 hq.1

end Riesz2
