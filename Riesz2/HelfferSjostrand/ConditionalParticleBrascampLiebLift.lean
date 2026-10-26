/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalParticleBrascampLiebPart4
public import Mathlib.Analysis.Convex.Measure

/-!
# The configuration law in the open cyclic lift

The adapter for Lemma 3.4 uses the actual fundamental representative
of each configuration. It preserves particle events as well as the gap image.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff ENNReal

namespace Riesz2.ConditionalParticleBrascampLieb

open AffineMetric Riesz1.WeightedSobolev

variable {N : ℕ+}

/-- The cyclic fundamental representative used by Lemma 3.4. -/
def configurationLift (N : ℕ+) (X : Riesz1.Configuration N) :
    EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 X.val

/-- The fundamental representative in Lemma 3.4 is a measurable
embedding, so arbitrary particle events can be transported. -/
theorem configurationLift_measurableEmbedding (N : ℕ+) :
    MeasurableEmbedding (configurationLift N) :=
  (PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)).symm.measurableEmbedding.comp
    (MeasurableEmbedding.subtype_coe (Riesz1.measurableSet_orderedDomain N))

/-- The image of the representative in Lemma 3.4 is the half-open
fundamental region, including its artificial rotation-cut face. -/
theorem range_configurationLift (N : ℕ+) :
    Set.range (configurationLift N) = Riesz1.hsFundamentalRegion N := by
  rw [Riesz1.hsFundamentalRegion_eq_preimage]
  ext x
  constructor
  · rintro ⟨X, rfl⟩
    exact X.property
  · intro hx
    exact ⟨⟨WithLp.ofLp x, hx⟩, rfl⟩

/-- Fundamental-region volume transport for Lemma 3.4, directly
from the proved library integration identity. -/
theorem map_configurationVolume_lift (N : ℕ+) :
    (Riesz1.configurationVolume N).map (configurationLift N) =
      volume.restrict (Riesz1.hsFundamentalRegion N) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (configurationLift_measurableEmbedding N).measurable]
  simpa only [configurationLift, WithLp.toLp_ofLp] using (Riesz1.hsFundamentalRegion_lintegral N
    (fun y => f (WithLp.toLp 2 y))
    (hf.comp (PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable)).symm

/-- The lift has exactly the gap image in Lemma 3.4. -/
theorem liftedGapMap_configurationLift (X : Riesz1.Configuration N) :
    liftedGapMap N (configurationLift N X) =
      centeredGapChart N (WithLp.toLp 2 (gapVector X)) := by
  unfold liftedGapMap configurationLift
  rw [Riesz1.hsGap_eq_gapVector]
  rfl

/-- Compatibility with the `intrinsicGapLaw` in Lemma 3.4,
for every configuration law, before or after conditioning. -/
theorem map_lift_gap (μ : Measure (Riesz1.Configuration N)) :
    (μ.map (configurationLift N)).map (liftedGapMap N) = intrinsicGapLaw μ := by
  have hm : Measurable (liftedGapMap N) := by
    have he : liftedGapMap N = fun x => gapDerivative N x + gapOffset N :=
      funext (liftedGapMap_eq N)
    rw [he]
    exact ((gapDerivative N).continuous.add_const _).measurable
  rw [Measure.map_map hm (configurationLift_measurableEmbedding N).measurable]
  congr 1

namespace Internal

/-- Density transport along the representative in Lemma 3.4. Only measurability on the actual target measure is required. -/
theorem map_lift_withDensity {μ : Measure (Riesz1.Configuration N)}
    {w : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ≥0∞}
    (hw : AEMeasurable w (μ.map (configurationLift N))) :
    (μ.withDensity (fun X => w (configurationLift N X))).map (configurationLift N) =
      (μ.map (configurationLift N)).withDensity w := by
  have hL := (configurationLift_measurableEmbedding N).measurable
  calc
    _ = (μ.withDensity (fun X => hw.mk w (configurationLift N X))).map
        (configurationLift N) := by
      congr 1
      exact withDensity_congr_ae ((configurationLift_measurableEmbedding N).ae_map_iff.mp hw.ae_eq_mk)
    _ = (μ.map (configurationLift N)).withDensity (hw.mk w) :=
      Riesz1.map_withDensity_comp μ hL hw.measurable_mk
    _ = _ := withDensity_congr_ae hw.ae_eq_mk.symm

end Internal

/-- The pair Gibbs law has its original normalized density on
the cyclic fundamental lift in Lemma 3.4. -/
theorem map_pairGibbsMeasure_lift
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c) :
    (pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1).map (configurationLift N) =
      (pairGibbsNormalizer χ)⁻¹ •
        (volume.restrict (Riesz1.hsFundamentalRegion N)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-particlePairEnergy χ x))) := by
  let w := fun x => ENNReal.ofReal (Real.exp (-particlePairEnergy χ x))
  have hw : AEMeasurable w (volume.restrict (Riesz1.hsFundamentalRegion N)) := by
    have hH := Riesz1.hsPairExpression_contDiffOn (libraryPairs hχ)
    rw [libraryPairs_energy] at hH
    have hh : AEMeasurable (fun x => Real.exp (-particlePairEnergy χ x))
        (volume.restrict (particleChamber N)) :=
      (Real.continuous_exp.comp_continuousOn hH.continuousOn.neg).aemeasurable
        (Riesz1.isOpen_hsChamber N).measurableSet
    have hs : Riesz1.hsFundamentalRegion N ⊆ particleChamber N := fun x hx => hx.1
    exact (hh.ennreal_ofReal).mono_measure (Measure.restrict_mono hs le_rfl)
  change ((pairGibbsNormalizer χ)⁻¹ •
    (Riesz1.configurationVolume N).withDensity (fun X => w (configurationLift N X))).map _ = _
  rw [Measure.map_smul _ (configurationLift_measurableEmbedding N).measurable.aemeasurable,
    Internal.map_lift_withDensity (by rwa [map_configurationVolume_lift]), map_configurationVolume_lift]

end Riesz2.ConditionalParticleBrascampLieb
