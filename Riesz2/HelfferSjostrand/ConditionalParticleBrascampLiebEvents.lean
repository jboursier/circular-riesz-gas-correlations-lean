/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalParticleBrascampLiebLift
public import Riesz1.HelfferSjostrand.SobolevLifts
public import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning in the cyclic lift

For Lemma 3.4, the convex strict cyclic lift of a particle event
can be replaced by its interior without changing the conditional law.
Convexity itself gives a null boundary, so the argument also covers the
piecewise smooth boundary convention in the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff ENNReal

namespace Riesz2.ConditionalParticleBrascampLieb

open AffineMetric Riesz1.WeightedSobolev

variable {N : ℕ+}

/-- The strict cyclic lift `0 < x₁ < 1` of the event in
Lemma 3.4. The upper cut is already part of the representative. -/
def openCyclicLift (N : ℕ+) (A : Set (Riesz1.Configuration N)) :
    Set (EuclideanSpace ℝ (Fin (N : ℕ))) :=
  configurationLift N '' A ∩ {x | 0 < x ⟨0, N.pos⟩}

/-- Every fundamental representative is collision-free, as used in
Lemma 3.4. -/
theorem configurationLift_mem_chamber (X : Riesz1.Configuration N) :
    configurationLift N X ∈ particleChamber N :=
  ⟨X.property.1, X.property.2.2.2⟩

/-- The interior of the strict lift in Lemma 3.4 stays in the
fundamental region and the collision-free particle chamber. -/
theorem interior_openCyclicLift_subset (A : Set (Riesz1.Configuration N)) :
    interior (openCyclicLift N A) ⊆ Riesz1.hsFundamentalRegion N := by
  intro x hx
  rw [← range_configurationLift]
  exact image_subset_range _ _ (interior_subset hx).1

/-- The bounded-lift assertion needed for the regularization in
Lemma 3.4. -/
theorem interior_openCyclicLift_bounded (A : Set (Riesz1.Configuration N)) :
    Bornology.IsBounded (interior (openCyclicLift N A)) :=
  (Riesz1.isCompact_closure_hsFundamentalRegion N).isBounded.subset
    ((interior_openCyclicLift_subset A).trans subset_closure)

/-- Absolute continuity of the actual Gibbs lift in Lemma 3.4,
needed to remove the artificial cut and the convex event boundary. -/
theorem pairGibbs_lift_absolutelyContinuous
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c) :
    (pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1).map (configurationLift N) ≪ volume := by
  rw [map_pairGibbsMeasure_lift hN hc hχ]
  exact ((withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)).smul_left _

namespace Internal

/-- The artificial rotation-cut face in Lemma 3.4 has zero
Euclidean volume. -/
theorem ae_rotation_cut_ne (N : ℕ+) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin (N : ℕ)) ∂volume, x ⟨0, N.pos⟩ ≠ 0 := by
  have hpi : ∀ᵐ y : Fin (N : ℕ) → ℝ ∂volume, y ⟨0, N.pos⟩ ≠ 0 :=
    MeasureTheory.Measure.ae_eval_ne (fun _ : Fin (N : ℕ) => (volume : Measure ℝ)) ⟨0, N.pos⟩ 0
  exact (PiLp.volume_preserving_ofLp (Fin (N : ℕ))).quasiMeasurePreserving.ae hpi

/-- Boundary removal in Lemma 3.4, for arbitrary absolutely
continuous lift laws. This does not assume the event is a gap event. -/
theorem interior_openCyclicLift_ae {μ : Measure (Riesz1.Configuration N)}
    (hμ : μ.map (configurationLift N) ≪ volume)
    {A : Set (Riesz1.Configuration N)} (hA : Convex ℝ (openCyclicLift N A)) :
    interior (openCyclicLift N A) =ᵐ[μ.map (configurationLift N)]
      configurationLift N '' A := by
  have hi : interior (openCyclicLift N A) =ᵐ[μ.map (configurationLift N)]
      openCyclicLift N A := hμ.ae_le
    (interior_ae_eq_of_null_frontier (hA.addHaar_frontier volume))
  apply hi.trans
  filter_upwards [hμ.ae_le (ae_rotation_cut_ne N)] with x hx
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    obtain ⟨X, hX, rfl⟩ := h
    exact ⟨⟨X, hX, rfl⟩, lt_of_le_of_ne X.property.2.1 (Ne.symm hx)⟩

/-- Restriction commutes with the fundamental lift in Lemma 3.4,
after removing the null boundary of its convex event. -/
theorem map_conditional_lift {μ : Measure (Riesz1.Configuration N)}
    (hμ : μ.map (configurationLift N) ≪ volume)
    {A : Set (Riesz1.Configuration N)} (hA : Convex ℝ (openCyclicLift N A)) :
    (((μ A)⁻¹ • μ.restrict A).map (configurationLift N)) =
      (μ A)⁻¹ • (μ.map (configurationLift N)).restrict
        (interior (openCyclicLift N A)) := by
  rw [Measure.map_smul _ (configurationLift_measurableEmbedding N).measurable.aemeasurable,
    Measure.restrict_congr_set (interior_openCyclicLift_ae hμ hA),
    (configurationLift_measurableEmbedding N).restrict_map,
    preimage_image_eq _ (configurationLift_measurableEmbedding N).injective]

/-- The original conditional configuration law in Lemma 3.4,
transported to the interior of its convex strict lift, has exactly the
normalized original Euclidean density. Positive finite normalization is
proved from the actual Gibbs law, rather than assumed. -/
theorem conditional_lift_density
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c)
    (A : Set (Riesz1.Configuration N)) (hA : Convex ℝ (openCyclicLift N A))
    (hmass : (pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1) A ≠ 0) :
    let μ := pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1
    let Ω := interior (openCyclicLift N A)
    let ρ := (((μ A)⁻¹ • μ.restrict A).map (configurationLift N))
    IsProbabilityMeasure ρ ∧ Ω.Nonempty ∧
      ρ = (volume.restrict Ω).withDensity (fun x =>
        ENNReal.ofReal (Real.exp (-particlePairEnergy χ x) /
          ∫ y in Ω, Real.exp (-particlePairEnergy χ y))) := by
  dsimp only
  let μ := pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
    (particle_hessian_normalization hN c hc χ hχ).1
  let Ω := interior (openCyclicLift N A)
  let ρ := (((μ A)⁻¹ • μ.restrict A).map (configurationLift N))
  let a := (μ A)⁻¹ * (pairGibbsNormalizer χ)⁻¹
  have hμp : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [pairGibbsMeasure_eq_library hc hχ]
    infer_instance
  have hcond : IsProbabilityMeasure ((μ A)⁻¹ • μ.restrict A) :=
    ProbabilityTheory.cond_isProbabilityMeasure hmass
  have hρp : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have ha0 : a ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top μ A))
    (ENNReal.inv_ne_zero.mpr (particle_hessian_normalization hN c hc χ hχ).1.2.ne)
  have hat : a ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hmass)
    (ENNReal.inv_ne_top.mpr (particle_hessian_normalization hN c hc χ hχ).1.1.ne')
  have he : ρ = a • (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-particlePairEnergy χ x))) := by
    dsimp only [ρ]
    rw [map_conditional_lift (pairGibbs_lift_absolutelyContinuous hN hc hχ) hA]
    rw [map_pairGibbsMeasure_lift hN hc hχ, Measure.restrict_smul,
      restrict_withDensity isOpen_interior.measurableSet,
      Measure.restrict_restrict isOpen_interior.measurableSet,
      inter_eq_left.mpr (interior_openCyclicLift_subset A), smul_smul]
  have hΩne : Ω.Nonempty := by
    by_contra hn
    have hz : ρ = 0 := by simp [he, not_nonempty_iff_eq_empty.mp hn]
    have hu := measure_univ (μ := ρ)
    simp [hz] at hu
  have hH := Riesz1.hsPairExpression_contDiffOn (libraryPairs hχ)
  rw [libraryPairs_energy] at hH
  obtain ⟨B, hB⟩ := Riesz1.hsFundamentalHamiltonian_bounded_below (libraryPairs hχ) hc
  have hi : Integrable (fun x => Real.exp (-particlePairEnergy χ x)) (volume.restrict Ω) := by
    refine Integrable.mono'
      (integrableOn_const (C := Real.exp (-B))
        (interior_openCyclicLift_bounded A).measure_lt_top.ne)
      (Real.continuous_exp.comp_continuousOn
        (hH.continuousOn.mono (fun x hx => (interior_openCyclicLift_subset A hx).1)).neg
        |>.aestronglyMeasurable isOpen_interior.measurableSet) ?_
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with x hx
    obtain ⟨X, rfl⟩ := (range_configurationLift N).symm ▸
      (interior_openCyclicLift_subset A hx)
    have hb := hB X
    change B ≤ Riesz1.hsPairExpression (libraryPairs hχ) (configurationLift N X) at hb
    rw [libraryPairs_energy] at hb
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (neg_le_neg hb)
  have : NeZero (volume.restrict Ω) :=
    ⟨fun hz => (isOpen_interior.measure_pos volume hΩne).ne' (Measure.restrict_eq_zero.mp hz)⟩
  have hn : 0 < ∫ x in Ω, Real.exp (-particlePairEnergy χ x) := integral_exp_pos hi
  refine ⟨hρp, hΩne, ?_⟩
  change ρ = _
  apply Riesz1.Gaussian.eq_normalized_density_of_probability hi (fun _ => (Real.exp_pos _).le)
    hn (ENNReal.toReal_pos ha0 hat)
  rw [he, ← withDensity_smul' a _ hat]
  congr 1
  funext x
  rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hat]
  rfl

end Internal

end Riesz2.ConditionalParticleBrascampLieb
