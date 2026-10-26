/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalParticleBrascampLiebEvents

/-!
# Conditional particle Brascamp–Lieb

The inequality of Lemma 3.4 for the configuration Gibbs
law, an arbitrary positive-mass particle event with convex strict cyclic
lift, and an H¹ observable of the unconditional gap law. The inverse acts
only on the rotation complement. Convexity gives a null lift boundary,
so piecewise smoothness of that boundary is not needed as an extra premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff ENNReal

namespace Riesz2.ConditionalParticleBrascampLieb

open AffineMetric Riesz1.WeightedSobolev

variable {N : ℕ+}

/-- The weak particle gradient of a gap observable in Lemma 3.4,
with its zero-sum certificate and the actual nonisometric gap differential. -/
def gapPullbackGradient (G : gapTangentSpace N → gapTangentSpace N)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) : gapTangentSpace N :=
  ⟨(gapDerivative N).adjoint (G (liftedGapMap N x)), adjoint_gapDerivative_tangent _⟩

/-- Lemma 3.4: conditional particle Brascamp–Lieb for the actual
Gibbs law. The observable belongs to H¹ of the unconditional gap
law. The conditioning event may depend on rotation as well as gaps. Its
strict cyclic lift is convex. Convex boundary removal covers, in particular,
the paper's piecewise smooth domain convention. The right-hand side is the
inverse Hessian energy on `1⊥`, and is integrable. -/
theorem conditional_particle_brascamp_lieb
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c)
    (A : Set (Riesz1.Configuration N)) (hA : Convex ℝ (openCyclicLift N A))
    (hmass : (pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1) A ≠ 0)
    {f : gapTangentSpace N → ℝ} {G : gapTangentSpace N → gapTangentSpace N}
    (hFG : IsWeightedH1 (intrinsicGapLaw (pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1)) (intrinsicGapDomain N) f G) :
    let μ := pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1
    let ρ := (μ A)⁻¹ • μ.restrict A
    let F := fun X : Riesz1.Configuration N => f (centeredGapChart N (WithLp.toLp 2 (gapVector X)))
    let K := fun X : Riesz1.Configuration N =>
      ⟪gapPullbackGradient G (configurationLift N X),
        (tangentHessian_coercive hc hχ (configurationLift_mem_chamber X)).continuousLinearEquivOfBilin.symm
          (gapPullbackGradient G (configurationLift N X))⟫_ℝ
    Integrable F ρ ∧ Integrable (fun X => F X ^ 2) ρ ∧ Integrable K ρ ∧
      (∫ X, (F X - ∫ Y, F Y ∂ρ) ^ 2 ∂ρ) ≤ ∫ X, K X ∂ρ := by
  dsimp only
  let μ := pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
    (particle_hessian_normalization hN c hc χ hχ).1
  let ρ := (μ A)⁻¹ • μ.restrict A
  let μL := μ.map (configurationLift N)
  let ν := ρ.map (configurationLift N)
  let Ω := interior (openCyclicLift N A)
  let F := fun x => f (liftedGapMap N x)
  let T := gapPullbackGradient G
  let E := fun x => sSup (Set.range fun u : gapTangentSpace N =>
    2 * ⟪T x, u⟫_ℝ - tangentHessian χ x u u)
  have hL := configurationLift_measurableEmbedding N
  have hμp : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [pairGibbsMeasure_eq_library hc hχ]
    infer_instance
  have hac : μL ≪ volume := pairGibbs_lift_absolutelyContinuous hN hc hχ
  have hμch : ∀ᵐ x ∂μL, x ∈ particleChamber N :=
    hL.ae_map_iff.mpr (Eventually.of_forall configurationLift_mem_chamber)
  have hΩ : Ω ⊆ particleChamber N := fun x hx => (interior_openCyclicLift_subset A hx).1
  have hpull : IsWeightedH1 μL (particleChamber N) F (fun x => (T x).val) := by
    apply (gap_weightedH1_pullback (Subset.refl _) hμch ?_).1
    simpa only [μL, map_lift_gap] using hFG
  have hm : μL Ω = μ A := by
    rw [measure_congr (Internal.interior_openCyclicLift_ae hac hA), hL.map_apply,
      preimage_image_eq _ hL.injective]
  have hν : ν = (μL Ω)⁻¹ • μL.restrict Ω := by
    rw [hm]
    exact Internal.map_conditional_lift hac hA
  have hcond : IsWeightedH1 ν Ω F (fun x => (T x).val) := by
    rw [hν]
    exact conditional_weightedH1 hΩ (hm ▸ hmass) hpull
  obtain ⟨hνp, hΩne, hνdensity⟩ := Internal.conditional_lift_density hN hc hχ A hA hmass
  have hνp' : IsProbabilityMeasure ν := hνp
  have hbl := Internal.lifted_particle_brascamp_lieb hN hc hχ
    (interior_openCyclicLift_bounded A) isOpen_interior hΩne hA.interior hΩ ν hνdensity hcond
  have hiF : Integrable F ν := hcond.memLp_fun.integrable (by norm_num)
  have hiF2 : Integrable (fun x => F x ^ 2) ν := hcond.memLp_fun.integrable_sq
  have hiE : Integrable E ν := hbl.2.1
  have hmean := hL.integral_map (μ := ρ) F
  have hvariance := hL.integral_map (μ := ρ) (fun x => (F x - ∫ y, F y ∂ν) ^ 2)
  have henergy := hL.integral_map (μ := ρ) E
  have hinv (X : Riesz1.Configuration N) : E (configurationLift N X) =
      ⟪T (configurationLift N X),
        (tangentHessian_coercive hc hχ (configurationLift_mem_chamber X)).continuousLinearEquivOfBilin.symm
          (T (configurationLift N X))⟫_ℝ :=
    Riesz1.bl_quadratic_sSup_eq_inverse (tangentHessian_coercive hc hχ (configurationLift_mem_chamber X))
      (tangentHessian_symm hχ (configurationLift_mem_chamber X)) (T (configurationLift N X))
  have hFcomp : F ∘ configurationLift N =
      fun X => f (centeredGapChart N (WithLp.toLp 2 (gapVector X))) := by
    funext X
    exact congrArg f (liftedGapMap_configurationLift X)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hFcomp] using hL.integrable_map_iff.mp hiF
  · have hsq := hL.integrable_map_iff.mp hiF2
    change Integrable (fun X => (F ∘ configurationLift N) X ^ 2) ρ at hsq
    simpa only [hFcomp] using hsq
  · exact (hL.integrable_map_iff.mp hiE).congr (Eventually.of_forall hinv)
  · have hb := hbl.1
    rw [hvariance, hmean, henergy] at hb
    have hFpoint (X : Riesz1.Configuration N) : F (configurationLift N X) =
        f (centeredGapChart N (WithLp.toLp 2 (gapVector X))) := congrFun hFcomp X
    simpa only [hFpoint, hinv] using hb

end Riesz2.ConditionalParticleBrascampLieb
