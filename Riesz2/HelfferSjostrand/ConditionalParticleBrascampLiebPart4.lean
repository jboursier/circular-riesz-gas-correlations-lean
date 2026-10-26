/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalParticleBrascampLiebPart3

/-!
# Conditional Brascamp–Lieb on the original Euclidean lift law

This completes the regularization and limit step of Lemma 3.4:
the law here has the original pair potential, and the gradient is tangent.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff ENNReal

namespace Riesz2.ConditionalParticleBrascampLieb.Internal

open AffineMetric Riesz1.WeightedSobolev

variable {N : ℕ+}

/-- In Lemma 3.4, the tangent inverse energy is integrable under
any finite lift law carried by the chamber, as soon as its gradient is L².
Use the library's coercive energy lemma with the fixed rotation penalty one. -/
theorem integrable_tangent_energy
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c)
    {ρ : Measure (EuclideanSpace ℝ (Fin (N : ℕ)))} [IsFiniteMeasure ρ]
    (hρ : ∀ᵐ x ∂ρ, x ∈ particleChamber N)
    {G : EuclideanSpace ℝ (Fin (N : ℕ)) → gapTangentSpace N}
    (hG : MemLp (fun x => (G x).val) 2 ρ) :
    Integrable (fun x => sSup (Set.range fun u : gapTangentSpace N =>
      2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u)) ρ := by
  have hi := Riesz1.integrable_energy_field
    (V := regularizedPotential χ 1) (lt_min (by positivity) zero_lt_one)
    (fun x hx u => regularized_hessian_lower hc hχ hx u) hρ hG
  apply hi.congr
  filter_upwards [hρ] with x hx
  exact (regularized_variational_eq_tangent_inverse hc hχ zero_le_one hx (G x)).trans
    (Riesz1.bl_quadratic_sSup_eq_inverse (tangentHessian_coercive hc hχ hx)
      (tangentHessian_symm hχ hx) (G x)).symm

/-- The regularization and limit step of Lemma 3.4, for the
original normalized lift law on a bounded open convex conditioning domain.
Its hypotheses refer to that original law. Regularized H¹ membership,
normalization and the density limit are proved inside the argument. -/
theorem lifted_particle_brascamp_lieb
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c)
    {Ω : Set (EuclideanSpace ℝ (Fin (N : ℕ)))}
    (hΩb : Bornology.IsBounded Ω) (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩc : Convex ℝ Ω) (hΩ : Ω ⊆ particleChamber N)
    (ρ : Measure (EuclideanSpace ℝ (Fin (N : ℕ)))) [IsProbabilityMeasure ρ]
    (hρ : ρ = (volume.restrict Ω).withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ x) /
        ∫ y in Ω, Real.exp (-particlePairEnergy χ y))))
    {F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (N : ℕ)) → gapTangentSpace N}
    (hFG : IsWeightedH1 ρ Ω F (fun x => (G x).val)) :
    (∫ x, (F x - ∫ y, F y ∂ρ) ^ 2 ∂ρ) ≤
        ∫ x, sSup (Set.range fun u : gapTangentSpace N =>
          2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u) ∂ρ ∧
      Integrable (fun x => sSup (Set.range fun u : gapTangentSpace N =>
        2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u)) ρ ∧
      (∀ (x) (hx : x ∈ Ω), sSup (Set.range fun u : gapTangentSpace N =>
        2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u) =
          ⟪G x, (tangentHessian_coercive hc hχ (hΩ hx)).continuousLinearEquivOfBilin.symm
            (G x)⟫_ℝ) := by
  have hρΩ : ∀ᵐ x ∂ρ, x ∈ Ω := by
    rw [hρ]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩo.measurableSet)
  have hraw : Integrable (fun x => Real.exp (-particlePairEnergy χ x))
      (volume.restrict Ω) := by
    by_contra hn
    have hz : ρ = 0 := by
      simp [hρ, integral_undef hn]
    have hu := measure_univ (μ := ρ)
    simp [hz] at hu
  change ρ = (volume.restrict Ω).tilted (fun x => -particlePairEnergy χ x) at hρ
  let p := rotationPenalty N 1
  have hp : Measurable p := (rotationPenalty_contDiff N 1).continuous.measurable
  have hp0 : ∀ᵐ x ∂ρ, 0 ≤ p x := Eventually.of_forall fun x => by
    dsimp [p, rotationPenalty]
    positivity
  let E := fun x => sSup (Set.range fun u : gapTangentSpace N =>
    2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u)
  have hi : Integrable E ρ := integrable_tangent_energy hN hc hχ
    (hρΩ.mono fun _ hx => hΩ hx) hFG.memLp_grad
  have hBL (ε : ℝ) (hε : 0 < ε) :
      (∫ x, (F x - ∫ y, F y ∂ρ.tilted (fun z => -ε * p z)) ^ 2
        ∂ρ.tilted (fun z => -ε * p z)) ≤
      ∫ x, E x ∂ρ.tilted (fun z => -ε * p z) := by
    have ht : ρ.tilted (fun x => -ε * p x) =
        (volume.restrict Ω).withDensity (fun x =>
          ENNReal.ofReal (Real.exp (-regularizedPotential χ ε x) /
            ∫ y in Ω, Real.exp (-regularizedPotential χ ε y))) := by
      rw [hρ, tilted_tilted hraw]
      congr 1
      funext x
      dsimp [p, regularizedPotential, rotationPenalty]
      ring
    have hFGt : IsWeightedH1 (ρ.tilted (fun x => -ε * p x)) Ω F
        (fun x => (G x).val) := weightedH1_of_measure_le_smul
      ENNReal.ofReal_ne_top (damping_le_smul hp0 hε.le) (Subset.refl Ω) hFG
    exact (regularized_particle_brascamp_lieb hN hc hχ hΩb hΩo hΩne hΩc hΩ hε _ ht hFGt).2.1
  refine ⟨?_, hi, fun x hx => Riesz1.bl_quadratic_sSup_eq_inverse
    (tangentHessian_coercive hc hχ (hΩ hx)) (tangentHessian_symm hχ (hΩ hx)) (G x)⟩
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) :=
    nhdsWithin_mono _ Ioi_subset_Ici_self
  apply le_of_tendsto_of_tendsto
    ((tendsto_damping_variance hp.aemeasurable hp0 hFG.memLp_fun).mono_left hfilter)
    ((tendsto_damping_integral hp.aemeasurable hp0 hi).mono_left hfilter)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact hBL ε hε

end Riesz2.ConditionalParticleBrascampLieb.Internal
