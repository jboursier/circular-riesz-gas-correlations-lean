/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.AdmissibleParticlePairs
public import Riesz2.Frozen.PairGibbsNormalizer
public import Riesz1.HelfferSjostrand.RieszAdmissible

/-! # Admissible two-particle Riesz collision data -/

@[expose] public section
open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace Riesz2.DefinitionSanity

def rieszPairsTwo (s : Riesz1.RieszExponent) : ParticlePairData 2 :=
  fun _ => (Riesz1.hsRieszPairPotentials 2 1 (by norm_num) s).potential 0 1

theorem particle_pair_two (χ : ParticlePairData 2)
    (x : EuclideanSpace ℝ (Fin (2 : ℕ+))) :
    particlePairEnergy χ x = 2 * χ ⟨(0, 1), by norm_num⟩ (x 1 - x 0) := by
  have hu : (Finset.univ : Finset {p : Fin (2 : ℕ+) × Fin (2 : ℕ+) // p.1 < p.2}) =
      {⟨(0, 1), by norm_num⟩} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    rcases p with ⟨⟨i, j⟩, hp⟩
    have hi : i.val < 2 := i.isLt
    have hj : j.val < 2 := j.isLt
    have hp' : i.val < j.val := hp
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change i.val = 0
      omega
    · apply Fin.ext
      change j.val = 1
      omega
  unfold particlePairEnergy
  rw [hu, Finset.sum_singleton]

theorem riesz_pair_two_library (s : Riesz1.RieszExponent) (t : ℝ) (ht : 0 < t) :
    Riesz1.hsPairExpression (Riesz1.hsRieszPairPotentials 2 t ht s) =
      fun x => t * particlePairEnergy (rieszPairsTwo s) x := by
  funext x
  rw [particle_pair_two]
  change (2 : ℝ) * (∑ i : Fin 2, ∑ j ∈ Finset.univ.filter (i < ·),
    t * (2 : ℝ) ^ (-s.val) * Riesz1.hurwitzKernel s.val (x j - x i)) = _
  norm_num [Fin.sum_univ_two, Finset.sum_filter, rieszPairsTwo,
    Riesz1.hsRieszPairPotentials]
  ring_nf
  rfl

theorem riesz_pairs_two_admissible (s : Riesz1.RieszExponent) :
    AdmissibleParticlePairs (by norm_num : 2 ≤ ((2 : ℕ+) : ℕ)) (rieszPairsTwo s)
      ((2 : ℝ) ^ (-s.val) * (s.val * (s.val + 1))) := by
  constructor
  · intro p
    let χ := Riesz1.hsRieszPairPotentials 2 1 (by norm_num) s
    refine ⟨χ.smooth 0 1 (by norm_num), ?_,
      χ.leftBoundary 0 1 (by norm_num), χ.rightBoundary 0 1 (by norm_num)⟩
    intro r hr
    have hcurv := χ.curvature 0 1 (by norm_num) r hr
    dsimp [χ, rieszPairsTwo, Riesz1.hsRieszPairPotentials] at hcurv ⊢
    simpa only [one_mul] using hcurv
  · intro a ha
    let t := min 1 (4 * a)
    have ht : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have hta : t ≤ 4 * a := min_le_right _ _
    obtain ⟨C, hC⟩ := Riesz1.hsRiesz_admissible 2 (by norm_num) t ht s
    obtain ⟨hN, _, hC0, hC⟩ := hC
    refine ⟨2 * C / t, by positivity, ?_⟩
    intro x hx
    have hx' : x ∈ Riesz1.hsChamber 2 := hx
    have hbound := hC x hx'
    rw [riesz_pair_two_library s t ht] at hbound
    have hfull := Riesz1.hsPairExpression_contDiffOn
      (Riesz1.hsRieszPairPotentials 2 1 (by norm_num) s)
    rw [riesz_pair_two_library s 1 (by norm_num)] at hfull
    simp only [one_mul] at hfull
    have hdiff : ContDiffAt ℝ 2 (particlePairEnergy (rieszPairsTwo s)) x :=
      (hfull.contDiffAt ((Riesz1.isOpen_hsChamber 2).mem_nhds hx')).of_le (by simp)
    have hg : gradient (fun y => t * particlePairEnergy (rieszPairsTwo s) y) x =
        t • gradient (particlePairEnergy (rieszPairsTwo s)) x := by
      unfold gradient
      rw [fderiv_const_mul (hdiff.differentiableAt (by norm_num))]
      exact map_smul _ _ _
    have hl : Laplacian.laplacian (fun y => t * particlePairEnergy (rieszPairsTwo s) y) x =
        t * Laplacian.laplacian (particlePairEnergy (rieszPairsTwo s)) x :=
      InnerProductSpace.laplacian_smul t hdiff
    rw [hg, hl, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hbound
    change (t * ‖gradient (particlePairEnergy (rieszPairsTwo s)) x‖) ^ 2 / (4 * (2 : ℝ)) -
      t * Laplacian.laplacian (particlePairEnergy (rieszPairsTwo s)) x / 2 ≥
      (Metric.infDist x (particleChamber 2)ᶜ)⁻¹ ^ 2 - C at hbound
    have hcoef : t ^ 2 ≤ 4 * t * a := by nlinarith
    have hgrad := mul_le_mul_of_nonneg_right hcoef
      (sq_nonneg ‖gradient (particlePairEnergy (rieszPairsTwo s)) x‖)
    apply (mul_le_mul_iff_right₀ ht).mp
    have hcancel : (2 * C / t) * t = 2 * C := by field_simp
    have hdist := sq_nonneg (Metric.infDist x (particleChamber 2)ᶜ)⁻¹
    nlinarith

/-- The admissible carrier has a concrete positive-curvature member. -/
theorem admissible_pairs_two_nonempty :
    ∃ (χ : ParticlePairData 2) (c : ℝ), 0 < c ∧
      AdmissibleParticlePairs (by norm_num : 2 ≤ ((2 : ℕ+) : ℕ)) χ c := by
  let s : Riesz1.RieszExponent := ⟨1 / 2, by norm_num, by norm_num⟩
  refine ⟨rieszPairsTwo s, (2 : ℝ) ^ (-s.val) * (s.val * (s.val + 1)), ?_,
    riesz_pairs_two_admissible s⟩
  have hs := s.property.1
  positivity

/-- The nonconstant admissible example has a partition function. -/
theorem riesz_pairs_two_normalizer (s : Riesz1.RieszExponent) :
    0 < pairGibbsNormalizer (rieszPairsTwo s) ∧
      pairGibbsNormalizer (rieszPairsTwo s) < ⊤ := by
  let χ := Riesz1.hsRieszPairPotentials 2 1 (by norm_num) s
  have he : Riesz1.hsFundamentalHamiltonian χ =
      fun X => particlePairEnergy (rieszPairsTwo s) (WithLp.toLp 2 X.val) := by
    funext X
    dsimp only [Riesz1.hsFundamentalHamiltonian, χ]
    simpa only [one_mul] using
      congrFun (riesz_pair_two_library s 1 (by norm_num)) (WithLp.toLp 2 X.val)
  have hZ : pairGibbsNormalizer (rieszPairsTwo s) = Riesz1.hsPartitionFunction χ := by
    rw [Riesz1.hsPartitionFunction_eq_lintegral, he]
    rfl
  rw [hZ]
  exact ⟨Riesz1.hsPartitionFunction_pos χ,
    Riesz1.hsPartitionFunction_lt_top χ (Riesz1.hsRieszPairPotentials_curvature_pos 2
      (by norm_num) s)⟩

end Riesz2.DefinitionSanity
