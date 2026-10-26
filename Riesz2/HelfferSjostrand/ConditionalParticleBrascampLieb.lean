/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.AffineMetricPart2
public import Riesz1.HelfferSjostrand.BLEnergy

/-!
# Rotation regularization for the conditional particle Brascamp–Lieb inequality

For Lemma 3.4 in the paper, regularize only the common
rotation coordinate. The full Hessian then becomes coercive. On tangent vectors
its inverse energy is exactly the inverse energy of the original tangent
Hessian, independently of the regularization parameter. No inverse of a singular
ambient Hessian is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff

namespace Riesz2.ConditionalParticleBrascampLieb

open AffineMetric

variable {N : ℕ+}

/-- The normalized rotation coordinate used to regularize Lemma 3.4. -/
def rotationCoordinate (N : ℕ+) : EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ :=
  innerSL ℝ (Riesz1.hsUnitVector N)

/-- The rank-one quadratic penalty for Lemma 3.4, on the whole lift. -/
def rotationPenalty (N : ℕ+) (ε : ℝ) (x : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  ε / 2 * (rotationCoordinate N x) ^ 2

/-- The regularized particle potential in the proof of Lemma 3.4. -/
def regularizedPotential (χ : ParticlePairData N) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  particlePairEnergy χ x + rotationPenalty N ε x

/-- The restriction of the particle Hessian to `1⊥` in
Lemma 3.4. It is defined at every lift point. -/
def tangentHessian (χ : ParticlePairData N) (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    gapTangentSpace N →L[ℝ] gapTangentSpace N →L[ℝ] ℝ :=
  (fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x).bilinearComp
    (gapTangentSpace N).subtypeL (gapTangentSpace N).subtypeL

/-- Tangent vectors have zero rotation coordinate, as used in
Lemma 3.4. -/
theorem rotationCoordinate_tangent (u : gapTangentSpace N) :
    rotationCoordinate N u.val = 0 := by
  have hu : u.val ∈ Riesz1.hsOrthSubspace N := by
    rw [← gapTangentSpace_eq_orth]
    exact u.property
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hu

/-- The orthogonal decomposition of a lift vector used in Lemma 3.4. -/
theorem centered_decomposition (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (centeredGapChart N u).val + rotationCoordinate N u • Riesz1.hsUnitVector N = u := by
  rw [centeredGapChart_eq_orthComp, Riesz1.hsOrthComp_coe]
  simp only [rotationCoordinate, innerSL_apply_apply, real_inner_comm (Riesz1.hsUnitVector N) u]
  exact sub_add_cancel _ _

/-- Pythagoras for the decomposition in Lemma 3.4. -/
theorem norm_sq_centered (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    ‖u‖ ^ 2 = ‖centeredGapChart N u‖ ^ 2 + (rotationCoordinate N u) ^ 2 := by
  change ‖u‖ ^ 2 = ‖(centeredGapChart N u).val‖ ^ 2 + (rotationCoordinate N u) ^ 2
  rw [centeredGapChart_eq_orthComp]
  simpa only [rotationCoordinate, innerSL_apply_apply,
    real_inner_comm (Riesz1.hsUnitVector N) u] using Riesz1.norm_sq_hsOrthComp N u

/-- The penalty in Lemma 3.4 is smooth everywhere. -/
theorem rotationPenalty_contDiff (N : ℕ+) (ε : ℝ) :
    ContDiff ℝ ∞ (rotationPenalty N ε) :=
  contDiff_const.mul ((rotationCoordinate N).contDiff.pow 2)

/-- First derivative of the rotation penalty in Lemma 3.4. -/
theorem hasFDerivAt_rotationPenalty (N : ℕ+) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    HasFDerivAt (rotationPenalty N ε)
      ((ε * rotationCoordinate N x) • rotationCoordinate N) x := by
  have hd := (((rotationCoordinate N).hasFDerivAt (x := x)).pow 2).const_mul (ε / 2)
  have he : (ε / 2) • ((2 : ℕ) • (rotationCoordinate N x) ^ (2 - 1)) •
      rotationCoordinate N = (ε * rotationCoordinate N x) • rotationCoordinate N := by
    rw [smul_smul]
    congr 1
    norm_num
    ring
  rw [he] at hd
  exact hd

/-- The penalty adds precisely `ε e ⊗ e` to the Hessian in
Lemma 3.4. -/
theorem hessian_rotationPenalty (N : ℕ+) (ε : ℝ)
    (x u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ (rotationPenalty N ε)) x u v =
      ε * rotationCoordinate N u * rotationCoordinate N v := by
  have he : fderiv ℝ (rotationPenalty N ε) =
      fun y => (ε * rotationCoordinate N y) • rotationCoordinate N := by
    funext y
    exact (hasFDerivAt_rotationPenalty N ε y).fderiv
  rw [he]
  rw [((((rotationCoordinate N).hasFDerivAt (x := x)).const_mul ε).smul_const
    (rotationCoordinate N)).fderiv]
  simp

variable {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}

/-- Smoothness of the regularized potential on the chamber in
Lemma 3.4. -/
theorem regularizedPotential_contDiffOn (h : AdmissibleParticlePairs hN χ c) (ε : ℝ) :
    ContDiffOn ℝ ∞ (regularizedPotential χ ε) (particleChamber N) := by
  have hh := Riesz1.hsPairExpression_contDiffOn (libraryPairs h)
  rw [libraryPairs_energy] at hh
  exact hh.add (rotationPenalty_contDiff N ε).contDiffOn

/-- The regularized Hessian formula in Lemma 3.4. -/
theorem hessian_regularizedPotential (h : AdmissibleParticlePairs hN χ c) (ε : ℝ)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N)
    (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ (regularizedPotential χ ε)) x u v =
      fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x u v +
        ε * rotationCoordinate N u * rotationCoordinate N v := by
  have hh := (Riesz1.hsPairExpression_contDiffOn (libraryPairs h)).contDiffAt
    ((Riesz1.isOpen_hsChamber N).mem_nhds hx)
  rw [libraryPairs_energy] at hh
  have hp := (rotationPenalty_contDiff N ε).contDiffAt (x := x)
  have he : fderiv ℝ (regularizedPotential χ ε) =ᶠ[𝓝 x]
      fun y => fderiv ℝ (particlePairEnergy χ) y + fderiv ℝ (rotationPenalty N ε) y := by
    filter_upwards [((Riesz1.isOpen_hsChamber N).mem_nhds hx)] with y hy
    have hd := (Riesz1.hasFDerivAt_hsPairExpression (libraryPairs h) hy).differentiableAt
    rw [libraryPairs_energy] at hd
    exact fderiv_add hd ((rotationPenalty_contDiff N ε).differentiable (by simp) y)
  rw [he.fderiv_eq, fderiv_fun_add
    ((hh.fderiv_right (by simp : (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞))).differentiableAt
      (by simp))
    ((hp.fderiv_right (by simp : (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞))).differentiableAt
      (by simp))]
  simp only [add_apply, hessian_rotationPenalty]

/-- Symmetry of the restricted particle Hessian used for the inverse in
Lemma 3.4. -/
theorem tangentHessian_symm (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N)
    (u v : gapTangentSpace N) : tangentHessian χ x u v = tangentHessian χ x v u := by
  simp only [tangentHessian, ContinuousLinearMap.bilinearComp_apply,
    Submodule.subtypeL_apply, particlePairEnergy_hessian h hx]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The tangent Hessian is coercive with the paper's constant `2Nc` in
Lemma 3.4. The inverse therefore has no singular default case. -/
theorem tangentHessian_coercive (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N) :
    IsCoercive (tangentHessian χ x) := by
  refine ⟨2 * (N : ℝ) * c, by positivity, fun u => ?_⟩
  simpa only [mul_assoc, pow_two, tangentHessian, ContinuousLinearMap.bilinearComp_apply,
    Submodule.subtypeL_apply] using
    (((particle_hessian_normalization hN c hc χ h).2.1 x hx).2 u).2

/-- Centering either direction leaves the particle Hessian unchanged in
Lemma 3.4. -/
theorem hessian_centered (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N)
    (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    tangentHessian χ x (centeredGapChart N u) (centeredGapChart N v) =
      fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x u v := by
  simp only [tangentHessian, ContinuousLinearMap.bilinearComp_apply,
    Submodule.subtypeL_apply, particlePairEnergy_hessian h hx]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  change _ * (((u p.val.2 - _) - (u p.val.1 - _)) *
    ((v p.val.2 - _) - (v p.val.1 - _))) = _
  ring

/-- Uniform full coercivity after regularizing rotation in Lemma 3.4. -/
theorem regularized_hessian_lower (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {ε : ℝ} {x : EuclideanSpace ℝ (Fin (N : ℕ))}
    (hx : x ∈ particleChamber N) (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    min (2 * (N : ℝ) * c) ε * ‖u‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (regularizedPotential χ ε)) x u u := by
  have ht := (((particle_hessian_normalization hN c hc χ h).2.1 x hx).2
    (centeredGapChart N u)).2
  change 2 * (N : ℝ) * c * ‖centeredGapChart N u‖ ^ 2 ≤
    tangentHessian χ x (centeredGapChart N u) (centeredGapChart N u) at ht
  rw [hessian_centered h hx] at ht
  rw [hessian_regularizedPotential h ε hx, norm_sq_centered]
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (2 * (N : ℝ) * c) ε)
    (sq_nonneg ‖centeredGapChart N u‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (2 * (N : ℝ) * c) ε)
    (sq_nonneg (rotationCoordinate N u))
  nlinarith

/-- For Lemma 3.4, the regularized inverse energy on a tangent
gradient is exactly the original tangent inverse energy for every positive ε. -/
theorem regularized_variational_eq_tangent_inverse
    (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {ε : ℝ} (hε : 0 ≤ ε) {x : EuclideanSpace ℝ (Fin (N : ℕ))}
    (hx : x ∈ particleChamber N) (g : gapTangentSpace N) :
    sSup (Set.range fun u : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      2 * ⟪g.val, u⟫_ℝ - fderiv ℝ (fderiv ℝ (regularizedPotential χ ε)) x u u) =
      ⟪g, (tangentHessian_coercive hc h hx).continuousLinearEquivOfBilin.symm g⟫_ℝ := by
  let B := tangentHessian χ x
  let hB := tangentHessian_coercive hc h hx
  let v := hB.continuousLinearEquivOfBilin.symm g
  have hi (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
      ⟪g, centeredGapChart N u⟫_ℝ = ⟪g.val, u⟫_ℝ := by
    have he := congrArg (fun y => inner ℝ g.val y) (centered_decomposition u)
    rw [inner_add_right, real_inner_smul_right] at he
    have hg : inner ℝ g.val (Riesz1.hsUnitVector N) = 0 := by
      rw [real_inner_comm]
      exact rotationCoordinate_tangent g
    simpa only [hg, mul_zero, add_zero, Submodule.coe_inner] using he
  apply IsGreatest.csSup_eq
  refine ⟨⟨v.val, ?_⟩, ?_⟩
  · dsimp only
    rw [hessian_regularizedPotential h ε hx, rotationCoordinate_tangent, mul_zero, add_zero]
    change 2 * ⟪g, v⟫_ℝ - B v v = ⟪g, v⟫_ℝ
    have hv := Riesz1.bl_quadratic_complete_square hB (tangentHessian_symm h hx) g v
    simpa only [v, sub_self, map_zero, zero_apply, sub_zero] using hv
  · rintro _ ⟨u, rfl⟩
    dsimp only
    have hb := Riesz1.bl_quadratic_le_inverse hB (tangentHessian_symm h hx) g
      (centeredGapChart N u)
    rw [hi, hessian_centered h hx] at hb
    rw [hessian_regularizedPotential h ε hx]
    nlinarith [mul_nonneg hε (sq_nonneg (rotationCoordinate N u))]

/-- The inverse energy in Lemma 3.4 is nonnegative and bounded
by `(2Nc)⁻¹ |g|²` on tangent gradients. -/
theorem tangent_inverse_bounds (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N)
    (g : gapTangentSpace N) :
    0 ≤ ⟪g, (tangentHessian_coercive hc h hx).continuousLinearEquivOfBilin.symm g⟫_ℝ ∧
      ⟪g, (tangentHessian_coercive hc h hx).continuousLinearEquivOfBilin.symm g⟫_ℝ ≤
        ‖g‖ ^ 2 / (2 * (N : ℝ) * c) := by
  refine ⟨Riesz1.bl_inverse_energy_nonneg (tangentHessian_coercive hc h hx) g, ?_⟩
  apply Riesz1.bl_inverse_energy_le_norm_sq_div (tangentHessian_coercive hc h hx)
    (tangentHessian_symm h hx) (by positivity)
  intro u
  exact (((particle_hessian_normalization hN c hc χ h).2.1 x hx).2 u).2

end Riesz2.ConditionalParticleBrascampLieb
