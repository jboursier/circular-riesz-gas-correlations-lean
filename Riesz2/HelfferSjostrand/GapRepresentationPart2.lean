/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.GapRepresentation
public import Riesz2.ToMathlib.FiniteLinearPotential

/-!
# Native ambient coefficient bridges

Additional native-carrier interfaces for Proposition 3.3.
The matrix is the ambient Hessian, including its normal component.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set Matrix
open scoped BigOperators ContDiff RealInnerProductSpace

namespace Riesz2.GapRepresentation

variable {N : ℕ+}

/-- The actual ambient Hessian is nonnegative in every ambient direction,
Proposition 3.3. It is a positive combination of the
rank-one pair-separation forms, including on the full native simplex. -/
theorem ambientHessian_posSemidef {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hc : 0 ≤ c)
    (hχ : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N) :
    (hessianMatrix (pairAmbientGapPotential χ)
      (WithLp.toLp 2 (fun k => 1 + z.val k))).PosSemidef := by
  classical
  let P := {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2}
  let l (p : P) : EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ :=
    (N : ℝ)⁻¹ • ∑ a ∈ Finset.univ.filter
      (fun a : Fin (N : ℕ) => p.val.1.val ≤ a.val ∧ a.val < p.val.2.val),
      PiLp.proj 2 (fun _ : Fin (N : ℕ) => ℝ) a
  have hl (p : P) (y : EuclideanSpace ℝ (Fin (N : ℕ))) : l p y =
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (N : ℕ) => p.val.1.val ≤ a.val ∧ a.val < p.val.2.val), y a) / (N : ℝ) := by
    simp only [l, _root_.smul_apply, _root_.sum_apply,
      PiLp.proj_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hfun : (fun y => ∑ p : P, (2 : ℝ) * χ p (l p y)) = pairAmbientGapPotential χ := by
    funext y
    simp only [pairAmbientGapPotential, ← Finset.mul_sum, hl]
    rfl
  let y : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 (fun k => 1 + z.val k)
  have harg (p : P) : l p y ∈ Ioo (0 : ℝ) 1 := by
    rw [hl]
    exact pair_argument_mem z hz p
  have hs := ambientPotential_contDiffAt hχ hz
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun t => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact ambientHessian_symmetric hχ hz j i
  · have hd := (finite_linear_potential_derivatives (fun _ : P => (2 : ℝ)) χ l
      (fun _ => Ioo 0 1) (fun _ => isOpen_Ioo)
      (fun p => (hχ.1 p).1.of_le (by norm_num)) y harg
      (WithLp.toLp 2 t) (WithLp.toLp 2 t)).2
    rw [hfun] at hd
    have hn : 0 ≤ fderiv ℝ (fderiv ℝ (pairAmbientGapPotential χ)) y
        (WithLp.toLp 2 t) (WithLp.toLp 2 t) := by
      rw [hd]
      apply Finset.sum_nonneg
      intro p _
      exact mul_nonneg (mul_nonneg (by norm_num) (hc.trans ((hχ.1 p).2.1 _ (harg p))))
        (mul_self_nonneg _)
    rw [Intrinsic.hessianMatrix_bilinear hs] at hn
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using hn

/-- Global measurability of the ambient coefficient entries, Proposition 3.3. Local smoothness is used separately for compact tests. -/
theorem ambientHessian_measurable (χ : ParticlePairData N) (i j : Fin (N : ℕ)) :
    Measurable (fun z : gapTangentSpace N =>
      hessianMatrix (pairAmbientGapPotential χ)
        (WithLp.toLp 2 (fun k => 1 + z.val k)) i j) := by
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      hessianMatrix (pairAmbientGapPotential χ) y i j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (N : ℕ) => ℝ) i).continuous.measurable.comp
      (measurable_fderiv_apply_const ℝ (gradient (pairAmbientGapPotential χ))
        (EuclideanSpace.single j 1))
  exact hm.comp (by fun_prop)

end Riesz2.GapRepresentation
