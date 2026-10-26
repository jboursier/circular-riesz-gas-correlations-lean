/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.BoundedGradientCutoff
public import Riesz1.ToMathlib.WeightedSobolev.GraphLimits
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Density regularization in the weighted Sobolev graph

The smooth quotients `g / (w + a)` approximate `g / w` on a positive
density carrier. An L² bound on the force times the density score controls
the extra gradient term. This is a general internal approximation criterion.
Physical applications must prove its integrability and differential premises.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.DensityScore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exact derivative of a regularized smooth density quotient. -/
theorem regularized_gradient_internal {w g : E → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    {a : ℝ} {x : E} (ha : w x + a ≠ 0) :
    gradient (fun y => g y / (w y + a)) x =
      (w x + a)⁻¹ • gradient g x -
        (g x / (w x + a) ^ 2) • gradient w x := by
  have hi : HasFDerivAt (fun y => (w y + a)⁻¹)
      (-((w x + a) ^ 2)⁻¹ • fderiv ℝ w x) x :=
    (hasDerivAt_inv ha).comp_hasFDerivAt x
      (((hw.differentiable (by simp)) x).hasFDerivAt.add_const a)
  have hp := ((hg.differentiable (by simp)) x).hasFDerivAt.mul hi
  have he := hp.hasGradientAt.gradient
  simp only [gradient, map_add, map_smul, smul_smul] at he
  simpa only [gradient, Pi.mul_def, div_eq_mul_inv, mul_neg, neg_smul, sub_eq_add_neg, add_comm] using he

variable [MeasurableSpace E] [BorelSpace E]

/-- Internal H¹ certificate by positive denominator regularization.
The numerator and its gradient agree with the specified quotient jet on
the positive carrier. No boundary regularity of the quotient is assumed.
The extran L² premise is the product of the quotient with the density score. -/
theorem isWeightedH1_of_density_quotient_internal
    (μ : Measure E) (U : Set E) {w g F : E → ℝ} {G : E → E}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (hwn : ∀ x, 0 ≤ w x)
    (hpos : ∀ᵐ x ∂μ, 0 < w x)
    (hval : ∀ᵐ x ∂μ, g x = w x * F x)
    (hjet : ∀ᵐ x ∂μ, gradient g x = w x • G x + F x • gradient w x)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hS : MemLp (fun x => (F x / w x) • gradient w x) 2 μ) :
    Riesz1.WeightedSobolev.IsWeightedH1 μ U F G := by
  let a : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  let φ : ℕ → E → ℝ := fun k x => g x / (w x + a k)
  let θ : ℕ → E → ℝ := fun k x => w x / (w x + a k)
  let α : ℕ → E → ℝ := fun k x => a k * w x / (w x + a k) ^ 2
  let S : E → E := fun x => (F x / w x) • gradient w x
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have hφ (k : ℕ) : ContDiff ℝ ∞ (φ k) :=
    hg.div (hw.add contDiff_const) (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (hwn x) (ha k)))
  have hb (k : ℕ) (x : E) : 0 ≤ θ k x ∧ θ k x ≤ 1 ∧ 0 ≤ α k x ∧ α k x ≤ 1 := by
    have hden : 0 < w x + a k := add_pos_of_nonneg_of_pos (hwn x) (ha k)
    have hwx := hwn x
    dsimp only [θ, α]
    refine ⟨by positivity, (div_le_one hden).mpr (by linarith [ha k]), by positivity, ?_⟩
    apply (div_le_one (sq_pos_of_pos hden)).mpr
    nlinarith [sq_nonneg (w x), sq_nonneg (a k), mul_nonneg (hwn x) (ha k).le]
  have hv (k : ℕ) : ∀ᵐ x ∂μ, φ k x = θ k x * F x := by
    filter_upwards [hval] with x hx
    dsimp [φ, θ]
    rw [hx]
    ring
  have hj (k : ℕ) : ∀ᵐ x ∂μ,
      gradient (φ k) x = θ k x • G x + α k x • S x := by
    filter_upwards [hpos, hval, hjet] with x hx hxv hxj
    rw [regularized_gradient_internal hw hg (ne_of_gt (add_pos hx (ha k))), hxj, hxv]
    dsimp only [θ, α, S]
    simp only [smul_add, smul_smul]
    have hc : (w x + a k)⁻¹ * F x -
        (w x * F x / (w x + a k) ^ 2) =
        (a k * w x / (w x + a k) ^ 2) * (F x / w x) := by
      field_simp [hx.ne', (add_pos hx (ha k)).ne']
      ring
    rw [show w x / (w x + a k) = (w x + a k)⁻¹ * w x by ring,
      add_sub_assoc, ← sub_smul, hc]
  have hφb (k : ℕ) : ∀ᵐ x ∂μ, ‖φ k x‖ ≤ ‖F x‖ := by
    filter_upwards [hv k] with x hx
    rw [hx, norm_mul, Real.norm_of_nonneg (hb k x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb k x).2.1
  have hgb (k : ℕ) : ∀ᵐ x ∂μ, ‖gradient (φ k) x‖ ≤ ‖G x‖ + ‖S x‖ := by
    filter_upwards [hj k] with x hx
    rw [hx]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_of_nonneg (hb k x).1,
      Real.norm_of_nonneg (hb k x).2.2.1]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (hb k x).2.1)
      (mul_le_of_le_one_left (norm_nonneg _) (hb k x).2.2.2)
  have hm (k : ℕ) : MemLp (φ k) 2 μ :=
    hF.of_le_mul (c := 1) (hφ k).continuous.aestronglyMeasurable
      (by simpa only [one_mul] using hφb k)
  have hgm (k : ℕ) : MemLp (gradient (φ k)) 2 μ :=
    (hG.norm.add hS.norm).of_le_mul (c := 1)
      (Riesz1.WeightedSobolev.continuous_gradient_of_contDiff (hφ k)).aestronglyMeasurable
      (by
        filter_upwards [hgb k] with x hx
        change ‖gradient (φ k) x‖ ≤ 1 * ‖‖G x‖ + ‖S x‖‖
        rwa [one_mul, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))])
  have hat : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hθt (x : E) (hx : 0 < w x) : Tendsto (fun k => θ k x) atTop (𝓝 1) := by
    simpa only [θ, Pi.div_def, Pi.div_apply, Pi.add_apply, add_zero, div_self hx.ne'] using
      (tendsto_const_nhds (x := w x)).div
        ((tendsto_const_nhds (x := w x)).add hat) (by simpa using hx.ne')
  have hαt (x : E) (hx : 0 < w x) : Tendsto (fun k => α k x) atTop (𝓝 0) := by
    simpa only [α, Pi.div_def, Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, zero_mul, add_zero, zero_div] using
      (hat.mul tendsto_const_nhds).div ((tendsto_const_nhds.add hat).pow 2)
        (by simpa only [add_zero] using pow_ne_zero 2 hx.ne')
  refine ⟨hF, hG, φ, fun k => ⟨univ, isOpen_univ, subset_univ _, (hφ k).contDiffOn⟩, ?_, ?_⟩
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq φ hm F hF).mp
    apply Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hm hF hF.norm (hφb) (ae_of_all _ fun _ => le_rfl)
    filter_upwards [hpos, ae_all_iff.mpr hv] with x hx hxv
    have ht := (hθt x hx).mul_const (F x)
    simpa only [one_mul] using ht.congr (fun k => (hxv k).symm)
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hgm G hG).mp
    apply Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hgm hG (hG.norm.add hS.norm) hgb
      (ae_of_all _ fun x => le_add_of_nonneg_right (norm_nonneg (S x)))
    filter_upwards [hpos, ae_all_iff.mpr hj] with x hx hxj
    have ht := ((hθt x hx).smul_const (G x)).add ((hαt x hx).smul_const (S x))
    simpa only [one_smul, zero_smul, add_zero] using ht.congr (fun k => (hxj k).symm)

end Riesz2.DensityScore
