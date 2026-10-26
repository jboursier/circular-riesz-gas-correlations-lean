/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineMetricTransport
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Riesz1.HelfferSjostrand.LogSobolevSmoothPotential

/-!
# Quantitative derivatives of affine pullbacks

Gradient and Hessian comparisons require only differentiability of the function,
so they can be used before any collision or Gibbs admissibility assertion.
-/

@[expose] public section

noncomputable section

namespace Riesz2.AffinePullback

open Riesz1.LogSobolevInternal

section Gradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- An invertible affine change controls the original gradient by the pulled-back one. -/
theorem gradient_norm_le (e : E ≃L[ℝ] F) (v : F) {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (e x + v)) :
    ‖gradient f (e x + v)‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      ‖gradient (fun z => f (e z + v)) x‖ := by
  have hd := (hf.hasFDerivAt.comp x (e.hasFDerivAt.add_const v)).fderiv
  simp only [Function.comp_def] at hd
  have he : fderiv ℝ f (e x + v) =
      (fderiv ℝ (fun z => f (e z + v)) x).comp e.symm.toContinuousLinearMap := by
    rw [hd]
    ext u
    simp
  rw [norm_gradient_eq_norm_fderiv, he, norm_gradient_eq_norm_fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

end Gradient

section Hessian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quadratic Hessian upper bound pulls back with the squared operator norm. -/
theorem hessian_upper (A : E →L[ℝ] F) (v : F) {f : F → ℝ} {x : E} {D : ℝ}
    (hf : ContDiffAt ℝ 2 f (A x + v)) (hD : 0 ≤ D)
    (hu : ∀ u : F, fderiv ℝ (fderiv ℝ f) (A x + v) u u ≤ D * ‖u‖ ^ 2)
    (u : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (A z + v))) x u u ≤
      (D * ‖A‖ ^ 2) * ‖u‖ ^ 2 := by
  rw [AffineMetricTransport.hessian_comp_affine A v hf]
  apply (hu (A u)).trans
  have hn := pow_le_pow_left₀ (norm_nonneg (A u)) (A.le_opNorm u) 2
  simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left hn hD

/-- A strict Hessian lower bound survives an invertible affine change. -/
theorem hessian_lower (e : E ≃L[ℝ] F) (v : F) {f : F → ℝ} {x : E} {κ M : ℝ}
    (hf : ContDiffAt ℝ 2 f (e x + v)) (hκ : 0 ≤ κ) (hM : 0 < M)
    (he : ‖e.symm.toContinuousLinearMap‖ ≤ M)
    (hu : ∀ u : F, κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (e x + v) u u)
    (u : E) :
    (κ / M ^ 2) * ‖u‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun z => f (e z + v))) x u u := by
  have hh := AffineMetricTransport.hessian_comp_affine e.toContinuousLinearMap v hf u u
  change fderiv ℝ (fderiv ℝ (fun z => f (e z + v))) x u u = _ at hh
  rw [hh]
  have hn : ‖u‖ ≤ M * ‖e u‖ := by
    calc
      ‖u‖ = ‖e.symm (e u)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e u‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ M * ‖e u‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
  have hs := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg u) hn 2) (div_nonneg hκ (sq_nonneg M))
  have hi : κ / M ^ 2 * (M * ‖e u‖) ^ 2 = κ * ‖e u‖ ^ 2 := by
    field_simp
  rw [hi] at hs
  exact hs.trans (hu (e u))

end Hessian

end Riesz2.AffinePullback
