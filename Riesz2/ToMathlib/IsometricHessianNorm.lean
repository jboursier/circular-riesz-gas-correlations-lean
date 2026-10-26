/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineMetricTransport

/-!
# Hessian norms under isometric affine restriction

The bilinear operator norm of the Hessian controls its restriction to any
isometrically included affine subspace, including a mass hyperplane.
-/

public section
noncomputable section
open scoped ContDiff
namespace Riesz2.IsometricHessianNorm

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, metric input: the operator norm of a Hessian
cannot increase under an affine isometric restriction. This applies to the
actual mass-hyperplane inclusion and its translation by the all-ones vector. -/
theorem hessian_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →ₗᵢ[ℝ] E) (V : E → ℝ) (v₀ : E) (z : F)
    (hV : ContDiffAt ℝ 2 V (L z + v₀)) :
    ‖fderiv ℝ (fderiv ℝ (fun w : F => V (L w + v₀))) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ V) (L z + v₀)‖ := by
  let A := fderiv ℝ (fderiv ℝ V) (L z + v₀)
  let B := fderiv ℝ (fderiv ℝ (fun w : F => V (L w + v₀))) z
  have he (u v : F) : B u v = A (L u) (L v) :=
    AffineMetricTransport.hessian_comp_affine L.toContinuousLinearMap v₀ hV u v
  change ‖B‖ ≤ ‖A‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))
  intro v
  rw [he]
  calc
    ‖A (L u) (L v)‖ ≤ ‖A (L u)‖ * ‖L v‖ := (A (L u)).le_opNorm _
    _ ≤ (‖A‖ * ‖L u‖) * ‖L v‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [L.norm_map, L.norm_map]

end Riesz2.IsometricHessianNorm
