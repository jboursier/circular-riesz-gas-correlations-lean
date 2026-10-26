/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.ConvexLineHessian

/-!
# Convexity from Hessians tangent to a convex carrier

The carrier may have empty ambient interior. Only directions joining two
points of the carrier enter the curvature condition. This supplements the
companion library's criterion on open sets and applies to affine simplices.
-/

public section

open Set

namespace Riesz2

/-- The Hessian criterion on a possibly lower dimensional convex carrier.
Ambient derivatives exist at every point, but curvature is needed only in
directions joining points of the carrier. -/
theorem convexOn_of_tangent_hessian_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → ℝ} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hdf : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hH : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      0 ≤ fderiv ℝ (fderiv ℝ f) x (z - y) (z - y)) :
    ConvexOn ℝ S f := by
  refine ⟨hS, fun y hy z hz a b ha hb hab => ?_⟩
  let l : ℝ → E := fun t => y + t • (z - y)
  have hl (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : l t ∈ S := by
    have he : l t = (1 - t) • y + t • z := by dsimp [l]; module
    rw [he]
    exact hS hy hz (by linarith [ht.2]) ht.1 (by ring)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (l t)) (fderiv ℝ f (l t) (z - y)) t :=
    Riesz1.hasDerivAt_comp_line (hf _ (hl t ht))
  have hdd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => fderiv ℝ f (l t) (z - y))
        (fderiv ℝ (fderiv ℝ f) (l t) (z - y) (z - y)) t :=
    Riesz1.hasDerivAt_fderiv_comp_line_at (hdf _ (hl t ht))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => f (l t)) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hdd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hH _ (hl t (interior_subset ht)) y hy z hz)
  have hi := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ha hb hab
  have he : l b = a • y + b • z := by
    dsimp [l]
    have ha' : a = 1 - b := by linarith
    rw [ha']
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, he, l,
    zero_smul, add_zero, one_smul, add_sub_cancel] using hi

end Riesz2
