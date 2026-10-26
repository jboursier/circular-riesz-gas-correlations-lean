/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Tactic

/-!
# Gradient inequality for convex functions

Let `R` be convex on a set `Ω` of a real normed space, and let `R` be differentiable at a point
`x ∈ Ω`. For every `y ∈ Ω` the derivative at `x` satisfies the gradient inequality
`fderiv ℝ R x (y - x) ≤ R y - R x`.

The proof restricts `R` to the line through `x` and `y`, where the inequality is the one-variable
bound `ConvexOn.deriv_le_slope` at the left endpoint of the segment.
-/

@[expose] public section

namespace Riesz2.ConvexGradient

/-- If `R` is convex on `Ω` and differentiable at `x ∈ Ω`, then `fderiv ℝ R x (y - x) ≤ R y - R x`
for every `y ∈ Ω`. -/
theorem fderiv_apply_sub_le_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {R : E → ℝ} (hR : ConvexOn ℝ Ω R) {x y : E} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hdiff : DifferentiableAt ℝ R x) :
    fderiv ℝ R x (y - x) ≤ R y - R x := by
  set ℓ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hℓ
  have hconv : ConvexOn ℝ (ℓ ⁻¹' Ω) (R ∘ ℓ) := hR.comp_affineMap ℓ
  have h0 : (0 : ℝ) ∈ ℓ ⁻¹' Ω := by
    simpa [Set.mem_preimage, hℓ] using hx
  have h1 : (1 : ℝ) ∈ ℓ ⁻¹' Ω := by
    simpa [Set.mem_preimage, hℓ] using hy
  have hline : HasDerivAt (fun t : ℝ => ℓ t) (y - x) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
    have hfun : (fun t : ℝ => ℓ t) = fun t : ℝ => x + t • (y - x) := by
      funext t
      simp only [hℓ, AffineMap.lineMap_apply_module]
      module
    rw [hfun]
    simpa using h
  have hcomp : HasDerivAt (R ∘ fun t : ℝ => ℓ t) (fderiv ℝ R x (y - x)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdiff.hasFDerivAt hline (by simp [hℓ])
  have hslope := hconv.deriv_le_slope h0 h1 zero_lt_one hcomp.differentiableAt
  rw [hcomp.deriv] at hslope
  simpa [slope_def_field, hℓ] using hslope

end Riesz2.ConvexGradient

end
