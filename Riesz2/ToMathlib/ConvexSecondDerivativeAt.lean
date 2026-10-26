/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.ConvexLineHessian
public import Mathlib.Analysis.Convex.Function

/-!
# Convex Hessians at a single twice differentiable point

The first derivative must exist on a neighbourhood of the point and be
differentiable at that point. Continuity of the second derivative on a
neighbourhood is unnecessary. This is the pointwise supplement to the
companion library's C² convex Hessian theorem.
-/

public section

open Set Filter
open scoped Topology

namespace Riesz2

/-- A convex function has a nonnegative Hessian at any point where its
locally defined first derivative is differentiable. No C² neighbourhood
assumption is imposed. -/
theorem convexOn_second_fderiv_nonneg_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f : E → ℝ} (hU : IsOpen U) (hf : ConvexOn ℝ U f)
    {x : E} (hx : x ∈ U)
    (hd : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z)
    (hdd : DifferentiableAt ℝ (fderiv ℝ f) x) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hd.and (hU.mem_nhds hx))
  let a : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + v)
  have ha (t : ℝ) : a t = x + t • v := by
    simp [a, AffineMap.lineMap_apply_module', add_comm]
  let I := a ⁻¹' Metric.ball x r
  have hIo : IsOpen I := Metric.isOpen_ball.preimage (show Continuous a by
    have : a = fun t : ℝ => x + t • v := funext ha
    rw [this]
    fun_prop)
  have h0 : (0 : ℝ) ∈ I := by
    change a 0 ∈ Metric.ball x r
    simpa [ha] using hr
  have hc : ConvexOn ℝ I (fun t : ℝ => f (x + t • v)) := by
    have ht := (hf.subset (fun z hz => (hrs hz).2) (convex_ball x r)).comp_affineMap a
    simpa only [Function.comp_def, ha] using ht
  have hdI (t : ℝ) (ht : t ∈ I) : DifferentiableAt ℝ f (x + t • v) := by
    simpa only [ha] using (hrs (show a t ∈ Metric.ball x r from ht)).1
  have hline (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f (x + t • v) v) t :=
    Riesz1.hasDerivAt_comp_line (hdI t ht)
  have hmono := hc.monotoneOn_deriv (fun t ht => (hline t ht).differentiableAt)
  have hD : HasDerivAt (deriv (fun t : ℝ => f (x + t • v)))
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    apply (Riesz1.hasDerivAt_fderiv_comp_line hdd).congr_of_eventuallyEq
    filter_upwards [hIo.mem_nhds h0] with t ht
    exact (hline t ht).deriv
  have hi := hmono.derivWithin_nonneg (x := 0)
  rwa [derivWithin_of_isOpen hIo h0, hD.deriv] at hi

end Riesz2
