/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConvexLocalization

/-!
# Convex barriers retained under marginalization

Subtracting a function of the retained variables commutes with taking the
negative logarithm of a Gibbs fibre integral. The fibre may have dimension zero.
-/

public section
noncomputable section
open MeasureTheory Set

namespace Riesz2.MarginalBarrier

/-- Internal marginalization interface: a convex residual of the joint
potential gives a convex residual of its marginal, with no regularity or
integrability hypotheses beyond convexity on the bounded open joint domain. -/
theorem convex_subtraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ}
    {Ω : Set (E × EuclideanSpace ℝ (Fin m))}
    (ho : IsOpen Ω) (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    (U : E × EuclideanSpace ℝ (Fin m) → ℝ) (B : E → ℝ)
    (hR : ConvexOn ℝ Ω (fun q => U q - B q.1)) :
    ConvexOn ℝ (Prod.fst '' Ω) (fun x =>
      -Real.log (∫ y, Ω.indicator (fun q => Real.exp (-U q)) (x,y)) - B x) := by
  classical
  have h := (convexLocalization ho hc hb hR (fun _ => 0)).2
  simp only [zero_sub, sub_zero] at h
  apply h.congr
  intro x hx
  have hp := (convexLocalization ho hc hb hR (fun _ => 0)).1 x hx
  have he : (fun y => Ω.indicator (fun q => Real.exp (-U q)) (x,y)) =
      fun y => Real.exp (-B x) *
        Ω.indicator (fun q => Real.exp (-(U q - B q.1))) (x,y) := by
    funext y
    by_cases hq : (x,y) ∈ Ω
    · simp only [indicator_of_mem hq]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp only [indicator_of_notMem hq, mul_zero]
  dsimp only at ⊢
  rw [he, integral_const_mul,
    Real.log_mul (Real.exp_ne_zero _) hp.2.ne', Real.log_exp]
  ring

end Riesz2.MarginalBarrier
