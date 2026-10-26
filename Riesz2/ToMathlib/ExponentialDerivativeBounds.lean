/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CollisionDensityBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivatives of exponentially suppressed densities

Internal estimates for Appendix A. The composition bound
retains the exponential factor in every derivative order. An inverse-power
bound on the derivatives of the exponent is then absorbed by half of a
collision barrier. These are general analytic lemmas, not assertions that
the physical energy satisfies the derivative hypotheses.
-/

public section
open Set
open scoped ContDiff

namespace Riesz2.ExponentialDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The all-order exponential chain rule bound on an open domain keeps the
small factor `exp (f x)`. Replacing it by a global bound would lose collision
flatness. This is internal calculus for Appendix A. -/
theorem norm_iteratedFDeriv_exp_comp_le {Q : Set E} (hQ : IsOpen Q)
    {f : E → ℝ} {n : ℕ} (hf : ContDiffOn ℝ n f Q) {x : E} (hx : x ∈ Q)
    {D : ℝ} (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (f y)) x‖ ≤
      (n.factorial : ℝ) * Real.exp (f x) * D ^ n := by
  have hC (i : ℕ) (_hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i Real.exp Set.univ (f x)‖ ≤ Real.exp (f x) := by
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hDw : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i f Q x‖ ≤ D ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hQ hx]
    exact hD i hi hin
  have h := norm_iteratedFDerivWithin_comp_le
    (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ (n : WithTop ℕ∞) Real.exp Set.univ)
    hf le_rfl uniqueDiffOn_univ hQ.uniqueDiffOn (Set.mapsTo_univ _ _) hx hC hDw
  rw [iteratedFDerivWithin_of_isOpen n hQ hx] at h
  exact h

/-- A polynomial inverse-gap bound on the exponent's tensors, together with
an exponential collision barrier, gives an exponentially vanishing bound
on every density tensor. Constants precede the domain, exponent and point.
This internal lemma does not assume a physical marginal domination contract. -/
theorem inverse_barrier_bound {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (n : ℕ) (A K q : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Set E), IsOpen Q →
      ∀ (f : E → ℝ), ContDiffOn ℝ n f Q → ∀ x ∈ Q,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          f x ≤ K - c * δ ^ (-s) →
          (∀ i : ℕ, 1 ≤ i → i ≤ n →
            ‖iteratedFDeriv ℝ i f x‖ ≤ (A * δ ^ (-q)) ^ i) →
          ‖iteratedFDeriv ℝ n (fun y => Real.exp (f y)) x‖ ≤
            C * Real.exp (-(c / 2) * δ ^ (-s)) := by
  obtain ⟨B, hB, hb⟩ := CollisionDensity.inverse_power_absorption hs hc (q * n)
  let F : ℝ := n.factorial * Real.exp K * A ^ n
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨F * B, mul_nonneg hF hB, fun Q hQ f hf x hx δ hδ hδ1 hfx hD => ?_⟩
  have he : Real.exp (f x) ≤ Real.exp K * Real.exp (-c * δ ^ (-s)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow : (δ ^ (-q)) ^ n = δ ^ (-(q * n)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  calc
    _ ≤ n.factorial * Real.exp (f x) * (A * δ ^ (-q)) ^ n :=
      norm_iteratedFDeriv_exp_comp_le hQ hf hx hD
    _ ≤ n.factorial * (Real.exp K * Real.exp (-c * δ ^ (-s))) *
        (A * δ ^ (-q)) ^ n := by
      gcongr
    _ = F * (δ ^ (-(q * n)) * Real.exp (-c * δ ^ (-s))) := by
      rw [mul_pow, hpow]
      dsimp [F]
      ring
    _ ≤ F * (B * Real.exp (-(c / 2) * δ ^ (-s))) :=
      mul_le_mul_of_nonneg_left (hb δ hδ hδ1) hF
    _ = _ := by ring

end Riesz2.ExponentialDerivative
