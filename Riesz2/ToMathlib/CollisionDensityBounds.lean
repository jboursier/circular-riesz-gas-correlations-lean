/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MomentEventBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar collision density bounds

Internal scalar ingredients of Appendix A. A Gibbs
barrier suppresses every inverse power at a collision. These estimates
do not assert bounds on derivatives of the physical energy or smoothness
of a zero extension. Those require separate physical calculus.
-/

public section

open Filter
open scoped Topology

namespace Riesz2.CollisionDensity

/-- An arbitrary inverse power can be absorbed into half of the collision
barrier. The constant is uniform over all positive gaps at most one. -/
theorem inverse_power_absorption {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (p : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      δ ^ (-p) * Real.exp (-c * δ ^ (-s)) ≤
        C * Real.exp (-(c / 2) * δ ^ (-s)) := by
  obtain ⟨C, hC, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := p) hs (show c / 2 < c by linarith)
  refine ⟨C, hC, fun δ hδ hδ1 => ?_⟩
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hh := hb δ⁻¹ hi
  simpa only [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le] using hh

/-- Every inverse power times the collision Gibbs factor tends to zero
as the positive gap tends to zero, for every real power. -/
theorem tendsto_inverse_power_mul_exp {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (p : ℝ) :
    Tendsto (fun δ : ℝ => δ ^ (-p) * Real.exp (-c * δ ^ (-s)))
      (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / s) c hc).comp
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hs))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hδ.le]
  have he : -s * (p / s) = -p := by field_simp
  rw [he]

end Riesz2.CollisionDensity
