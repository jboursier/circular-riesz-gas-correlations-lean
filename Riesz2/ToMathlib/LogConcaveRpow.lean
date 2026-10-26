/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Multiplicative midpoint inequality for log-concave functions

A nonnegative function `f` that is log-concave on its positive set `{x | 0 < f x}` satisfies
`f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)` for every `0 < t < 1`. The Bakry–Émery input
of `Riesz2.Bridges.ConvexMeasureInputs` uses this form of log-concavity.

The positive set is convex and `log ∘ f` is concave on it, as in the convention of
`Riesz2.External.LogConcaveConvergence`.
-/

public section

namespace Riesz2

/-- Let `f : E → ℝ` be nonnegative, and let `log ∘ f` be concave on the positive set
`{x | 0 < f x}`. Then for all `x y : E` and every `0 < t < 1`, the inequality
`f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)` holds. -/
theorem rpow_mul_rpow_le_of_concaveOn_log {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (x y : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y) := by
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  by_cases hx : f x = 0
  · rw [hx, Real.zero_rpow ht0.ne', zero_mul]
    exact hf0 _
  by_cases hy : f y = 0
  · rw [hy, Real.zero_rpow ht1'.ne', mul_zero]
    exact hf0 _
  have hx' : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hx)
  have hy' : 0 < f y := lt_of_le_of_ne (hf0 y) (Ne.symm hy)
  -- The combination stays in the positive set, which is convex.
  have hz : 0 < f (t • x + (1 - t) • y) := hf.1 hx' hy' ht0.le ht1'.le (by ring)
  have hlog : t * Real.log (f x) + (1 - t) * Real.log (f y) ≤
      Real.log (f (t • x + (1 - t) • y)) := by
    have := hf.2 hx' hy' ht0.le ht1'.le (by ring)
    simpa only [smul_eq_mul] using this
  calc f x ^ t * f y ^ (1 - t)
      = Real.exp (Real.log (f x) * t + Real.log (f y) * (1 - t)) := by
        rw [Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hy', Real.exp_add]
    _ ≤ Real.exp (Real.log (f (t • x + (1 - t) • y))) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = f (t • x + (1 - t) • y) := Real.exp_log hz

end Riesz2

end
