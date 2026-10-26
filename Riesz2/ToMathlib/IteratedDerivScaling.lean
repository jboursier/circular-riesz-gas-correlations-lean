/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Iterated derivatives under a scalar change of variable

The formula includes functions that need not be differentiable everywhere.
-/

public section

namespace Riesz2

/-- Scaling the variable multiplies the `n`th derivative by the `n`th power.
No global smoothness assumption is needed. -/
theorem iteratedDeriv_scale {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (f : 𝕜 → 𝕜) (c : 𝕜) (n : ℕ) :
    iteratedDeriv n (fun x => f (c * x)) =
      fun x => c ^ n * iteratedDeriv n f (c * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul,
      iteratedDeriv_succ, pow_succ]
    ring

end Riesz2
