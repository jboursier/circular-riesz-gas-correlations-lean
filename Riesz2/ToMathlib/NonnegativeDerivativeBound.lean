/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-!
# A local derivative bound for nonnegative functions

This is scalar infrastructure for the integrability step in Lemma 3.5. The correction `M t²/2 - f(t)` is convex, so
its tangent at zero gives a quadratic upper bound on `f`. Nonnegativity
of `f` then controls its squared first derivative. These estimates do
not assert an integration or smoothness theorem for marginal potentials.
-/

public section

open Set

namespace Riesz2

/-- Algebraic form of the local derivative bound: a nonnegative quadratic
majorant on a symmetric interval controls its linear coefficient. -/
theorem derivative_sq_le_of_nonnegative_quadratic {f p M r : ℝ}
    (hf : 0 ≤ f) (hM : 0 ≤ M) (hr : 0 < r)
    (hb : ∀ t : ℝ, |t| ≤ r → 0 ≤ f + p * t + M / 2 * t ^ 2) :
    p ^ 2 ≤ 2 * (M + |p| / r) * f := by
  by_cases hp : p = 0
  · subst p
    simp only [abs_zero, zero_div, add_zero]
    nlinarith [mul_nonneg hM hf]
  let K := M + |p| / r
  have hK : 0 < K := add_pos_of_nonneg_of_pos hM (div_pos (abs_pos.mpr hp) hr)
  have ht : |-p / K| ≤ r := by
    rw [abs_div, abs_neg, abs_of_pos hK, div_le_iff₀ hK]
    dsimp [K]
    nlinarith [div_mul_cancel₀ |p| hr.ne']
  have h := hb (-p / K) ht
  have hscaled := mul_nonneg h (sq_nonneg K)
  have he : (f + p * (-p / K) + M / 2 * (-p / K) ^ 2) * K ^ 2 =
      f * K ^ 2 - p ^ 2 * K + M / 2 * p ^ 2 := by
    field_simp
    ring
  rw [he] at hscaled
  have hMK : M ≤ K := le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hr.le)
  have hhalf : 0 ≤ K * (2 * K * f - p ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMK) (sq_nonneg p)]
  have := (nonneg_of_mul_nonneg_right hhalf hK)
  exact (sub_nonneg.mp this)

/-- A nonnegative twice differentiable function on `[-r,r]` satisfies a
local derivative bound using only an upper bound on its second derivative.
No continuity of the second derivative is required. This supplies the scalar
estimate needed for force-square integrability in Lemma 3.5. -/
theorem derivative_sq_le_of_nonnegative_on_interval {f g h : ℝ → ℝ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hn : ∀ t ∈ Icc (-r) r, 0 ≤ f t)
    (hd : ∀ t ∈ Icc (-r) r, HasDerivAt f (g t) t)
    (hdd : ∀ t ∈ Icc (-r) r, HasDerivAt g (h t) t)
    (hb : ∀ t ∈ Icc (-r) r, h t ≤ M) :
    g 0 ^ 2 ≤ 2 * (M + |g 0| / r) * f 0 := by
  let q := fun t => M / 2 * t ^ 2 - f t
  let q' := fun t => M * t - g t
  have hq (t) (ht : t ∈ Icc (-r) r) : HasDerivAt q (q' t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (M / 2)).fun_sub (hd t ht) using 1
    all_goals dsimp [q', id]
    ring
  have hq' (t) (ht : t ∈ Icc (-r) r) :
      HasDerivAt q' (M - h t) t := by
    simpa [q'] using ((hasDerivAt_id t).const_mul M).fun_sub (hdd t ht)
  have hc : ConvexOn ℝ (Icc (-r) r) q :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hq' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => sub_nonneg.mpr (hb t (interior_subset ht)))
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  apply derivative_sq_le_of_nonnegative_quadratic (hn 0 h0) hM hr
  intro t ht
  have htr : t ∈ Icc (-r) r := abs_le.mp ht
  rcases lt_trichotomy t 0 with ht0 | rfl | ht0
  · have hi := hc.slope_le_of_hasDerivAt htr h0 ht0 (hq 0 h0)
    rw [slope_def_field] at hi
    have := (div_le_iff₀ (sub_pos.mpr ht0)).mp hi
    dsimp [q, q'] at this
    nlinarith [hn t htr]
  · simpa using hn 0 h0
  · have hi := hc.le_slope_of_hasDerivAt h0 htr ht0 (hq 0 h0)
    rw [slope_def_field] at hi
    have := (le_div_iff₀ (sub_pos.mpr ht0)).mp hi
    dsimp [q, q'] at this
    nlinarith [hn t htr]

end Riesz2
