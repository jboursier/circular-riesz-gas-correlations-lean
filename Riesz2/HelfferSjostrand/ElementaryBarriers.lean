/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffinePolytopeDistance
public import Riesz2.ToMathlib.ConvexGradientBound
public import Riesz2.ToMathlib.RpowDomination
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic

/-!
# Elementary collision barriers

Two elementary estimates for the barriers of the collision analysis.

* The radial barrier estimate in Appendix A. For a bounded open convex polytope `Ω` with affine
  face coordinates `ℓ j` and a potential `V = ∑ a_j ℓ_j^(-s) + R`, the gradient satisfies
  `‖∇V‖ ≥ c δ^(-s-1) - C` with `δ = ⨅ j, ℓ j`. If `ΔV ≤ C₀ (1 + δ^(-s-2))`, then
  `A ‖∇V‖² - ΔV ≥ K d_∂^(-2) - C'` for all `A, K > 0`, where `d_∂` is the distance to `∂Ω`.
* The convexity of the exterior mass barrier in Appendix A. For `s > 0` and `m ≥ 1`, the function
  `y ↦ ∑ y_a^(-s) - (∑ y_a)^(-s)` is convex on the positive orthant of `ℝ^m`.

The affine space is modelled by the real inner product space `E` itself. The
gradient `∇V x` is `gradient V x`, the Riesz representative of `fderiv ℝ V x`, so
`‖∇V x‖ = ‖fderiv ℝ V x‖`. The Laplacian `ΔV x` is `Laplacian.laplacian V x`. The second estimate
uses the Laplacian only through its upper bound in the hypotheses.
-/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace Riesz2.ElementaryBarriers

section MassBarrier

/-- For nonnegative reals `y_a` with positive sum `L` and `p ≥ 1`, `∑ y_a ^ p ≤ L ^ p`. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} [Fintype ι] {y : ι → ℝ} (hy : ∀ a, 0 ≤ y a)
    {p : ℝ} (hp : 1 ≤ p) (hL : 0 < ∑ a, y a) :
    ∑ a, y a ^ p ≤ (∑ a, y a) ^ p := by
  have hyL : ∀ a, y a ≤ ∑ b, y b := fun a =>
    Finset.single_le_sum (fun b _ => hy b) (Finset.mem_univ a)
  have hterm : ∀ a, y a ^ p ≤ y a * (∑ b, y b) ^ (p - 1) := by
    intro a
    have hsplit : y a ^ p = y a * y a ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add' (hy a) (show (0 : ℝ) < 1 + (p - 1) by linarith).ne', Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hy a) (hyL a) (by linarith)) (hy a)
  calc ∑ a, y a ^ p ≤ ∑ a, y a * (∑ b, y b) ^ (p - 1) := Finset.sum_le_sum fun a _ => hterm a
    _ = (∑ a, y a) * (∑ b, y b) ^ (p - 1) := (Finset.sum_mul _ _ _).symm
    _ = (∑ a, y a) ^ p := by
      rw [Real.rpow_sub_one hL.ne']
      field_simp

/-- Weighted Cauchy–Schwarz inequality for the exterior mass barrier. For positive `y_a` with
sum `L`, the quantity `(∑ v_a)² L^(-s-2)` is at most `∑ v_a² y_a^(-s-2)`. -/
theorem sq_sum_mul_rpow_le {ι : Type*} [Fintype ι] {s : ℝ} (hs : 0 < s) {y v : ι → ℝ}
    (hy : ∀ a, 0 < y a) (hL : 0 < ∑ a, y a) :
    (∑ a, v a) ^ 2 * (∑ a, y a) ^ (-s - 1 - 1) ≤ ∑ a, v a ^ 2 * y a ^ (-s - 1 - 1) := by
  have hexp : ∀ z : ℝ, 0 < z → z ^ (-s - 1 - 1) = (z ^ (s + 2))⁻¹ := by
    intro z hz
    rw [show -s - 1 - 1 = -(s + 2) by ring, Real.rpow_neg hz.le]
  have hsum_eq : ∑ a, v a ^ 2 * y a ^ (-s - 1 - 1) = ∑ a, v a ^ 2 / y a ^ (s + 2) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hexp (y a) (hy a), div_eq_mul_inv]
  rw [hexp _ hL, hsum_eq]
  have hwpos : ∀ a, 0 < y a ^ (s + 2) := fun a => Real.rpow_pos_of_pos (hy a) _
  have hCS : (∑ a, v a) ^ 2 ≤ (∑ a, y a ^ (s + 2)) * ∑ a, v a ^ 2 / y a ^ (s + 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun a => Real.sqrt (y a ^ (s + 2))) (fun a => v a / Real.sqrt (y a ^ (s + 2)))
    have e1 : ∀ a, Real.sqrt (y a ^ (s + 2)) * (v a / Real.sqrt (y a ^ (s + 2))) = v a :=
      fun a => mul_div_cancel₀ _ (Real.sqrt_pos.2 (hwpos a)).ne'
    have e2 : ∀ a, Real.sqrt (y a ^ (s + 2)) ^ 2 = y a ^ (s + 2) :=
      fun a => Real.sq_sqrt (hwpos a).le
    have e3 : ∀ a, (v a / Real.sqrt (y a ^ (s + 2))) ^ 2 = v a ^ 2 / y a ^ (s + 2) :=
      fun a => by rw [div_pow, e2]
    simp only [e1, e2, e3] at h
    exact h
  have hsumw := sum_rpow_le_rpow_sum (fun a => (hy a).le) (by linarith : (1 : ℝ) ≤ s + 2) hL
  have hSnn : 0 ≤ ∑ a, v a ^ 2 / y a ^ (s + 2) :=
    Finset.sum_nonneg fun a _ => div_nonneg (sq_nonneg _) (hwpos a).le
  have hLp : 0 < (∑ a, y a) ^ (s + 2) := Real.rpow_pos_of_pos hL _
  calc (∑ a, v a) ^ 2 * ((∑ a, y a) ^ (s + 2))⁻¹
      ≤ ((∑ a, y a ^ (s + 2)) * ∑ a, v a ^ 2 / y a ^ (s + 2)) * ((∑ a, y a) ^ (s + 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hCS (inv_nonneg.2 hLp.le)
    _ ≤ ((∑ a, y a) ^ (s + 2) * ∑ a, v a ^ 2 / y a ^ (s + 2)) * ((∑ a, y a) ^ (s + 2))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsumw hSnn) (inv_nonneg.2 hLp.le)
    _ = ∑ a, v a ^ 2 / y a ^ (s + 2) := by
        field_simp

/-- A convex combination of two positive reals is positive. -/
theorem pos_of_convex_comb {p q a b : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < a * p + b * q := by
  have h1 := mul_le_mul_of_nonneg_left (min_le_left p q) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right p q) hb
  have h3 : a * min p q + b * min p q = min p q := by
    rw [← add_mul, hab, one_mul]
  have h4 : 0 < min p q := lt_min hp hq
  linarith

/-- On the segment from `x` to `z` in the positive orthant, the mass barrier is convex in the
segment parameter. -/
theorem convexOn_segment_mass {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) {x z : Fin m → ℝ}
    (hx : ∀ a, 0 < x a) (hz : ∀ a, 0 < z a) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ =>
      (∑ a, (x a + t * (z a - x a)) ^ (-s)) - (∑ a, (x a + t * (z a - x a))) ^ (-s)) := by
  -- Positivity of the points of the segment.
  have hYpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ a, 0 < x a + t * (z a - x a) := by
    rintro t ⟨ht0, ht1⟩ a
    have e : x a + t * (z a - x a) = (1 - t) * x a + t * z a := by ring
    rw [e]
    exact pos_of_convex_comb (hx a) (hz a) (sub_nonneg.2 ht1) ht0 (by ring)
  have hLpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < ∑ a, (x a + t * (z a - x a)) := fun t ht =>
    Finset.sum_pos (fun a _ => hYpos t ht a) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- Each `t ↦ x a + t (z a - x a)` is affine with derivative `z a - x a`.
  have hlin : ∀ a t, HasDerivAt (fun t : ℝ => x a + t * (z a - x a)) (z a - x a) t := by
    intro a t
    simpa using ((hasDerivAt_id t).mul_const (z a - x a)).const_add (x a)
  have hsumlin : ∀ t, HasDerivAt (fun t : ℝ => ∑ a, (x a + t * (z a - x a)))
      (∑ a, (z a - x a)) t := fun t =>
    HasDerivAt.fun_sum fun a _ => hlin a t
  -- First derivative of the barrier along the segment.
  have hg' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ =>
      (∑ a, (x a + t * (z a - x a)) ^ (-s)) - (∑ a, (x a + t * (z a - x a))) ^ (-s))
      ((∑ a, (z a - x a) * (-s) * (x a + t * (z a - x a)) ^ (-s - 1)) -
        (∑ a, (z a - x a)) * (-s) * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => ∑ a, (x a + t * (z a - x a)) ^ (-s))
        (∑ a, (z a - x a) * (-s) * (x a + t * (z a - x a)) ^ (-s - 1)) t :=
      HasDerivAt.fun_sum fun a _ =>
        (hlin a t).rpow_const (Or.inl (hYpos t ht a).ne')
    have h2 : HasDerivAt (fun t : ℝ => (∑ a, (x a + t * (z a - x a))) ^ (-s))
        ((∑ a, (z a - x a)) * (-s) * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1)) t :=
      (hsumlin t).rpow_const (Or.inl (hLpos t ht).ne')
    exact h1.sub h2
  -- Second derivative of the barrier along the segment.
  have hg'' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ =>
      (∑ a, (z a - x a) * (-s) * (x a + t * (z a - x a)) ^ (-s - 1)) -
        (∑ a, (z a - x a)) * (-s) * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1))
      ((∑ a, (z a - x a) * (-s) * ((z a - x a) * (-s - 1) *
          (x a + t * (z a - x a)) ^ (-s - 1 - 1))) -
        (∑ a, (z a - x a)) * (-s) * ((∑ a, (z a - x a)) * (-s - 1) *
          (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1))) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => ∑ a, (z a - x a) * (-s) * (x a + t * (z a - x a)) ^ (-s - 1))
        (∑ a, (z a - x a) * (-s) * ((z a - x a) * (-s - 1) *
          (x a + t * (z a - x a)) ^ (-s - 1 - 1))) t :=
      HasDerivAt.fun_sum fun a _ =>
        (((hlin a t).rpow_const (p := -s - 1) (Or.inl (hYpos t ht a).ne')).const_mul
          ((z a - x a) * (-s)))
    have h2 : HasDerivAt (fun t : ℝ =>
        (∑ a, (z a - x a)) * (-s) * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1))
        ((∑ a, (z a - x a)) * (-s) * ((∑ a, (z a - x a)) * (-s - 1) *
          (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1))) t :=
      ((hsumlin t).rpow_const (p := -s - 1) (Or.inl (hLpos t ht).ne')).const_mul
        ((∑ a, (z a - x a)) * (-s))
    exact h1.sub h2
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
    (f' := fun t : ℝ => (∑ a, (z a - x a) * (-s) * (x a + t * (z a - x a)) ^ (-s - 1)) -
        (∑ a, (z a - x a)) * (-s) * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1))
    (f'' := fun t : ℝ => (∑ a, (z a - x a) * (-s) * ((z a - x a) * (-s - 1) *
          (x a + t * (z a - x a)) ^ (-s - 1 - 1))) -
        (∑ a, (z a - x a)) * (-s) * ((∑ a, (z a - x a)) * (-s - 1) *
          (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1)))
    (fun t ht => (hg' t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (hg'' t (interior_subset ht)).hasDerivWithinAt) ?_
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
  have hk : (∑ a, (z a - x a)) ^ 2 * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1) ≤
      ∑ a, (z a - x a) ^ 2 * (x a + t * (z a - x a)) ^ (-s - 1 - 1) :=
    sq_sum_mul_rpow_le (v := fun a => z a - x a) hs (fun a => hYpos t ht' a) (hLpos t ht')
  have hc : 0 ≤ (-s) * (-s - 1) := by nlinarith
  have e1 : (∑ a, (z a - x a) * (-s) * ((z a - x a) * (-s - 1) *
      (x a + t * (z a - x a)) ^ (-s - 1 - 1))) =
      (-s) * (-s - 1) * ∑ a, (z a - x a) ^ 2 * (x a + t * (z a - x a)) ^ (-s - 1 - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hbr : 0 ≤ (∑ a, (z a - x a) ^ 2 * (x a + t * (z a - x a)) ^ (-s - 1 - 1)) -
      (∑ a, (z a - x a)) ^ 2 * (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1) := by
    linarith
  show 0 ≤ (∑ a, (z a - x a) * (-s) * ((z a - x a) * (-s - 1) *
      (x a + t * (z a - x a)) ^ (-s - 1 - 1))) -
        (∑ a, (z a - x a)) * (-s) * ((∑ a, (z a - x a)) * (-s - 1) *
          (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1))
  rw [e1]
  have e2 : (∑ a, (z a - x a)) * (-s) * ((∑ a, (z a - x a)) * (-s - 1) *
      (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1)) =
      (-s) * (-s - 1) * ((∑ a, (z a - x a)) ^ 2 *
        (∑ a, (x a + t * (z a - x a))) ^ (-s - 1 - 1)) := by
    ring
  rw [e2, ← mul_sub]
  exact mul_nonneg hc hbr

/-- The exterior mass-barrier convexity used in Appendix A. For `m ≥ 1` and `s > 0`, the exterior mass barrier
`y ↦ ∑ y_a ^ (-s) - (∑ y_a) ^ (-s)` is convex on the positive orthant of `ℝ^m`. -/
theorem convexOn_exterior_mass_barrier {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ {y : Fin m → ℝ | ∀ a, 0 < y a}
      (fun y => (∑ a, y a ^ (-s)) - (∑ a, y a) ^ (-s)) := by
  have hconv : Convex ℝ {y : Fin m → ℝ | ∀ a, 0 < y a} := by
    intro x hx y hy a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact pos_of_convex_comb (hx i) (hy i) ha hb hab
  refine ⟨hconv, fun x hx z hz a b ha hb hab => ?_⟩
  have hseg := convexOn_segment_mass hm hs hx hz
  have hxz : a • x + b • z = x + b • (z - x) := by
    rw [show a = 1 - b by linarith]
    module
  have key := hseg.2 (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ ha hb hab
  simp only [smul_eq_mul, mul_one, mul_zero, zero_add, zero_mul, add_zero, one_mul,
    add_sub_cancel] at key
  rw [hxz]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simpa only [smul_eq_mul, mul_sub, add_sub_cancel] using key

end MassBarrier

section RadialBarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The linear part of an affine function, as a continuous linear functional, takes differences
to differences. -/
theorem linear_sub_eq (ℓ : E →ᵃ[ℝ] ℝ) (x y : E) :
    (LinearMap.toContinuousLinearMap ℓ.linear) (x - y) = ℓ x - ℓ y := by
  have h := AffineMap.linear_apply_vsub ℓ x y
  simp only [vsub_eq_sub] at h
  exact h

/-- The derivative of `y ↦ ∑ a_j ℓ_j(y)^(-s) + R(y)` at `x`, applied to a vector `w`. -/
theorem fderiv_potential_apply {ι : Type*} [Fintype ι] {ℓ : ι → E →ᵃ[ℝ] ℝ} {a : ι → ℝ} {s : ℝ}
    {R : E → ℝ} {x : E} (hpos : ∀ j, ℓ j x ≠ 0) (hR : DifferentiableAt ℝ R x) (w : E) :
    fderiv ℝ (fun y => ∑ j, a j * ℓ j y ^ (-s) + R y) x w =
      ∑ j, (a j * (-s) * ℓ j x ^ (-s - 1)) *
        (LinearMap.toContinuousLinearMap (ℓ j).linear w) + fderiv ℝ R x w := by
  have hL : ∀ j, HasFDerivAt (fun y => ℓ j y)
      (LinearMap.toContinuousLinearMap (ℓ j).linear) x := by
    intro j
    have hfun : (fun y => ℓ j y) =
        fun y => (LinearMap.toContinuousLinearMap (ℓ j).linear) y + ℓ j 0 := by
      funext y
      have h := congrFun (AffineMap.decomp (ℓ j)) y
      simpa using h
    rw [hfun]
    exact (LinearMap.toContinuousLinearMap (ℓ j).linear).hasFDerivAt.add_const _
  have hpow : ∀ j, HasFDerivAt (fun y => a j * ℓ j y ^ (-s))
      ((a j * (-s) * ℓ j x ^ (-s - 1)) • LinearMap.toContinuousLinearMap (ℓ j).linear) x := by
    intro j
    have h := (((hL j).rpow_const (p := -s) (Or.inl (hpos j))).const_mul (a j))
    convert h using 1
    rw [smul_smul, mul_assoc]
  have htot : HasFDerivAt (fun y => ∑ j, a j * ℓ j y ^ (-s) + R y)
      (∑ j, (a j * (-s) * ℓ j x ^ (-s - 1)) • LinearMap.toContinuousLinearMap (ℓ j).linear +
        fderiv ℝ R x) x :=
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hpow j)).add hR.hasFDerivAt
  rw [htot.fderiv]
  simp

/-- One term of the radial derivative is bounded below by a constant. For positive `p = ℓ_j x₀`
and `q = ℓ_j x`, the product `s a q^(-s-1) (p - q)` is at least `-s a (p/2)^(-s)`. -/
theorem term_lower_bound {s a p q : ℝ} (hs : 0 < s) (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) :
    -(s * a * (p / 2) ^ (-s)) ≤ s * a * q ^ (-s - 1) * (p - q) := by
  rcases le_or_gt q (p / 2) with hle | hgt
  · have h1 : 0 ≤ s * a * q ^ (-s - 1) := by positivity
    have h2 : 0 ≤ s * a * (p / 2) ^ (-s) := by positivity
    have h3 : 0 ≤ s * a * q ^ (-s - 1) * (p - q) := mul_nonneg h1 (by linarith)
    linarith
  · have hqq : q ^ (-s) = q ^ (-s - 1) * q := by
      rw [← Real.rpow_add_one hq.ne']
      congr 1
      ring
    have hpow : q ^ (-s) ≤ (p / 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hgt.le (by linarith)
    have h1 : s * a * (q ^ (-s - 1) * (-q)) ≤ s * a * (q ^ (-s - 1) * (p - q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith)
        (Real.rpow_nonneg hq.le _)) (by positivity)
    have h2 : s * a * (q ^ (-s - 1) * (-q)) = -(s * a * q ^ (-s)) := by
      rw [hqq]
      ring
    have h3 : s * a * q ^ (-s) ≤ s * a * (p / 2) ^ (-s) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h4 : s * a * q ^ (-s - 1) * (p - q) = s * a * (q ^ (-s - 1) * (p - q)) := by ring
    rw [h4]
    linarith

/-- A pure square inequality: if `a - b ≤ p` with `a ≥ 0` and `p ≥ 0`, then `a²/2 - b² ≤ p²`. -/
theorem sq_half_sub_le_sq {p a b : ℝ} (ha : 0 ≤ a) (h : a - b ≤ p) :
    a ^ 2 / 2 - b ^ 2 ≤ p ^ 2 := by
  rcases le_or_gt b a with hab | hab
  · have h2 : 0 ≤ a - b := by linarith
    have h3 : (a - b) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ h2 h 2
    nlinarith [sq_nonneg (a - 2 * b)]
  · have h1 : a ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [sq_nonneg p, sq_nonneg b]

/-- For a finite nonempty index type, the infimum of `f` is attained at some index. -/
theorem exists_iInf_eq_apply {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) :
    ∃ j, (⨅ i, f i) = f j := by
  obtain ⟨j, hj⟩ := Finite.exists_min f
  exact ⟨j, le_antisymm (ciInf_le (Finite.bddBelow_range f) j) (le_ciInf hj)⟩

omit [FiniteDimensional ℝ E] in
/-- A bounded set of the form `{x | ∀ j, 0 < ℓ j x}` on a nontrivial space has a nonempty index
type. -/
theorem nonempty_index [Nontrivial E] {ι : Type*} [Fintype ι] (ℓ : ι → E →ᵃ[ℝ] ℝ) {Ω : Set E}
    (hΩ : Ω = {x : E | ∀ j, 0 < ℓ j x}) (hb : Bornology.IsBounded Ω) : Nonempty ι := by
  by_contra hι
  rw [not_nonempty_iff] at hι
  have huniv : Ω = Set.univ := by
    rw [hΩ]
    ext y
    simp
  exact NormedSpace.unbounded_univ ℝ E (huniv ▸ hb)

omit [FiniteDimensional ℝ E] in
/-- The derivative of a convex function at `x` is bounded below on a bounded set, relative to
its value at a base point `x₀`. -/
theorem convex_fderiv_sub_lower {Ω : Set E} {R : E → ℝ} (hRc : ConvexOn ℝ Ω R) {x x₀ : E}
    (hx : x ∈ Ω) (hx₀ : x₀ ∈ Ω) (hdx : DifferentiableAt ℝ R x) (hdx₀ : DifferentiableAt ℝ R x₀)
    {D : ℝ} (hD : ‖x - x₀‖ ≤ D) :
    -(‖fderiv ℝ R x₀‖ * D) ≤ fderiv ℝ R x (x - x₀) := by
  have h1 := ConvexGradient.fderiv_apply_sub_le_sub hRc hx hx₀ hdx
  have h2 := ConvexGradient.fderiv_apply_sub_le_sub hRc hx₀ hx hdx₀
  have h3 : fderiv ℝ R x (x - x₀) = -fderiv ℝ R x (x₀ - x) := by
    rw [← map_neg, neg_sub]
  have h4 := (fderiv ℝ R x₀).le_opNorm (x - x₀)
  rw [Real.norm_eq_abs] at h4
  have h5 := neg_abs_le (fderiv ℝ R x₀ (x - x₀))
  have h6 : ‖fderiv ℝ R x₀‖ * ‖x - x₀‖ ≤ ‖fderiv ℝ R x₀‖ * D :=
    mul_le_mul_of_nonneg_left hD (norm_nonneg _)
  linarith

/-- The gradient estimate in Appendix A. For the potential `V = ∑ a_j ℓ_j^(-s) + R` on the
bounded polytope `Ω = {x | ∀ j, 0 < ℓ j x}`, there are `c, C > 0` such that
`‖∇V‖ ≥ c δ^(-s-1) - C` on `Ω`, where `δ = ⨅ j, ℓ j` is the smallest face coordinate. -/
theorem radial_gradient_lower [Nontrivial E] {ι : Type*} [Fintype ι] (ℓ : ι → E →ᵃ[ℝ] ℝ)
    (a : ι → ℝ) (ha : ∀ j, 0 < a j) {s : ℝ} (hs : 0 < s) {Ω : Set E}
    (hΩ : Ω = {x : E | ∀ j, 0 < ℓ j x}) (hb : Bornology.IsBounded Ω)
    (R : E → ℝ) (hRc : ConvexOn ℝ Ω R) (hRs : ContDiffOn ℝ ∞ R Ω)
    (V : E → ℝ) (hV : ∀ x ∈ Ω, V x = ∑ j, a j * ℓ j x ^ (-s) + R x) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Ω, c * (⨅ j, ℓ j x) ^ (-s - 1) - C ≤ ‖gradient V x‖ := by
  have hΩopen : IsOpen Ω := hΩ ▸ AffinePolytope.isOpen_polytope ℓ
  have hpos : ∀ x ∈ Ω, ∀ j, 0 < ℓ j x := fun x hx j => by
    rw [hΩ] at hx
    exact hx j
  have hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ R x := fun x hx =>
    (hRs.contDiffAt (hΩopen.mem_nhds hx)).differentiableAt (by simp)
  rcases Set.eq_empty_or_nonempty Ω with hemp | ⟨x₀, hx₀⟩
  · exact ⟨1, 1, one_pos, one_pos, fun x hx => by simp [hemp] at hx⟩
  have := nonempty_index ℓ hΩ hb
  -- Constants depending only on the data and the base point `x₀`.
  obtain ⟨jμ, hjμ⟩ := Finite.exists_min (fun j => ℓ j x₀)
  obtain ⟨ja, hja⟩ := Finite.exists_min a
  obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max r 1 := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hDdef]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD : ∀ x ∈ Ω, ‖x - x₀‖ ≤ D := fun x hx => by
    have h1 : dist x x₀ ≤ r := Metric.mem_closedBall.1 (hr hx)
    rw [dist_eq_norm] at h1
    rw [hDdef]
    exact h1.trans (le_max_left _ _)
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = ℓ jμ x₀ := ⟨_, rfl⟩
  have hμpos : 0 < μ := by
    rw [hμdef]
    exact hpos x₀ hx₀ jμ
  have hμle : ∀ j, μ ≤ ℓ j x₀ := fun j => by
    rw [hμdef]
    exact hjμ j
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = s * a ja * (μ / 2) := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    have := ha ja
    positivity
  obtain ⟨Esum, hEsum⟩ : ∃ e : ℝ, e = ∑ j, s * a j * (ℓ j x₀ / 2) ^ (-s) := ⟨_, rfl⟩
  have hEnn : 0 ≤ Esum := by
    rw [hEsum]
    refine Finset.sum_nonneg fun j _ => ?_
    have := ha j
    have := hpos x₀ hx₀ j
    positivity
  obtain ⟨MR, hMRdef⟩ : ∃ m : ℝ, m = ‖fderiv ℝ R x₀‖ * D := ⟨_, rfl⟩
  have hMRnn : 0 ≤ MR := by
    rw [hMRdef]
    positivity
  obtain ⟨C₂, hC₂def⟩ : ∃ C₂ : ℝ, C₂ = Esum + MR + c₀ * (μ / 2) ^ (-s - 1) := ⟨_, rfl⟩
  have hcpow : 0 ≤ c₀ * (μ / 2) ^ (-s - 1) := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ μ / 2) (-s - 1)
    have := hc₀pos.le
    positivity
  refine ⟨c₀ / D, |C₂| / D + 1, by positivity, by positivity, fun x hx => ?_⟩
  -- The face attaining the infimum at `x`.
  have hjx : ∃ jx, (⨅ j, ℓ j x) = ℓ jx x := exists_iInf_eq_apply (fun j => ℓ j x)
  obtain ⟨jx, hjx⟩ := hjx
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ℓ jx x := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact hpos x hx jx
  rw [hjx, ← hδdef]
  -- The derivative of `V` at `x` applied to `x - x₀`.
  have hVF : V =ᶠ[nhds x] (fun y => ∑ j, a j * ℓ j y ^ (-s) + R y) :=
    Filter.eventually_of_mem (hΩopen.mem_nhds hx) hV
  have hfd : fderiv ℝ V x (x - x₀) =
      ∑ j, (a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) + fderiv ℝ R x (x - x₀) := by
    rw [hVF.fderiv_eq, fderiv_potential_apply (fun j => (hpos x hx j).ne') (hdiff x hx) (x - x₀)]
    simp only [linear_sub_eq]
  -- Each term is bounded below by a constant.
  have hTE : ∀ j, 0 ≤ (a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) +
      s * a j * (ℓ j x₀ / 2) ^ (-s) := by
    intro j
    have h := term_lower_bound hs (ha j) (hpos x₀ hx₀ j) (hpos x hx j)
    have e : (a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) =
        s * a j * ℓ j x ^ (-s - 1) * (ℓ j x₀ - ℓ j x) := by ring
    rw [e]
    linarith
  have hS1 : -Esum ≤ ∑ j, (a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hTE j)
    rw [Finset.sum_add_distrib, Finset.sum_const_zero] at h
    rw [hEsum]
    linarith
  have hS2 : (a jx * (-s) * ℓ jx x ^ (-s - 1)) * (ℓ jx x - ℓ jx x₀) - Esum ≤
      ∑ j, (a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) := by
    have h1 := Finset.single_le_sum (f := fun j => (a j * (-s) * ℓ j x ^ (-s - 1)) *
      (ℓ j x - ℓ j x₀) + s * a j * (ℓ j x₀ / 2) ^ (-s)) (fun j _ => hTE j)
      (Finset.mem_univ jx)
    have h2 : ∑ j, ((a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) +
        s * a j * (ℓ j x₀ / 2) ^ (-s)) =
        ∑ j, (a j * (-s) * ℓ j x ^ (-s - 1)) * (ℓ j x - ℓ j x₀) + Esum := by
      rw [Finset.sum_add_distrib, hEsum]
    have h3 : 0 ≤ s * a jx * (ℓ jx x₀ / 2) ^ (-s) := by
      have := ha jx
      have := hpos x₀ hx₀ jx
      positivity
    beta_reduce at h1
    linarith
  -- When `δ` is small, the minimal face carries the main term.
  have hTmin : δ ≤ μ / 2 → c₀ * δ ^ (-s - 1) ≤
      (a jx * (-s) * ℓ jx x ^ (-s - 1)) * (ℓ jx x - ℓ jx x₀) := by
    intro hδμ
    rw [← hδdef]
    have hδpow : 0 < δ ^ (-s - 1) := Real.rpow_pos_of_pos hδpos _
    have h1 : μ / 2 ≤ ℓ jx x₀ - δ := by linarith [hμle jx]
    have h2 : a ja ≤ a jx := hja jx
    have hk : s * a ja * δ ^ (-s - 1) ≤ s * a jx * δ ^ (-s - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hs.le) hδpow.le
    calc c₀ * δ ^ (-s - 1) = (s * a ja * δ ^ (-s - 1)) * (μ / 2) := by rw [hc₀def]; ring
      _ ≤ (s * a jx * δ ^ (-s - 1)) * (μ / 2) :=
          mul_le_mul_of_nonneg_right hk (by positivity)
      _ ≤ (s * a jx * δ ^ (-s - 1)) * (ℓ jx x₀ - δ) :=
          mul_le_mul_of_nonneg_left h1 (by have := ha jx; positivity)
      _ = (a jx * (-s) * δ ^ (-s - 1)) * (δ - ℓ jx x₀) := by ring
  have hR := convex_fderiv_sub_lower hRc hx hx₀ (hdiff x hx) (hdiff x₀ hx₀) (hD x hx)
  rw [← hMRdef] at hR
  -- Lower bound for the derivative of `V` along `x - x₀`.
  have hbig : c₀ * δ ^ (-s - 1) - C₂ ≤ fderiv ℝ V x (x - x₀) := by
    rw [hfd]
    by_cases hδμ : δ ≤ μ / 2
    · have h1 := hTmin hδμ
      rw [hC₂def]
      linarith
    · rw [not_le] at hδμ
      have hpow : δ ^ (-s - 1) ≤ (μ / 2) ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hδμ.le (by linarith)
      have h1 : c₀ * δ ^ (-s - 1) ≤ c₀ * (μ / 2) ^ (-s - 1) :=
        mul_le_mul_of_nonneg_left hpow hc₀pos.le
      rw [hC₂def]
      linarith
  -- Pass from the derivative to the gradient norm.
  have hgnorm : ‖gradient V x‖ = ‖fderiv ℝ V x‖ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
  have hop : fderiv ℝ V x (x - x₀) ≤ ‖fderiv ℝ V x‖ * D := by
    have h1 := (fderiv ℝ V x).le_opNorm (x - x₀)
    have h2 : ‖fderiv ℝ V x‖ * ‖x - x₀‖ ≤ ‖fderiv ℝ V x‖ * D :=
      mul_le_mul_of_nonneg_left (hD x hx) (norm_nonneg _)
    have h3 := Real.le_norm_self (fderiv ℝ V x (x - x₀))
    linarith
  have hfinal : c₀ * δ ^ (-s - 1) - C₂ ≤ ‖fderiv ℝ V x‖ * D := le_trans hbig hop
  rw [hgnorm]
  have e : c₀ / D * δ ^ (-s - 1) - (|C₂| / D + 1) = (c₀ * δ ^ (-s - 1) - (|C₂| + D)) / D := by
    field_simp
  rw [e, div_le_iff₀ hDpos]
  linarith [le_abs_self C₂]

/-- The Laplacian estimate in Appendix A. If `ΔV ≤ C₀ (1 + δ^(-s-2))` on `Ω`, then for all
`A, K > 0` there is `C` with `A ‖∇V‖² - ΔV ≥ K d_∂^(-2) - C` on `Ω`, where `d_∂` is the distance
from `x` to the frontier of `Ω`. -/
theorem radial_laplacian_lower [Nontrivial E] {ι : Type*} [Fintype ι] (ℓ : ι → E →ᵃ[ℝ] ℝ)
    (a : ι → ℝ) (ha : ∀ j, 0 < a j) {s : ℝ} (hs : 0 < s) {Ω : Set E}
    (hΩ : Ω = {x : E | ∀ j, 0 < ℓ j x}) (hb : Bornology.IsBounded Ω)
    (R : E → ℝ) (hRc : ConvexOn ℝ Ω R) (hRs : ContDiffOn ℝ ∞ R Ω)
    (V : E → ℝ) (hV : ∀ x ∈ Ω, V x = ∑ j, a j * ℓ j x ^ (-s) + R x) (C₀ : ℝ)
    (hΔ : ∀ x ∈ Ω, Laplacian.laplacian V x ≤ C₀ * (1 + (⨅ j, ℓ j x) ^ (-s - 2))) :
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ C : ℝ, ∀ x ∈ Ω,
      K * (Metric.infDist x (frontier Ω) ^ 2)⁻¹ - C ≤
        A * ‖gradient V x‖ ^ 2 - Laplacian.laplacian V x := by
  intro A K hA hK
  obtain ⟨c, C, hc, hC, hgrad⟩ := radial_gradient_lower ℓ a ha hs hΩ hb R hRc hRs V hV
  obtain ⟨G, hG, hlip⟩ := AffinePolytope.exists_lipschitz ℓ
  obtain ⟨Cd, hCd⟩ := RpowDomination.exists_bound (s := s) (α := A * c ^ 2 / 2)
    (β := max C₀ 0) (γ := K * G ^ 2) hs (by positivity) (le_max_right _ _) (by positivity)
  refine ⟨A * C ^ 2 + Cd, fun x hx => ?_⟩
  have := nonempty_index ℓ hΩ hb
  have hpos : ∀ j, 0 < ℓ j x := by
    have hx' := hx
    rw [hΩ] at hx'
    exact hx'
  -- The infimum of the faces at `x`, attained at some face `jx`.
  obtain ⟨jx, hjx⟩ : ∃ jx, (⨅ j, ℓ j x) = ℓ jx x := exists_iInf_eq_apply (fun j => ℓ j x)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ℓ jx x := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact hpos jx
  have hδ0 : (⨅ j, ℓ j x) = δ := by rw [hjx, hδdef]
  have hgrad' := hgrad x hx
  rw [hδ0] at hgrad'
  have hΔx := hΔ x hx
  rw [hδ0] at hΔx
  have hd := AffinePolytope.div_le_infDist_frontier ℓ hΩ hb hG hlip hx
  rw [hδ0] at hd
  -- The gradient term, squared.
  have hsq : (c * δ ^ (-s - 1)) ^ 2 / 2 - C ^ 2 ≤ ‖gradient V x‖ ^ 2 :=
    sq_half_sub_le_sq (p := ‖gradient V x‖) (a := c * δ ^ (-s - 1)) (b := C)
      (by positivity) (by linarith)
  have hA2 : A * ((c * δ ^ (-s - 1)) ^ 2 / 2 - C ^ 2) ≤ A * ‖gradient V x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hA.le
  -- The distance term.
  have hdpos : 0 < δ / G := div_pos hδpos hG
  have hdsq : (δ / G) ^ 2 ≤ Metric.infDist x (frontier Ω) ^ 2 := pow_le_pow_left₀ hdpos.le hd 2
  have hinv : (Metric.infDist x (frontier Ω) ^ 2)⁻¹ ≤ G ^ 2 * (δ ^ 2)⁻¹ := by
    have h1 := inv_anti₀ (pow_pos hdpos 2) hdsq
    have e : ((δ / G) ^ 2)⁻¹ = G ^ 2 * (δ ^ 2)⁻¹ := by
      field_simp
    rw [e] at h1
    exact h1
  have hKinv : K * (Metric.infDist x (frontier Ω) ^ 2)⁻¹ ≤ K * (G ^ 2 * (δ ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv hK.le
  -- The Laplacian term.
  have hΔ' : Laplacian.laplacian V x ≤ max C₀ 0 * (1 + δ ^ (-s - 2)) := by
    refine le_trans hΔx (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) ?_)
    have := Real.rpow_nonneg hδpos.le (-s - 2)
    linarith
  -- Absorb the Laplacian and distance terms into the gradient term.
  have hdom := hCd δ hδpos
  have hKG : K * (G ^ 2 * (δ ^ 2)⁻¹) = K * G ^ 2 * (δ ^ 2)⁻¹ := by ring
  have hA2' : A * ((c * δ ^ (-s - 1)) ^ 2 / 2) = A * c ^ 2 / 2 * (δ ^ (-s - 1)) ^ 2 := by ring
  linarith

end RadialBarrier

end Riesz2.ElementaryBarriers

end
