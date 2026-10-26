/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

/-!
# Bounds for periodized real powers

The distance from both endpoints of a period controls the entire image sum.
The constants depend only on the power, and the period can be any positive real.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Riesz2.PeriodicPower

/-- A summable majorant depending only on the exponent. -/
def bound (p : ℝ) (_hp : 1 < p) : ℝ :=
  1 + 2 ^ p * ∑' k : {k : ℤ // k ≠ 0}, |(k.val : ℝ)| ^ (-p)

private theorem bound_eq (p : ℝ) (hp : 1 < p) :
    bound p hp = 1 + 2 ^ p * ∑' k : ℤ, |(k : ℝ)| ^ (-p) := by
  have he := tsum_subtype_eq_of_support_subset
    (f := fun k : ℤ => |(k : ℝ)| ^ (-p)) (s := {k : ℤ | k ≠ 0}) (by
      intro k hk hk0
      subst k
      change |((0 : ℤ) : ℝ)| ^ (-p) ≠ 0 at hk
      exact hk (by simp only [Int.cast_zero, abs_zero,
        Real.zero_rpow (by linarith : -p ≠ 0)]))
  exact congrArg (fun t : ℝ => 1 + 2 ^ p * t) he

theorem bound_pos (p : ℝ) (hp : 1 < p) : 0 < bound p hp := by
  have hS : 0 ≤ ∑' k : {k : ℤ // k ≠ 0}, |(k.val : ℝ)| ^ (-p) :=
    tsum_nonneg (fun k => Real.rpow_nonneg (abs_nonneg (k.val : ℝ)) (-p))
  have htwo := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p
  unfold bound
  positivity

private theorem image_distance {N x δ : ℝ} (hδ : 0 < δ)
    (hx : δ ≤ x) (hxN : δ ≤ N - x) (k : ℤ) (hk : k ≠ 0) :
    δ / 2 * |(k : ℝ)| ≤ |x + k * N| := by
  have hN : 2 * δ ≤ N := by linarith
  have hx0 : 0 ≤ x := le_trans hδ.le hx
  have hN0 : 0 ≤ N := by linarith
  rcases le_total (0 : ℤ) k with hpos | hneg
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    rw [abs_of_nonneg (by positivity : 0 ≤ (k : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ x + (k : ℝ) * N)]
    nlinarith
  · have hkR : (1 : ℝ) ≤ -(k : ℝ) := by exact_mod_cast (show 1 ≤ -k by omega)
    have hm : 0 ≤ -(k : ℝ) - 1 := by linarith
    have hprod := mul_nonneg hm (show 0 ≤ N - 2 * δ by linarith)
    rw [abs_of_nonpos (by exact_mod_cast hneg),
      abs_of_nonpos (by nlinarith : x + (k : ℝ) * N ≤ 0)]
    nlinarith

/-- Summability and an explicit bound when both nearest images are at distance `δ`.
The two endpoint inequalities exclude every collision, so the series has its actual value. -/
theorem summable_and_le {p N x δ : ℝ} (hp : 1 < p) (hδ : 0 < δ)
    (hx : δ ≤ x) (hxN : δ ≤ N - x) :
    Summable (fun k : ℤ => |x + k * N| ^ (-p)) ∧
      (∑' k : ℤ, |x + k * N| ^ (-p)) ≤ bound p hp * δ ^ (-p) := by
  have hp0 : 0 < p := by linarith
  have hS : Summable (fun k : ℤ => |(k : ℝ)| ^ (-p)) :=
    Real.summable_abs_int_rpow hp
  let M : ℤ → ℝ := fun k =>
    δ ^ (-p) * ((if k = 0 then 1 else 0) + 2 ^ p * |(k : ℝ)| ^ (-p))
  have hM : Summable M :=
    ((hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable.add (hS.mul_left _)).mul_left _
  have hle (k : ℤ) : |x + k * N| ^ (-p) ≤ M k := by
    by_cases hk : k = 0
    · subst k
      simp only [zero_mul, add_zero, Int.cast_zero, abs_zero, ↓reduceIte,
        Real.zero_rpow (neg_ne_zero.mpr hp0.ne'), mul_zero, add_zero, mul_one, M]
      rw [abs_of_pos (lt_of_lt_of_le hδ hx)]
      exact Real.rpow_le_rpow_of_nonpos hδ hx (by linarith)
    · have hkR : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      have hpos : 0 < δ / 2 * |(k : ℝ)| := by positivity
      calc
        |x + k * N| ^ (-p) ≤ (δ / 2 * |(k : ℝ)|) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos hpos (image_distance hδ hx hxN k hk)
            (by linarith)
        _ = M k := by
          simp only [M, hk, ↓reduceIte, zero_add,
            Real.mul_rpow (by positivity : 0 ≤ δ / 2) (abs_nonneg (k : ℝ)),
            Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 2)]
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp
  have hf : Summable (fun k : ℤ => |x + k * N| ^ (-p)) :=
    Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (abs_nonneg _) _) hle hM
  refine ⟨hf, (hf.tsum_le_tsum hle hM).trans_eq ?_⟩
  rw [Summable.tsum_mul_left, Summable.tsum_add
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable (hS.mul_left _), tsum_ite_eq,
    tsum_mul_left]
  · rw [bound_eq]
    ring
  · exact (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable.add (hS.mul_left _)

/-- The nearest image supplies the lower bound. -/
theorem nearest_le {p N x : ℝ} (hp : 1 < p) (hx : 0 < x) (hxN : x < N) :
    x ^ (-p) ≤ ∑' k : ℤ, |x + k * N| ^ (-p) := by
  have hδ : 0 < min x (N - x) := lt_min hx (sub_pos.mpr hxN)
  have hf := (summable_and_le hp hδ (min_le_left _ _) (min_le_right _ _)).1
  simpa only [Int.cast_zero, zero_mul, add_zero, abs_of_pos hx] using
    hf.le_tsum (0 : ℤ) (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)

private theorem norm_deriv_image {p t z : ℝ} (hp : 0 < p) (hz : z + t ≠ 0) :
    DifferentiableAt ℝ (fun u : ℝ => |u + t| ^ (-p)) z ∧
      ‖deriv (fun u : ℝ => |u + t| ^ (-p)) z‖ = p * |z + t| ^ (-p - 1) := by
  rcases lt_or_gt_of_ne hz with hn | hpos
  · have hd := ((hasDerivAt_abs_neg hn).comp z
      ((hasDerivAt_id z).add_const t)).rpow_const (p := -p)
        (Or.inl (by simpa only [Function.comp_apply, id_eq] using abs_ne_zero.mpr hz))
    simp only [Function.comp_apply, id_eq] at hd
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    simp only [one_mul, neg_mul, neg_neg, Real.norm_eq_abs,
      abs_mul, abs_of_pos hp, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  · have hd := ((hasDerivAt_abs_pos hpos).comp z
      ((hasDerivAt_id z).add_const t)).rpow_const (p := -p)
        (Or.inl (by simpa only [Function.comp_apply, id_eq] using abs_ne_zero.mpr hz))
    simp only [Function.comp_apply, id_eq] at hd
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    simp only [one_mul, mul_one, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]

/-- A uniform Lipschitz bound for the image sum on an interval inside one period.
The constant depends only on `p`. The loss is the expected power `δ⁻ᵖ⁻¹`. -/
theorem variation {p N a b δ x y : ℝ} (hp : 1 < p) (hδ : 0 < δ)
    (ha : δ ≤ a) (hb : b ≤ N - δ) (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) :
    |(∑' k : ℤ, |y + k * N| ^ (-p)) -
      (∑' k : ℤ, |x + k * N| ^ (-p))| ≤
        (2 * p * bound (p + 1) (by linarith)) * δ ^ (-p - 1) * |y - x| := by
  have hp0 : 0 < p := by linarith
  have hab : a ≤ b := hx.1.trans hx.2
  have ha0 : 0 < a := hδ.trans_le ha
  have hbN : b < N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hq : 1 < p + 1 := by linarith
  have hsA := summable_and_le hq hδ ha (by linarith : δ ≤ N - a)
  have hsB := summable_and_le hq hδ (ha.trans hab) (by linarith : δ ≤ N - b)
  let M : ℤ → ℝ := fun k => p *
    (|a + k * N| ^ (-(p + 1)) + |b + k * N| ^ (-(p + 1))) * |y - x|
  have hM : Summable M := ((hsA.1.add hsB.1).mul_left p).mul_right _
  have hterm (k : ℤ) :
      ‖|y + k * N| ^ (-p) - |x + k * N| ^ (-p)‖ ≤ M k := by
    have hdist (z : ℝ) (hz : z ∈ Set.Icc a b) :
        0 < |z + k * N| ∧
        |z + k * N| ^ (-p - 1) ≤
          |a + k * N| ^ (-(p + 1)) + |b + k * N| ^ (-(p + 1)) := by
      by_cases hk : (0 : ℤ) ≤ k
      · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
        have haK : 0 < a + (k : ℝ) * N := by positivity
        have hzK : 0 < z + (k : ℝ) * N := by nlinarith [hz.1]
        refine ⟨by simpa only [abs_of_pos hzK] using hzK, ?_⟩
        have hpow := Real.rpow_le_rpow_of_nonpos haK
          (show a + (k : ℝ) * N ≤ z + k * N by linarith [hz.1])
          (show -p - 1 ≤ 0 by linarith)
        rw [abs_of_pos hzK, abs_of_pos haK, show -(p + 1) = -p - 1 by ring]
        exact hpow.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
      · have hkR : (k : ℝ) ≤ -1 := by
          exact_mod_cast (show k ≤ -1 by omega)
        have hbK : b + (k : ℝ) * N < 0 := by nlinarith
        have hzK : z + (k : ℝ) * N < 0 := by linarith [hz.2]
        refine ⟨abs_pos.mpr (ne_of_lt hzK), ?_⟩
        have hpow := Real.rpow_le_rpow_of_nonpos (neg_pos.mpr hbK)
          (show -(b + (k : ℝ) * N) ≤ -(z + k * N) by linarith [hz.2])
          (show -p - 1 ≤ 0 by linarith)
        rw [abs_of_neg hzK, abs_of_neg hbK, show -(p + 1) = -p - 1 by ring]
        exact hpow.trans (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
    apply (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (norm_deriv_image hp0 (abs_pos.mp (hdist z hz).1)).1) ?_ hx hy
    intro z hz
    rw [(norm_deriv_image hp0 (abs_pos.mp (hdist z hz).1)).2]
    exact mul_le_mul_of_nonneg_left (hdist z hz).2 hp0.le
  have hsX := (summable_and_le (N := N) hp hδ (ha.trans hx.1) (by linarith [hx.2])).1
  have hsY := (summable_and_le (N := N) hp hδ (ha.trans hy.1) (by linarith [hy.2])).1
  rw [← hsY.tsum_sub hsX, ← Real.norm_eq_abs]
  calc
    ‖∑' k : ℤ, (|y + k * N| ^ (-p) - |x + k * N| ^ (-p))‖ ≤ ∑' k, M k :=
      (norm_tsum_le_tsum_norm (hsY.sub hsX).norm).trans
        (((hsY.sub hsX).norm).tsum_le_tsum hterm hM)
    _ = p * ((∑' k : ℤ, |a + k * N| ^ (-(p + 1))) +
        ∑' k : ℤ, |b + k * N| ^ (-(p + 1))) * |y - x| := by
      simp only [M, tsum_mul_right, tsum_mul_left, hsA.1.tsum_add hsB.1]
    _ ≤ _ := by
      have hsum := add_le_add hsA.2 hsB.2
      rw [show -(p + 1) = -p - 1 by ring] at hsum ⊢
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum hp0.le) (abs_nonneg (y - x))]

end Riesz2.PeriodicPower
