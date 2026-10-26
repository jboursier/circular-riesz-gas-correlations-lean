/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Riesz2.ToMathlib.FiniteSchurBounds
public import Mathlib.Tactic

/-!
# Scalar bounds for commutators of power weights

For `1 < p < 2`, the difference of weights of degree `p - 1/2`
is controlled by a difference of degree `p - 1` times a square root.
The resulting kernel is dominated by an inverse-distance kernel and a
rank-one kernel. These estimates require no differentiability argument.
-/

public section

open scoped BigOperators
namespace Riesz2.PowerCommutatorBounds
/-- A power difference at ordered positive radii, with its endpoint degree. -/
theorem ordered_power_difference {p x y : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hy : 0 < y) (hyx : y ≤ x) :
    x ^ (p - 1 / 2) - y ^ (p - 1 / 2) ≤ 2 * Real.sqrt x * (x - y) ^ (p - 1) := by
  have hx : 0 < x := hy.trans_le hyx
  let t := y / x
  have ht0 : 0 ≤ t := (div_pos hy hx).le
  have ht1 : t ≤ 1 := (div_le_one hx).mpr hyx
  have hpow : t ^ (2 : ℝ) ≤ t ^ (p - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_ge (div_pos hy hx) ht1 (by linarith)
  have hlin : 1 - t ^ (p - 1 / 2) ≤ 2 * (1 - t) := by
    rw [Real.rpow_two] at hpow
    nlinarith
  have ht : 1 - t ≤ (1 - t) ^ (p - 1) := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h, sub_self, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
    · conv_lhs => rw [← Real.rpow_one (1 - t)]
      exact Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
  have hyid : y ^ (p - 1 / 2) = x ^ (p - 1 / 2) * t ^ (p - 1 / 2) := by
    rw [show t = y / x from rfl, Real.div_rpow hy.le hx.le]
    field_simp
  have hdid : (1 - t) ^ (p - 1) = (x - y) ^ (p - 1) / x ^ (p - 1) := by
    rw [show 1 - t = (x - y) / x by dsimp [t]; field_simp]
    exact Real.div_rpow (sub_nonneg.mpr hyx) hx.le _
  calc
    _ = x ^ (p - 1 / 2) * (1 - t ^ (p - 1 / 2)) := by rw [hyid]; ring
    _ ≤ x ^ (p - 1 / 2) * (2 * (1 - t) ^ (p - 1)) :=
      mul_le_mul_of_nonneg_left (hlin.trans (by linarith)) (by positivity)
    _ = _ := by
      rw [hdid, Real.sqrt_eq_rpow, show p - 1 / 2 = 1 / 2 + (p - 1) by ring,
        Real.rpow_add hx]
      field_simp

/-- The normalized power commutator is bounded by an inverse-distance
kernel plus a rank-one square-root kernel. -/
theorem scalar_kernel_bound {p x y D : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hx : 0 < x) (hy : 0 < y) (hD : 0 < D) (hd : |x - y| ≤ D) :
    |x ^ (p - 1 / 2) - y ^ (p - 1 / 2)| * D ^ (-p) / Real.sqrt y ≤
      2 * (D⁻¹ + (Real.sqrt x)⁻¹ * (Real.sqrt y)⁻¹) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hpower : D ^ (p - 1) * D ^ (-p) = D⁻¹ := by
    rw [← Real.rpow_add hD, show p - 1 + -p = -1 by ring, Real.rpow_neg_one]
  rcases le_total y x with hyx | hxy
  · have hdiff : |x ^ (p - 1 / 2) - y ^ (p - 1 / 2)| ≤
        2 * Real.sqrt x * D ^ (p - 1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hy.le hyx (by linarith)))]
      exact (ordered_power_difference hp hp2 hy hyx).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sub_nonneg.mpr hyx)
          (by rwa [abs_of_nonneg (sub_nonneg.mpr hyx)] at hd) (by linarith)) (by positivity))
    have hs : y ≤ Real.sqrt x * Real.sqrt y := by
      have := Real.sqrt_le_sqrt hyx
      nlinarith [Real.sq_sqrt hy.le]
    have hxd : x ≤ Real.sqrt x * Real.sqrt y + D := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hd
      linarith
    calc
      _ ≤ (2 * Real.sqrt x * D ^ (p - 1)) * D ^ (-p) / Real.sqrt y := by gcongr
      _ = 2 * Real.sqrt x / (D * Real.sqrt y) := by rw [mul_assoc, hpower]; ring
      _ ≤ _ := by
        apply (div_le_iff₀ (mul_pos hD hsy)).mpr
        field_simp
        nlinarith [Real.sq_sqrt hx.le]
  · have hdiff : |x ^ (p - 1 / 2) - y ^ (p - 1 / 2)| ≤
        2 * Real.sqrt y * D ^ (p - 1) := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hx.le hxy (by linarith)))]
      have hdy : y - x ≤ D := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)] at hd; exact hd
      exact (ordered_power_difference hp hp2 hx hxy).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sub_nonneg.mpr hxy) hdy (by linarith)) (by positivity))
    calc
      _ ≤ (2 * Real.sqrt y * D ^ (p - 1)) * D ^ (-p) / Real.sqrt y := by gcongr
      _ = 2 * D⁻¹ := by rw [mul_assoc, hpower]; field_simp
      _ ≤ _ := by
        have : 0 ≤ (Real.sqrt x)⁻¹ * (Real.sqrt y)⁻¹ := by positivity
        linarith
/-- An absolute kernel majorant by a Schur kernel and a rank-one kernel
controls the Euclidean norm. The index sets may be any finite type. -/
theorem sqrt_sum_sq_le_of_majorant {ι : Type*} [Fintype ι]
    (K A : ι → ι → ℝ) (w u : ι → ℝ) {H B : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 ≤ w i)
    (hrow : ∀ i, ∑ j, A i j ≤ H) (hcol : ∀ j, ∑ i, A i j ≤ H)
    (hwsq : ∑ i, w i ^ 2 ≤ H)
    (hK : ∀ i j, |K i j| ≤ 2 * B * (A i j + w i * w j)) :
    Real.sqrt (∑ i, (∑ j, K i j * u j) ^ 2) ≤
      4 * B * H * Real.sqrt (∑ j, u j ^ 2) := by
  classical
  let a := fun i => ∑ j, A i j * |u j|
  let S := ∑ j, w j * |u j|
  let U := ∑ j, u j ^ 2
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (abs_nonneg _)
  have ha (i : ι) : 0 ≤ a i := Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (abs_nonneg _)
  have hpoint (i : ι) : |∑ j, K i j * u j| ≤ 2 * B * (a i + w i * S) := by
    calc
      _ ≤ ∑ j, |K i j * u j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, 2 * B * (A i j + w i * w j) * |u j| := by
        simp only [abs_mul]
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hK i j) (abs_nonneg _)
      _ = ∑ j, 2 * B * (A i j * |u j| + w i * (w j * |u j|)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hpa : (∑ i, a i ^ 2) ≤ H ^ 2 * U := by
    have h := FiniteSchurBounds.sum_sq_norm_le A (fun j => |u j|) hH
      (fun i => by simpa only [abs_of_nonneg (hA i _)] using hrow i)
      (fun j => by simpa only [abs_of_nonneg (hA _ j)] using hcol j)
    simpa only [smul_eq_mul, Real.norm_eq_abs, abs_abs, sq_abs,
      abs_sq, a, U] using h
  have hcs : S ^ 2 ≤ H * U := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun j => |u j|)
    simp only [sq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right hwsq hU)
  have hpb : (∑ i, (w i * S) ^ 2) ≤ H ^ 2 * U := by
    calc
      _ = (∑ i, w i ^ 2) * S ^ 2 := by simp only [mul_pow, Finset.sum_mul]
      _ ≤ H * (H * U) := mul_le_mul hwsq hcs (sq_nonneg _) hH
      _ = _ := by ring
  have htotal : (∑ i, (∑ j, K i j * u j) ^ 2) ≤ (4 * B * H) ^ 2 * U := by
    calc
      _ ≤ ∑ i, 8 * B ^ 2 * (a i ^ 2 + (w i * S) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        have h := hpoint i
        have hn : 0 ≤ 2 * B * (a i + w i * S) :=
          mul_nonneg (mul_nonneg (by norm_num) hB) (add_nonneg (ha i) (mul_nonneg (hw i) hS))
        have hs := sq_le_sq₀ (abs_nonneg _) hn |>.mpr h
        rw [sq_abs] at hs
        nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg (a i - w i * S))]
      _ = 8 * B ^ 2 * ((∑ i, a i ^ 2) + ∑ i, (w i * S) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 8 * B ^ 2 * (H ^ 2 * U + H ^ 2 * U) :=
        mul_le_mul_of_nonneg_left (add_le_add hpa hpb) (by positivity)
      _ = _ := by ring
  have h := Real.sqrt_le_sqrt htotal
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h

end Riesz2.PowerCommutatorBounds
