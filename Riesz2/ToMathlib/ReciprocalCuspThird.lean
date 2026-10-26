/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.ReciprocalCusp

/-!
# Third derivatives of reciprocals with power bounds

The order-three calculus step used in the proof of Lemma 5.13.
-/

public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz2.ReciprocalCusp

/-- Third derivative of a reciprocal on an open set. -/
theorem third_derivative {F : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 3 F U) (hne : ∀ x ∈ U, F x ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv (deriv (deriv (fun y => (F y)⁻¹))) x =
      -6 * deriv F x ^ 3 * (F x)⁻¹ ^ 4 +
        6 * deriv F x * deriv (deriv F) x * (F x)⁻¹ ^ 3 -
        deriv (deriv (deriv F)) x * (F x)⁻¹ ^ 2 := by
  have hd : DifferentiableAt ℝ F x :=
    (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hF' : ContDiffOn ℝ 2 (deriv F) U :=
    hF.deriv_of_isOpen hU (by norm_num)
  have hd' : DifferentiableAt ℝ (deriv F) x :=
    (hF'.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hd'' : DifferentiableAt ℝ (deriv (deriv F)) x :=
    ((hF'.deriv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hi : HasDerivAt (fun y => (F y)⁻¹)
      (-deriv F x * (F x)⁻¹ ^ 2) x := by
    convert hd.hasDerivAt.inv (hne x hx) using 1
    simp only [div_eq_mul_inv, inv_pow]
  have he : deriv (deriv (fun y => (F y)⁻¹)) =ᶠ[𝓝 x]
      (fun y => 2 * deriv F y ^ 2 * (F y)⁻¹ ^ 3 -
        deriv (deriv F) y * (F y)⁻¹ ^ 2) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact second_derivative hU (hF.of_le (by norm_num)) hne hy
  rw [he.deriv_eq]
  convert (((hd'.hasDerivAt.pow 2).const_mul 2).mul (hi.pow 3) |>.sub
    (hd''.hasDerivAt.mul (hi.pow 2))).deriv using 1
  simp only [Pi.pow_apply]
  ring

/-- The third derivative envelope for the reciprocal of a power singularity. -/
theorem third_bound {f f' f'' f''' c D E G r a : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (hr : 0 < r) (hf : c * r ^ a ≤ f)
    (hf' : |f'| ≤ D * r ^ (a - 1)) (hf'' : |f''| ≤ E * r ^ (a - 2))
    (hf''' : |f'''| ≤ G * r ^ (a - 3)) :
    |-6 * f' ^ 3 * f⁻¹ ^ 4 + 6 * f' * f'' * f⁻¹ ^ 3 - f''' * f⁻¹ ^ 2| ≤
      (6 * D ^ 3 * c⁻¹ ^ 4 + 6 * D * E * c⁻¹ ^ 3 + G * c⁻¹ ^ 2) *
        r ^ (-a - 3) := by
  have hi := inv_bound hc hr hf
  have h1 : |-6 * f' ^ 3 * f⁻¹ ^ 4| ≤
      (6 * D ^ 3 * c⁻¹ ^ 4) * r ^ (-a - 3) := by
    calc
      _ = 6 * |f'| ^ 3 * |f⁻¹| ^ 4 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 6 * (D * r ^ (a - 1)) ^ 3 * (c⁻¹ * r ^ (-a)) ^ 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hf' 3) (by norm_num))
          (pow_le_pow_left₀ (abs_nonneg _) hi 4) (by positivity) (by positivity)
      _ = (6 * D ^ 3 * c⁻¹ ^ 4) * (r ^ ((a - 1) * 3) * r ^ ((-a) * 4)) := by
        rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hr.le (a - 1) 3,
          ← Real.rpow_mul_natCast hr.le (-a) 4]
        norm_num only [Nat.cast_ofNat]
        ring
      _ = _ := by rw [← Real.rpow_add hr]; congr 2; ring
  have h2 : |6 * f' * f'' * f⁻¹ ^ 3| ≤
      (6 * D * E * c⁻¹ ^ 3) * r ^ (-a - 3) := by
    calc
      _ = 6 * |f'| * |f''| * |f⁻¹| ^ 3 := by
        simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      _ ≤ 6 * (D * r ^ (a - 1)) * (E * r ^ (a - 2)) *
          (c⁻¹ * r ^ (-a)) ^ 3 :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hf' (by norm_num)) hf''
          (abs_nonneg _) (by positivity)) (pow_le_pow_left₀ (abs_nonneg _) hi 3)
          (by positivity) (by positivity)
      _ = (6 * D * E * c⁻¹ ^ 3) *
          ((r ^ (a - 1) * r ^ (a - 2)) * r ^ ((-a) * 3)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le (-a) 3]
        norm_num only [Nat.cast_ofNat]
        ring
      _ = _ := by rw [← Real.rpow_add hr, ← Real.rpow_add hr]; congr 2; ring
  have h3 : |f''' * f⁻¹ ^ 2| ≤ (G * c⁻¹ ^ 2) * r ^ (-a - 3) := by
    calc
      _ = |f'''| * |f⁻¹| ^ 2 := by rw [abs_mul, abs_pow]
      _ ≤ (G * r ^ (a - 3)) * (c⁻¹ * r ^ (-a)) ^ 2 :=
        mul_le_mul hf''' (pow_le_pow_left₀ (abs_nonneg _) hi 2)
          (sq_nonneg _) (by positivity)
      _ = (G * c⁻¹ ^ 2) * (r ^ (a - 3) * r ^ ((-a) * 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le (-a) 2]
        norm_num only [Nat.cast_ofNat]
        ring
      _ = _ := by rw [← Real.rpow_add hr]; congr 2; ring
  calc
    _ ≤ |-6 * f' ^ 3 * f⁻¹ ^ 4 + 6 * f' * f'' * f⁻¹ ^ 3| + |f''' * f⁻¹ ^ 2| :=
      abs_sub _ _
    _ ≤ (6 * D ^ 3 * c⁻¹ ^ 4 * r ^ (-a - 3) +
        6 * D * E * c⁻¹ ^ 3 * r ^ (-a - 3)) + G * c⁻¹ ^ 2 * r ^ (-a - 3) :=
      add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3
    _ = _ := by ring

end Riesz2.ReciprocalCusp
