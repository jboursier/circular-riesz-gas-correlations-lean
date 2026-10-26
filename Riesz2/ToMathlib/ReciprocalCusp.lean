/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Derivatives and power estimates for reciprocals

Local calculus and algebra for a positive function with a power singularity.
-/

public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz2.ReciprocalCusp

/-- The second derivative of a reciprocal on an open set. -/
theorem second_derivative {F : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) (hne : ∀ x ∈ U, F x ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv (deriv (fun y => (F y)⁻¹)) x =
      2 * deriv F x ^ 2 * (F x)⁻¹ ^ 3 - deriv (deriv F) x * (F x)⁻¹ ^ 2 := by
  have hd (y : ℝ) (hy : y ∈ U) : DifferentiableAt ℝ F y :=
    (hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hi : HasDerivAt (fun y => (F y)⁻¹)
      (-deriv F x * (F x)⁻¹ ^ 2) x := by
    convert (hd x hx).hasDerivAt.inv (hne x hx) using 1
    simp only [div_eq_mul_inv, inv_pow]
  have he : deriv (fun y => (F y)⁻¹) =ᶠ[𝓝 x]
      (fun y => -deriv F y * (F y)⁻¹ ^ 2) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [deriv_fun_inv'' (hd y hy) (hne y hy)]
    simp only [div_eq_mul_inv, inv_pow]
  rw [he.deriv_eq]
  have hd' : DifferentiableAt ℝ (deriv F) x :=
    ((hF.deriv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num)
  convert (hd'.hasDerivAt.neg.mul (hi.pow 2)).deriv using 1
  simp only [Pi.neg_apply, Pi.pow_apply]
  ring

/-- Inverting a positive lower power bound reverses its exponent. -/
theorem inv_bound {f c r a : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hf : c * r ^ a ≤ f) : |f⁻¹| ≤ c⁻¹ * r ^ (-a) := by
  have hpos := mul_pos hc (Real.rpow_pos_of_pos hr a)
  rw [abs_of_pos (inv_pos.mpr (hpos.trans_le hf)), Real.rpow_neg hr.le]
  simpa only [one_div, mul_inv_rev, mul_comm] using
    one_div_le_one_div_of_le hpos hf

/-- The derivative envelope for a reciprocal of a power singularity. -/
theorem first_bound {f f' c D r a : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hr : 0 < r) (hf : c * r ^ a ≤ f) (hf' : |f'| ≤ D * r ^ (a - 1)) :
    |-f' / f ^ 2| ≤ (D * c⁻¹ ^ 2) * r ^ (-a - 1) := by
  have hi := inv_bound hc hr hf
  calc
    |-f' / f ^ 2| = |f'| * |f⁻¹| ^ 2 := by
      simp only [div_eq_mul_inv, ← inv_pow, abs_mul, abs_neg, abs_pow]
    _ ≤ (D * r ^ (a - 1)) * (c⁻¹ * r ^ (-a)) ^ 2 :=
      mul_le_mul hf' (pow_le_pow_left₀ (abs_nonneg _) hi 2) (sq_nonneg _)
        (mul_nonneg hD (Real.rpow_nonneg hr.le _))
    _ = (D * c⁻¹ ^ 2) * (r ^ (a - 1) * r ^ ((-a) * 2)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hr.le (-a) 2]
      norm_num only [Nat.cast_ofNat]
      ring
    _ = _ := by
      rw [← Real.rpow_add hr]
      congr 2
      ring

/-- The second derivative envelope for a reciprocal of a power singularity. -/
theorem second_bound {f f' f'' c D E r a : ℝ} (hc : 0 < c) (_hD : 0 ≤ D)
    (hE : 0 ≤ E) (hr : 0 < r) (hf : c * r ^ a ≤ f)
    (hf' : |f'| ≤ D * r ^ (a - 1)) (hf'' : |f''| ≤ E * r ^ (a - 2)) :
    |2 * f' ^ 2 * f⁻¹ ^ 3 - f'' * f⁻¹ ^ 2| ≤
      (2 * D ^ 2 * c⁻¹ ^ 3 + E * c⁻¹ ^ 2) * r ^ (-a - 2) := by
  have hi := inv_bound hc hr hf
  have h1 : |2 * f' ^ 2 * f⁻¹ ^ 3| ≤
      (2 * D ^ 2 * c⁻¹ ^ 3) * r ^ (-a - 2) := by
    calc
      _ = 2 * |f'| ^ 2 * |f⁻¹| ^ 3 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (D * r ^ (a - 1)) ^ 2 * (c⁻¹ * r ^ (-a)) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hf' 2) (by norm_num))
          (pow_le_pow_left₀ (abs_nonneg _) hi 3) (by positivity) (by positivity)
      _ = (2 * D ^ 2 * c⁻¹ ^ 3) *
          (r ^ ((a - 1) * 2) * r ^ ((-a) * 3)) := by
        rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hr.le (a - 1) 2,
          ← Real.rpow_mul_natCast hr.le (-a) 3]
        norm_num only [Nat.cast_ofNat]
        ring
      _ = _ := by
        rw [← Real.rpow_add hr]
        congr 2
        ring
  have h2 : |f'' * f⁻¹ ^ 2| ≤ (E * c⁻¹ ^ 2) * r ^ (-a - 2) := by
    calc
      _ = |f''| * |f⁻¹| ^ 2 := by rw [abs_mul, abs_pow]
      _ ≤ (E * r ^ (a - 2)) * (c⁻¹ * r ^ (-a)) ^ 2 :=
        mul_le_mul hf'' (pow_le_pow_left₀ (abs_nonneg _) hi 2) (sq_nonneg _)
          (mul_nonneg hE (Real.rpow_nonneg hr.le _))
      _ = (E * c⁻¹ ^ 2) * (r ^ (a - 2) * r ^ ((-a) * 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le (-a) 2]
        norm_num only [Nat.cast_ofNat]
        ring
      _ = _ := by
        rw [← Real.rpow_add hr]
        congr 2
        ring
  exact (abs_sub _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end Riesz2.ReciprocalCusp
