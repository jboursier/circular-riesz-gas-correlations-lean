/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicFourier

/-!
# Fourier transform of a cyclic second difference

The transform uses the existing positive-sign convention on `Fin N`.
-/

public section

open scoped BigOperators

namespace Riesz2

/-- Addition of cyclic indices multiplies Fourier characters. -/
theorem cycleCharacter_add (N : ℕ+) (i j k : Fin (N : ℕ)) :
    Complex.exp (Complex.I * ((i + j).val : ℂ) * (cycleAngle N k : ℂ)) =
      Complex.exp (Complex.I * (i.val : ℂ) * (cycleAngle N k : ℂ)) *
        Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ)) := by
  simp only [kernel_eq]
  rw [← zpow_add₀ (cycleRoot_ne_zero N)]
  apply zpow_eq_of_dvd
  have hmod : ((i + j).val : ℤ) =
      ((i.val + j.val) % (N : ℕ) : ℕ) := by rw [Fin.val_add]
  rw [hmod]
  refine ⟨-(((i.val + j.val) / (N : ℕ) : ℕ) : ℤ) * k.val, ?_⟩
  have hdiv := Nat.mod_add_div (i.val + j.val) (N : ℕ)
  have hd : (((i.val + j.val) % (N : ℕ) : ℕ) : ℤ) +
      (N : ℕ) * (((i.val + j.val) / (N : ℕ) : ℕ) : ℤ) = i.val + j.val := by
    exact_mod_cast hdiv
  linear_combination (k.val : ℤ) * hd

/-- Fourier transform of a cyclic translate. -/
theorem cycleFourier_translate (N : ℕ+) (f : Fin (N : ℕ) → ℂ)
    (a k : Fin (N : ℕ)) :
    cycleFourier N (fun n => f (n + a)) k =
      Complex.exp (Complex.I * ((-a).val : ℂ) * (cycleAngle N k : ℂ)) *
        cycleFourier N f k := by
  unfold cycleFourier
  rw [Finset.mul_sum]
  have h := (Equiv.addRight a).sum_comp Finset.univ
    (fun n : Fin (N : ℕ) => f n *
      Complex.exp (Complex.I * (((n - a).val) : ℂ) * (cycleAngle N k : ℂ)))
  have hh := h (by simp)
  clear h
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro n _
  rw [show n - a = n + -a from sub_eq_add_neg n a, cycleCharacter_add]
  ring

/-- The multiplier of a cyclic second difference is `-2(1-cos θ)`. -/
theorem cycleFourier_secondDifference (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (f : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) :
    cycleFourier N (fun n => f (n + 1) + f (n - 1) - 2 * f n) k =
      (-2 * (1 - Real.cos (cycleAngle N k)) : ℝ) * cycleFourier N f k := by
  have hsplit : cycleFourier N (fun n => f (n + 1) + f (n - 1) - 2 * f n) k =
      cycleFourier N (fun n => f (n + 1)) k +
        cycleFourier N (fun n => f (n + (-1))) k - 2 * cycleFourier N f k := by
    simp only [sub_eq_add_neg]
    simp only [cycleFourier, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib,
      mul_assoc, ← Finset.mul_sum]
  rw [hsplit, cycleFourier_translate, cycleFourier_translate, neg_neg]
  have he (a : Fin (N : ℕ)) :
      Complex.exp (Complex.I * ((-a).val : ℂ) * (cycleAngle N k : ℂ)) =
        Complex.exp (-(Complex.I * (a.val : ℂ) * (cycleAngle N k : ℂ))) := by
    have h := cycleCharacter_add N a (-a) k
    simp only [add_neg_cancel, Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul,
      Complex.exp_zero] at h
    apply (mul_left_cancel₀ (Complex.exp_ne_zero
      (Complex.I * (a.val : ℂ) * (cycleAngle N k : ℂ))))
    rw [← h, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h1 : ((1 : Fin (N : ℕ)).val : ℂ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < (N : ℕ) by omega)]
    norm_num
  rw [he, h1, mul_one]
  have hcos := Complex.two_cos (cycleAngle N k : ℂ)
  rw [← Complex.ofReal_cos] at hcos
  have hp : (cycleAngle N k : ℂ) * Complex.I =
      Complex.I * (cycleAngle N k : ℂ) := mul_comm _ _
  have hm : -(cycleAngle N k : ℂ) * Complex.I =
      -(Complex.I * (cycleAngle N k : ℂ)) := by ring
  rw [hp, hm] at hcos
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_sub, Complex.ofReal_one]
  linear_combination -(cycleFourier N f k) * hcos

end Riesz2
