/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicFourier
public import Riesz2.ToMathlib.BoundedMatrixModes

/-!
# Finite Fourier multipliers on real L² fields

Parseval is integrated only after establishing integrability of every term.
The real and imaginary modes are finite combinations in the original L²
space, and the transform has the positive sign and counting normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Riesz2.CyclicFourierL2

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- The integral of the square of an L² representative is its squared norm. -/
theorem integral_sq (u : Lp ℝ 2 ν) : (∫ x, u x ^ 2 ∂ν) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two]

/-- Integrated Parseval for any real finite Fourier multiplier. This includes
the zero-killing fractional primitive and asserts integrability explicitly. -/
theorem multiplier_parseval (N : ℕ+) (b : Fin (N : ℕ) → ℝ)
    (u : Fin (N : ℕ) → Lp ℝ 2 ν) :
    let J := fun x => cycleFourierInv N (fun k => (b k : ℂ) *
      cycleFourier N (fun j => (u j x : ℂ)) k)
    Integrable (fun x => ∑ i, ‖J x i‖ ^ 2) ν ∧
    (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν) =
      (N : ℝ)⁻¹ * ∑ k, (b k) ^ 2 *
        (‖∑ j, (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).re • u j‖ ^ 2 +
          ‖∑ j, (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).im • u j‖ ^ 2) := by
  let R : Fin (N : ℕ) → Lp ℝ 2 ν := fun k =>
    ∑ j, (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).re • u j
  let I : Fin (N : ℕ) → Lp ℝ 2 ν := fun k =>
    ∑ j, (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).im • u j
  have hR : ∀ᵐ x ∂ν, ∀ k : Fin (N : ℕ), R k x =
      (cycleFourier N (fun j => (u j x : ℂ)) k).re := by
    apply ae_all_iff.mpr
    intro k
    have h := BoundedMatrixModes.coe_sum_smul
      (fun j : Fin (N : ℕ) => (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).re) u
    filter_upwards [h] with x hx
    change (∑ j, (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).re • u j) x = _
    rw [hx]
    simp only [cycleFourier, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro j _; ring
  have hI : ∀ᵐ x ∂ν, ∀ k : Fin (N : ℕ), I k x =
      (cycleFourier N (fun j => (u j x : ℂ)) k).im := by
    apply ae_all_iff.mpr
    intro k
    have h := BoundedMatrixModes.coe_sum_smul
      (fun j : Fin (N : ℕ) => (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).im) u
    filter_upwards [h] with x hx
    change (∑ j, (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))).im • u j) x = _
    rw [hx]
    simp only [cycleFourier, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j _; ring
  let J := fun x => cycleFourierInv N (fun k => (b k : ℂ) *
    cycleFourier N (fun j => (u j x : ℂ)) k)
  have he : (fun x => ∑ i, ‖J x i‖ ^ 2) =ᵐ[ν]
      (fun x => (N : ℝ)⁻¹ * ∑ k, (b k) ^ 2 * ((R k x) ^ 2 + (I k x) ^ 2)) := by
    filter_upwards [hR, hI] with x hr hi
    dsimp only [J]
    rw [sum_norm_sq_cycleFourier]
    simp only [cycleFourier_cycleFourierInv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hr k, hi k, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hint (k) : Integrable (fun x => (b k) ^ 2 * ((R k x) ^ 2 + (I k x) ^ 2)) ν :=
    ((Lp.memLp (R k)).integrable_sq.add (Lp.memLp (I k)).integrable_sq).const_mul _
  have hsum := (integrable_finsetSum Finset.univ (fun k _ => hint k)).const_mul (N : ℝ)⁻¹
  refine ⟨hsum.congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const_mul, integral_finsetSum _ (fun k _ => hint k)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, integral_add (Lp.memLp (R k)).integrable_sq
    (Lp.memLp (I k)).integrable_sq, integral_sq, integral_sq]

/-- Counting-measure mixed L² norm with a deterministic real diagonal weight.
The integral is finite, and equals the sum of the weighted component norms. -/
theorem weighted_integral_sq {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (u : ι → Lp ℝ 2 ν) :
    Integrable (fun x => ∑ j, (w j * u j x) ^ 2) ν ∧
      (∫ x, ∑ j, (w j * u j x) ^ 2 ∂ν) = ∑ j, (w j * ‖u j‖) ^ 2 := by
  have hint (j) : Integrable (fun x => (w j * u j x) ^ 2) ν := by
    simpa only [mul_pow] using ((Lp.memLp (u j)).integrable_sq.const_mul (w j ^ 2))
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hint j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_pow, integral_const_mul, integral_sq]

end Riesz2.CyclicFourierL2
