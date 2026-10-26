/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reflection and conjugation of circle Fourier coefficients

The identities hold for every positive circumference and complex-valued
function. Real even functions consequently have real even coefficients.
-/

public section
noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Riesz2.CircleFourier

variable {T : ℝ} [Fact (0 < T)]

/-- Reflecting the input reverses the Fourier frequency. -/
theorem coefficient_reflection (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => f (-x)) n = fourierCoeff f (-n) := by
  have : (AddCircle.haarAddCircle (T := T)).IsNegInvariant := by
    unfold AddCircle.haarAddCircle
    infer_instance
  unfold fourierCoeff
  rw [← integral_neg_eq_self
    (fun x : AddCircle T => fourier (-(-n)) x • f x) AddCircle.haarAddCircle]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [neg_neg, fourier_apply, smul_neg, neg_smul]

/-- Complex conjugation reverses the Fourier frequency and conjugates the
coefficient. -/
theorem coefficient_conjugation (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => conj (f x)) (-n) = conj (fourierCoeff f n) := by
  simp only [fourierCoeff, ← integral_conj, smul_eq_mul, map_mul, neg_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← fourier_neg, neg_neg]

/-- The coefficients of an even function are even. -/
theorem coefficient_neg_of_even (f : AddCircle T → ℂ)
    (hf : ∀ x, f (-x) = f x) (n : ℤ) : fourierCoeff f (-n) = fourierCoeff f n := by
  rw [← coefficient_reflection]
  congr 1
  exact funext hf

/-- The coefficients of a real even function have zero imaginary part. -/
theorem coefficient_im_of_real_even (f : AddCircle T → ℝ)
    (hf : ∀ x, f (-x) = f x) (n : ℤ) :
    (fourierCoeff (fun x => (f x : ℂ)) n).im = 0 := by
  have he := coefficient_neg_of_even (fun x => (f x : ℂ))
    (fun x => congrArg Complex.ofReal (hf x)) n
  have hc := coefficient_conjugation (fun x => (f x : ℂ)) n
  simp only [Complex.conj_ofReal] at hc
  rw [he] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

end Riesz2.CircleFourier
