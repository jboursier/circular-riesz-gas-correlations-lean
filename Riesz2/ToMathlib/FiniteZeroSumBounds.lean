/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Weighted estimates for finite zero-sum rows

Cancellation on an arbitrary subset, weighted Cauchy--Schwarz, and the
Hilbert--Schmidt estimate for finite real kernels. No norm is redefined.
-/

public section

open scoped BigOperators
open Finset

namespace Riesz2.FiniteZeroSumBounds

/-- Subtracting a constant on a subset of a zero-sum vector leaves its
complement as an explicit correction. -/
theorem centered_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f g : ι → ℝ) (c : ℝ) (hg : ∑ j, g j = 0) :
    (∑ j ∈ S, f j * g j) =
      (∑ j ∈ S, (f j - c) * g j) - c * ∑ j ∈ Sᶜ, g j := by
  have hsplit : (∑ j ∈ S, g j) + ∑ j ∈ Sᶜ, g j = 0 := by
    rw [sum_add_sum_compl, hg]
  simp only [sub_mul, sum_sub_distrib, ← mul_sum]
  have hc := congrArg (c * ·) hsplit
  rw [mul_add, mul_zero] at hc
  linarith

/-- Weighted Cauchy--Schwarz on a subset, with the full energy on the
right. It includes the empty subset and the zero vector. -/
theorem weighted_cauchy_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w a g : ι → ℝ) (hw : ∀ j, 0 < w j) :
    (∑ j ∈ S, |a j * g j|) ≤
      Real.sqrt (∑ j ∈ S, (a j / w j) ^ 2) *
        Real.sqrt (∑ j, (w j * g j) ^ 2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq S (fun j => |a j / w j|)
    (fun j => |w j * g j|)
  have heq (j : ι) : |a j / w j| * |w j * g j| = |a j * g j| := by
    rw [← abs_mul]
    congr 1
    field_simp [(hw j).ne']
  simp only [heq, sq_abs] at hcs
  have hsub : (∑ j ∈ S, (w j * g j) ^ 2) ≤ ∑ j, (w j * g j) ^ 2 :=
    sum_le_univ_sum_of_nonneg (fun j => sq_nonneg _)
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hsub (by positivity))
  have hroot := Real.sqrt_le_sqrt hcs'
  rw [Real.sqrt_sq (sum_nonneg (fun j _ => abs_nonneg _)),
    Real.sqrt_mul (by positivity : 0 ≤ ∑ j ∈ S, (a j / w j) ^ 2)] at hroot
  exact hroot

/-- A centered subset row controlled by weighted coefficient energies.
This is an internal estimate: applications supply the two coefficient
bounds from their kernel and geometry. -/
theorem centered_subset_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f g w : ι → ℝ) (c U V : ℝ)
    (hg : ∑ j, g j = 0) (hw : ∀ j, 0 < w j)
    (hU : Real.sqrt (∑ j ∈ S, ((f j - c) / w j) ^ 2) ≤ U)
    (hV : |c| * Real.sqrt (∑ j ∈ Sᶜ, (1 / w j) ^ 2) ≤ V) :
    |∑ j ∈ S, f j * g j| ≤
      (U + V) * Real.sqrt (∑ j, (w j * g j) ^ 2) := by
  rw [centered_subset S f g c hg]
  calc
    _ ≤ |∑ j ∈ S, (f j - c) * g j| + |c * ∑ j ∈ Sᶜ, g j| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (∑ j ∈ S, (f j - c) * g j) (-(c * ∑ j ∈ Sᶜ, g j))
    _ ≤ (∑ j ∈ S, |(f j - c) * g j|) + |c| * ∑ j ∈ Sᶜ, |g j| := by
      rw [abs_mul]
      gcongr
      · exact abs_sum_le_sum_abs _ _
      · exact abs_sum_le_sum_abs _ _
    _ ≤ U * Real.sqrt (∑ j, (w j * g j) ^ 2) +
        V * Real.sqrt (∑ j, (w j * g j) ^ 2) := by
      apply add_le_add
      · exact (weighted_cauchy_subset S w (fun j => f j - c) g hw).trans
          (mul_le_mul_of_nonneg_right hU (Real.sqrt_nonneg _))
      · have hc := weighted_cauchy_subset Sᶜ w (fun _ => 1) g hw
        simp only [one_mul] at hc
        calc
          _ ≤ |c| * (Real.sqrt (∑ j ∈ Sᶜ, (1 / w j) ^ 2) *
              Real.sqrt (∑ j, (w j * g j) ^ 2)) :=
            mul_le_mul_of_nonneg_left hc (abs_nonneg _)
          _ = (|c| * Real.sqrt (∑ j ∈ Sᶜ, (1 / w j) ^ 2)) *
              Real.sqrt (∑ j, (w j * g j) ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hV (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The Hilbert--Schmidt quadratic estimate for a finite real matrix. -/
theorem quadratic_hilbertSchmidt {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (u : ι → ℝ) :
    |∑ i, ∑ j, K i j * u i * u j| ≤
      Real.sqrt (∑ i, ∑ j, K i j ^ 2) * ∑ i, u i ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (ι × ι))
    (fun ij => K ij.1 ij.2) (fun ij => u ij.1 * u ij.2)
  simp only [Fintype.sum_prod_type, mul_pow] at hcs
  have hprod : (∑ i, ∑ j, u i ^ 2 * u j ^ 2) = (∑ i, u i ^ 2) ^ 2 := by
    simp only [← mul_sum, ← sum_mul, pow_two]
  rw [hprod] at hcs
  have hh := Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (by positivity : 0 ≤ ∑ i, ∑ j, K i j ^ 2),
    Real.sqrt_sq (sum_nonneg (fun i _ => sq_nonneg _))] at hh
  simpa only [mul_assoc] using hh

namespace Internal

/-- Internal assembly of the leading far-row term: centering each row
against a zero-sum vector and then applying weighted Cauchy--Schwarz in
the row index costs the square root of the coefficient energy. Applications
must prove the displayed coefficient bounds from their actual kernel. -/
theorem centered_rows_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ι) (f : ι → ι → ℝ) (c t U V w g : ι → ℝ)
    (hg : ∑ j, g j = 0) (hw : ∀ j, 0 < w j)
    (hU : ∀ i, Real.sqrt (∑ j ∈ S i, ((f i j - c i) / w j) ^ 2) ≤ U i)
    (hV : ∀ i, |c i| * Real.sqrt (∑ j ∈ (S i)ᶜ, (1 / w j) ^ 2) ≤ V i) :
    |∑ i, t i * g i * ∑ j ∈ S i, f i j * g j| ≤
      Real.sqrt (∑ i, (t i * (U i + V i) / w i) ^ 2) *
        ∑ j, (w j * g j) ^ 2 := by
  let E := ∑ j, (w j * g j) ^ 2
  have hE : 0 ≤ E := sum_nonneg (fun j _ => sq_nonneg _)
  have hU₀ (i) : 0 ≤ U i := (Real.sqrt_nonneg _).trans (hU i)
  have hV₀ (i) : 0 ≤ V i := (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)).trans (hV i)
  have hr (i) := centered_subset_bound (S i) (f i) g w (c i) (U i) (V i)
    hg hw (hU i) (hV i)
  calc
    _ ≤ ∑ i, |t i * g i * ∑ j ∈ S i, f i j * g j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |t i * g i| * ((U i + V i) * Real.sqrt E) := by
      simp only [abs_mul]
      apply sum_le_sum
      intro i _
      simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hr i) (abs_nonneg (t i * g i))
    _ = (∑ i, |(t i * (U i + V i)) * g i|) * Real.sqrt E := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      rw [abs_mul (t i * (U i + V i)), abs_mul (t i) (U i + V i),
        abs_of_nonneg (add_nonneg (hU₀ i) (hV₀ i)), abs_mul]
      ring
    _ ≤ (Real.sqrt (∑ i, (t i * (U i + V i) / w i) ^ 2) * Real.sqrt E) *
        Real.sqrt E := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact weighted_cauchy_subset univ w (fun i => t i * (U i + V i)) g hw
    _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hE]

end Internal

end Riesz2.FiniteZeroSumBounds
