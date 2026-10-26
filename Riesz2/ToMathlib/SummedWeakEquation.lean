/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.BoundedMatrixModes
public import Riesz2.ToMathlib.ScalarFormHalfGenerator

/-!
# Summing an unrestricted matrix weak equation

The constant component test gives a scalar equation with the exact reference
row mass. Its error is an actual L² class, constructed from bounded measurable
coefficients. Scalar energy estimates and the form triangle inequality apply
on the entire form domain, including nonsmooth L² sources.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Riesz2.SummedWeakEquation

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ν : Measure α}

/-- Summing an unrestricted equation against a constant component test.
The error term is constructed in L² and retains its exact coefficient bound. -/
theorem summed_equation (Q : ScalarFormData ν)
    (M : α → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (H : Matrix ι ι ℝ) (b : ℝ) (hrow : ∀ i, ∑ j, H i j = b)
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ᵐ x ∂ν, ∀ i, |∑ j, (M x i j - H i j)| ≤ B)
    (f : ι → Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ f u) :
    ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = ∑ i, (u i).val x * ∑ j, (M x i j - H i j)) ∧
      ‖g‖ ≤ B * ∑ i, ‖(u i).val‖ ∧
      ∀ w : Q.1,
        Q.2 (∑ i, u i) w + b * inner ℝ (∑ i, (u i).val) w.val =
          inner ℝ ((∑ i, f i) - g) w.val := by
  classical
  let d : ι → α → ℝ := fun i x => ∑ j, (M x i j - H i j)
  have hd (i) : Measurable (d i) :=
    Finset.measurable_sum _ (fun j _ => (hMm i j).sub measurable_const)
  choose g hg hgn using fun i => BoundedMatrixModes.exists_multiplier (d i) (hd i)
    B hB (herror.mono fun x hx => hx i) (u i).val
  have hgv : ∀ᵐ x ∂ν, (∑ i, g i) x =
      ∑ i, (u i).val x * ∑ j, (M x i j - H i j) := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ g, ae_all_iff.mpr hg] with x hs hx
    rw [hs]
    exact Finset.sum_congr rfl (fun i _ => (hx i).trans (mul_comm _ _))
  refine ⟨∑ i, g i, hgv, ?_, ?_⟩
  · exact (norm_sum_le _ _).trans
      ((Finset.sum_le_sum fun i _ => hgn i).trans_eq (Finset.mul_sum _ _ _).symm)
  intro w
  have hw : WeightedFormDomain Q M ⊤ (fun _ : ι => w) := by
    apply (BoundedMatrixForms.domain_iff Q M hMm hMb _ _).mpr
    exact ae_of_all _ (fun _ => Submodule.mem_top)
  have ht := (hu.2 (fun _ => w) hw).2
  have hp : matrixFieldPair M (fun i => (u i).val) (fun _ : ι => w.val) =ᵐ[ν]
      (fun x => b * ((∑ i, (u i).val) x * w.val x) + (∑ i, g i) x * w.val x) := by
    filter_upwards [hgv, Lp.coeFn_fun_finsetSum Finset.univ (fun i => (u i).val)] with x hgx hux
    rw [hgx, hux]
    simp only [matrixFieldPair]
    have he (i) : (∑ j, (u i).val x * M x i j * w.val x) =
        b * (u i).val x * w.val x +
          ((u i).val x * ∑ j, (M x i j - H i j)) * w.val x := by
      rw [Finset.sum_sub_distrib, hrow]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  have hi := integral_congr_ae hp
  rw [integral_add, integral_const_mul] at hi
  · have hinner (v : Lp ℝ 2 ν) : (∫ x, v x * w.val x ∂ν) = inner ℝ v w.val := by
      rw [L2.inner_def]
      simp only [Real.inner_apply]
    rw [hinner, hinner] at hi
    simp only [map_sum, LinearMap.sum_apply] at ht ⊢
    rw [hi, ← sum_inner] at ht
    rw [inner_sub_left]
    linarith only [ht]
  · exact ((Lp.memLp _).integrable_mul (Lp.memLp w.val)).const_mul b
  · exact (Lp.memLp _).integrable_mul (Lp.memLp w.val)

/-- Exact scalar value and energy estimates, obtained by testing at the
solution. The source is an L² class and the shift is strictly positive. -/
theorem scalar_estimates (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ν) (u : Q.1)
    (hu : ∀ w : Q.1, Q.2 u w + b * inner ℝ u.val w.val = inner ℝ f w.val) :
    ‖u.val‖ ≤ b⁻¹ * ‖f‖ ∧ Real.sqrt (Q.2 u u) ≤ (Real.sqrt b)⁻¹ * ‖f‖ := by
  have he := hu u
  rw [real_inner_self_eq_norm_sq] at he
  have hcs := real_inner_le_norm f u.val
  have hq := hQ.2.2.1 u
  have hv : b * ‖u.val‖ ≤ ‖f‖ := by
    by_cases hz : ‖u.val‖ = 0
    · rw [hz, mul_zero]; exact norm_nonneg _
    · have hp : 0 < ‖u.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [he, hcs, hq]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hb]
    nlinarith only [hv]
  · have henergy : b * Q.2 u u ≤ ‖f‖ ^ 2 := by
      have hqv : Q.2 u u ≤ ‖f‖ * ‖u.val‖ := by
        nlinarith only [he, hcs, mul_nonneg hb.le (sq_nonneg ‖u.val‖)]
      have hh := mul_le_mul_of_nonneg_left hqv hb.le
      have hv' := mul_le_mul_of_nonneg_left hv (norm_nonneg f)
      nlinarith only [hh, hv']
    have hbroot := Real.sqrt_pos.mpr hb
    have hqroot := Real.sq_sqrt hq
    have hbroot2 := Real.sq_sqrt hb.le
    rw [inv_mul_eq_div, le_div_iff₀ hbroot]
    have hs : (Real.sqrt b * Real.sqrt (Q.2 u u)) ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [mul_pow, hbroot2, hqroot]
      exact henergy
    nlinarith only [(sq_le_sq₀ (mul_nonneg hbroot.le (Real.sqrt_nonneg _))
      (norm_nonneg f)).mp hs]

/-- The form seminorm satisfies the triangle inequality on finite sums. -/
theorem sqrt_energy_sum_le (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    {κ : Type*} (s : Finset κ) (u : κ → Q.1) :
    Real.sqrt (Q.2 (∑ i ∈ s, u i) (∑ i ∈ s, u i)) ≤
      ∑ i ∈ s, Real.sqrt (Q.2 (u i) (u i)) := by
  let D := (ScalarFormHalfGenerator.halfGenerator Q hQ).toLinearMap.comp
    (ScalarFormHilbert.equiv Q hQ).symm.toLinearMap
  have hn (w : Q.1) : ‖D w‖ = Real.sqrt (Q.2 w w) :=
    ScalarFormHalfGenerator.halfGenerator_norm Q hQ w
  rw [← hn, map_sum]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => hn (u i))

/-- Subtraction also obeys the form triangle inequality. -/
theorem sqrt_energy_sub_le (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (u v : Q.1) :
    Real.sqrt (Q.2 (u - v) (u - v)) ≤ Real.sqrt (Q.2 u u) + Real.sqrt (Q.2 v v) := by
  let D := (ScalarFormHalfGenerator.halfGenerator Q hQ).toLinearMap.comp
    (ScalarFormHilbert.equiv Q hQ).symm.toLinearMap
  have hn (w : Q.1) : ‖D w‖ = Real.sqrt (Q.2 w w) :=
    ScalarFormHalfGenerator.halfGenerator_norm Q hQ w
  calc
    _ = ‖D (u - v)‖ := (hn _).symm
    _ = ‖D u - D v‖ := congrArg norm (map_sub D u v)
    _ ≤ ‖D u‖ + ‖D v‖ := norm_sub_le _ _
    _ = _ := by rw [hn, hn]

end Riesz2.SummedWeakEquation
