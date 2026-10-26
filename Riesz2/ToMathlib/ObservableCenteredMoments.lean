/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.DerivativeSup
public import Riesz2.ToMathlib.LipschitzDerivativeBound
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic

/-!
# Centered observables of a positive variable

For an observable `ξ` with bounded almost everywhere derivative `U`, the centered function
`x ↦ ξ x - ξ 1` satisfies `|ξ x - ξ 1| ≤ U |x - 1|`. If `g` is a positive random variable with
finite second moment, then `(ξ ∘ g - ξ 1)²` is integrable, and its integral is at most
`U² (2 E g² + 2)`. The product of two such centered observables has second moment at most
`U² V² (4 E g₁⁴ + 4 E g₂⁴ + 8)`. These are the moment inputs of the covariance estimate.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz2.CenteredObservable

/-- The square of `x - 1` is at most `2 x² + 2`. -/
theorem sq_sub_one_le (x : ℝ) : (x - 1) ^ 2 ≤ 2 * x ^ 2 + 2 := by
  nlinarith [sq_nonneg (x + 1)]

/-- The fourth power of `x - 1` is at most `8 x⁴ + 8`. -/
theorem pow_four_sub_one_le (x : ℝ) : (x - 1) ^ 4 ≤ 8 * x ^ 4 + 8 := by
  have h1 : (x - 1) ^ 2 ≤ 2 * x ^ 2 + 2 := sq_sub_one_le x
  have h2 : (x - 1) ^ 4 = ((x - 1) ^ 2) ^ 2 := by ring
  rw [h2]
  have h3 : ((x - 1) ^ 2) ^ 2 ≤ (2 * x ^ 2 + 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (x ^ 2 - 1)]

/-- The product of two reals has square at most half the sum of their fourth powers. -/
theorem sq_mul_le_half_pow_four (a b : ℝ) : (a * b) ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

theorem rpow_four_eq (x : ℝ) : x ^ (4 : ℝ) = x ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The Lipschitz constant of an observable is the essential supremum of its derivative. -/
theorem abs_observable_sub_le (ξ : GapObservable) (x y : ℝ) :
    |ξ.val.1 y - ξ.val.1 x| ≤ derivativeSup ξ * |y - x| := by
  obtain ⟨⟨L, hL⟩, hm, hd, hfin⟩ := ξ.property
  exact LipschitzDerivative.abs_sub_le_of_eLpNorm_top_hasDerivAt hL hm hfin hd x y

/-- The observable is continuous, being Lipschitz. -/
theorem continuous_observable (ξ : GapObservable) : Continuous ξ.val.1 := by
  obtain ⟨⟨L, hL⟩, -⟩ := ξ.property
  exact hL.continuous

/-- The derivative of an observable is almost everywhere bounded by its essential supremum. -/
theorem ae_abs_derivative_le (ξ : GapObservable) :
    ∀ᵐ x ∂(volume : Measure ℝ), |ξ.val.2 x| ≤ derivativeSup ξ := by
  obtain ⟨-, hm, -, hfin⟩ := ξ.property
  have h := enorm_ae_le_eLpNormEssSup ξ.val.2 volume
  rw [← eLpNorm_exponent_top hm] at h
  filter_upwards [h] with x hx
  unfold derivativeSup
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin.ne, ← Real.enorm_eq_ofReal_abs]
  exact hx

/-- Pointwise, the squared centered observable is at most `U² (x - 1)²`. -/
theorem sq_observable_sub_le (ξ : GapObservable) (x : ℝ) :
    (ξ.val.1 x - ξ.val.1 1) ^ 2 ≤ derivativeSup ξ ^ 2 * (x - 1) ^ 2 := by
  have h1 := abs_observable_sub_le ξ 1 x
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs, mul_pow, sq_abs] at hsq
  exact hsq

/-- The centered observable of a positive variable has integrable square, and its second
moment is at most `U² (2 E g² + 2)`. -/
theorem integrable_sq_sub_and_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ξ : GapObservable) {g : Ω → ℝ} (hg : Measurable g)
    (hg2 : Integrable (fun ω => g ω ^ (2 : ℝ)) μ) :
    Integrable (fun ω => (ξ.val.1 (g ω) - ξ.val.1 1) ^ 2) μ ∧
      ∫ ω, (ξ.val.1 (g ω) - ξ.val.1 1) ^ 2 ∂μ ≤
        derivativeSup ξ ^ 2 * (2 * ∫ ω, g ω ^ (2 : ℝ) ∂μ + 2) := by
  have hmeas : Measurable (fun ω => (ξ.val.1 (g ω) - ξ.val.1 1) ^ 2) :=
    (((continuous_observable ξ).measurable.comp hg).sub_const _).pow_const 2
  have hB : Integrable (fun ω => derivativeSup ξ ^ 2 * (2 * g ω ^ (2 : ℝ) + 2)) μ :=
    ((hg2.const_mul 2).add (integrable_const 2)).const_mul _
  have hpt : ∀ ω, (ξ.val.1 (g ω) - ξ.val.1 1) ^ 2 ≤
      derivativeSup ξ ^ 2 * (2 * g ω ^ (2 : ℝ) + 2) := by
    intro ω
    rw [Real.rpow_two]
    exact (sq_observable_sub_le ξ (g ω)).trans
      (mul_le_mul_of_nonneg_left (by linarith [sq_sub_one_le (g ω)]) (sq_nonneg _))
  have hdom : ∀ ω, ‖(ξ.val.1 (g ω) - ξ.val.1 1) ^ 2‖ ≤
      derivativeSup ξ ^ 2 * (2 * g ω ^ (2 : ℝ) + 2) := fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨Integrable.mono' hB hmeas.aestronglyMeasurable (ae_of_all _ hdom), ?_⟩
  calc
    ∫ ω, (ξ.val.1 (g ω) - ξ.val.1 1) ^ 2 ∂μ ≤
        ∫ ω, derivativeSup ξ ^ 2 * (2 * g ω ^ (2 : ℝ) + 2) ∂μ :=
      integral_mono (Integrable.mono' hB hmeas.aestronglyMeasurable (ae_of_all _ hdom)) hB hpt
    _ = derivativeSup ξ ^ 2 * (2 * ∫ ω, g ω ^ (2 : ℝ) ∂μ + 2) := by
      rw [integral_const_mul, integral_add (hg2.const_mul 2) (integrable_const 2),
        integral_const_mul, integral_const]
      simp

/-- The product of two centered observables, of positive variables `g₁` and `g₂` with finite
fourth moments, has integrable square with integral at most
`U² V² (4 E g₁⁴ + 4 E g₂⁴ + 8)`. -/
theorem integrable_sq_mul_and_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ξ χ : GapObservable) {g₁ g₂ : Ω → ℝ} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) (h₁ : Integrable (fun ω => g₁ ω ^ (4 : ℝ)) μ)
    (h₂ : Integrable (fun ω => g₂ ω ^ (4 : ℝ)) μ) :
    Integrable (fun ω => ((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2) μ ∧
      ∫ ω, ((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2 ∂μ ≤
        derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
          (4 * ∫ ω, g₁ ω ^ (4 : ℝ) ∂μ + 4 * ∫ ω, g₂ ω ^ (4 : ℝ) ∂μ + 8) := by
  have hmeas : Measurable (fun ω =>
      ((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2) :=
    ((((continuous_observable ξ).measurable.comp hg₁).sub_const _).mul
      (((continuous_observable χ).measurable.comp hg₂).sub_const _)).pow_const 2
  have hB : Integrable (fun ω => derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
      (4 * g₁ ω ^ (4 : ℝ) + 4 * g₂ ω ^ (4 : ℝ) + 8)) μ :=
    (((h₁.const_mul 4).add (h₂.const_mul 4)).add (integrable_const 8)).const_mul _
  have hpt : ∀ ω, ((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2 ≤
      derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
        (4 * g₁ ω ^ (4 : ℝ) + 4 * g₂ ω ^ (4 : ℝ) + 8) := by
    intro ω
    rw [rpow_four_eq, rpow_four_eq]
    have hA := sq_observable_sub_le ξ (g₁ ω)
    have hB' := sq_observable_sub_le χ (g₂ ω)
    have hprod : ((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2 =
        (ξ.val.1 (g₁ ω) - ξ.val.1 1) ^ 2 * (χ.val.1 (g₂ ω) - χ.val.1 1) ^ 2 := by ring
    rw [hprod]
    have hC : 0 ≤ derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 := by positivity
    calc
      (ξ.val.1 (g₁ ω) - ξ.val.1 1) ^ 2 * (χ.val.1 (g₂ ω) - χ.val.1 1) ^ 2
          ≤ (derivativeSup ξ ^ 2 * (g₁ ω - 1) ^ 2) * (derivativeSup χ ^ 2 * (g₂ ω - 1) ^ 2) :=
        mul_le_mul hA hB' (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 * ((g₁ ω - 1) * (g₂ ω - 1)) ^ 2 := by ring
      _ ≤ derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
          (((g₁ ω - 1) ^ 4 + (g₂ ω - 1) ^ 4) / 2) :=
        mul_le_mul_of_nonneg_left (sq_mul_le_half_pow_four _ _) hC
      _ ≤ derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
          (4 * g₁ ω ^ 4 + 4 * g₂ ω ^ 4 + 8) := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith [pow_four_sub_one_le (g₁ ω), pow_four_sub_one_le (g₂ ω)]
  have hdom : ∀ ω, ‖((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2‖ ≤
      derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
        (4 * g₁ ω ^ (4 : ℝ) + 4 * g₂ ω ^ (4 : ℝ) + 8) := fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨Integrable.mono' hB hmeas.aestronglyMeasurable (ae_of_all _ hdom), ?_⟩
  calc
    ∫ ω, ((ξ.val.1 (g₁ ω) - ξ.val.1 1) * (χ.val.1 (g₂ ω) - χ.val.1 1)) ^ 2 ∂μ ≤
        ∫ ω, derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
          (4 * g₁ ω ^ (4 : ℝ) + 4 * g₂ ω ^ (4 : ℝ) + 8) ∂μ :=
      integral_mono (Integrable.mono' hB hmeas.aestronglyMeasurable (ae_of_all _ hdom)) hB hpt
    _ = derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
          (4 * ∫ ω, g₁ ω ^ (4 : ℝ) ∂μ + 4 * ∫ ω, g₂ ω ^ (4 : ℝ) ∂μ + 8) := by
      have hi1 : Integrable (fun ω => 4 * g₁ ω ^ (4 : ℝ)) μ := h₁.const_mul 4
      have hi2 : Integrable (fun ω => 4 * g₂ ω ^ (4 : ℝ)) μ := h₂.const_mul 4
      have hi12 : Integrable (fun ω => 4 * g₁ ω ^ (4 : ℝ) + 4 * g₂ ω ^ (4 : ℝ)) μ := hi1.add hi2
      rw [integral_const_mul, integral_add hi12 (integrable_const 8),
        integral_add hi1 hi2, integral_const_mul, integral_const_mul, integral_const]
      simp

end Riesz2.CenteredObservable
