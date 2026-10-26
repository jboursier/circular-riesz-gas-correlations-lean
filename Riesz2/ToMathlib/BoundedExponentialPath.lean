/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Tactic

/-!
# Calculus of bounded exponential changes of measure

A bounded measurable score gives a smooth path of normalized expectations
for bounded measurable observables. The path uses Mathlib's existing
`Measure.tilted`. Normalization and all covariance integrabilities are proved.
-/

public section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal ContDiff

namespace Riesz2.BoundedExponentialPath

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {D G : Ω → ℝ} {B A : ℝ}

/-- Bounded exponential weights times bounded tests are integrable. -/
theorem weighted_integrable [IsFiniteMeasure μ]
    (hD : Measurable D) (hG : Measurable G) (_hB : 0 ≤ B) (_hA : 0 ≤ A)
    (hDb : ∀ x, |D x| ≤ B) (hGb : ∀ x, |G x| ≤ A) (t : ℝ) :
    Integrable (fun x => Real.exp (t * D x) * G x) μ := by
  apply (integrable_const (Real.exp (|t| * B) * A)).mono'
    ((hD.const_mul t).exp.mul hG).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hGb x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  calc
    t * D x ≤ |t * D x| := le_abs_self _
    _ = |t| * |D x| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hDb x) (abs_nonneg _)

/-- Differentiation of a bounded weighted exponential integral. -/
theorem hasDerivAt_weighted_integral [IsFiniteMeasure μ]
    (hD : Measurable D) (hG : Measurable G) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hDb : ∀ x, |D x| ≤ B) (hGb : ∀ x, |G x| ≤ A) (t : ℝ) :
    HasDerivAt (fun u => ∫ x, Real.exp (u * D x) * G x ∂μ)
      (∫ x, Real.exp (t * D x) * (D x * G x) ∂μ) t := by
  let s := Ioo (t - 1) (t + 1)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun u x => Real.exp (u * D x) * (D x * G x))
    (bound := fun _ => Real.exp ((|t| + 1) * B) * (B * A))
    (s := s) (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun u =>
      ((hD.const_mul u).exp.mul hG).aestronglyMeasurable)
    (weighted_integrable hD hG hB hA hDb hGb t)
    (((hD.const_mul t).exp.mul (hD.mul hG)).aestronglyMeasurable)
    ?_ (integrable_const _) ?_).2
  · apply ae_of_all
    intro x u hu
    have hu' : |u| ≤ |t| + 1 := by
      have htu : |u - t| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      calc
        |u| = |(u - t) + t| := by congr 1; ring
        _ ≤ |u - t| + |t| := abs_add_le _ _
        _ ≤ |t| + 1 := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    apply mul_le_mul _ (mul_le_mul (hDb x) (hGb x) (abs_nonneg _) hB)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    calc
      u * D x ≤ |u * D x| := le_abs_self _
      _ = |u| * |D x| := abs_mul _ _
      _ ≤ (|t| + 1) * B := mul_le_mul hu' (hDb x) (abs_nonneg _) (by positivity)
  · apply ae_of_all
    intro x u _
    convert (((hasDerivAt_id u).mul_const (D x)).exp.mul_const (G x)) using 1 <;> simp only [id_eq, Pi.mul_apply, one_mul]; ring

/-- Smoothness holds even when the test itself is merely measurable. -/
theorem smooth_weighted_integral [IsFiniteMeasure μ]
    (hD : Measurable D) (hG : Measurable G) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hDb : ∀ x, |D x| ≤ B) (hGb : ∀ x, |G x| ≤ A) :
    ContDiff ℝ ∞ (fun t => ∫ x, Real.exp (t * D x) * G x ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing G A with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_weighted_integral hD hG hB hA hDb hGb t).continuousAt)
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_weighted_integral hD hG hB hA hDb hGb t).differentiableAt,
      by simp, ?_⟩
    have he : deriv (fun t => ∫ x, Real.exp (t * D x) * G x ∂μ) =
        fun t => ∫ x, Real.exp (t * D x) * (D x * G x) ∂μ :=
      funext fun t => (hasDerivAt_weighted_integral hD hG hB hA hDb hGb t).deriv
    rw [he]
    exact ih (hD.mul hG) (mul_nonneg hB hA)
      (fun x => by rw [abs_mul]; exact mul_le_mul (hDb x) (hGb x) (abs_nonneg _) hB)

/-- A bounded score has a strictly positive normalizer for every real
parameter, including outside the interpolation interval. -/
theorem normalizer_pos [IsProbabilityMeasure μ]
    (hD : Measurable D) (hB : 0 ≤ B) (hDb : ∀ x, |D x| ≤ B) (t : ℝ) :
    0 < ∫ x, Real.exp (t * D x) ∂μ := by
  apply integral_exp_pos
  simpa only [mul_one] using
    weighted_integrable (μ := μ) (G := fun _ => (1 : ℝ)) hD measurable_const hB (show (0 : ℝ) ≤ 1 by norm_num)
      hDb (fun _ => by norm_num) t

/-- Exact normalized expectation formula for the existing exponential tilt. -/
theorem integral_eq_ratio (μ : Measure Ω) (D G : Ω → ℝ) (t : ℝ) :
    ∫ x, G x ∂μ.tilted (fun x => t * D x) =
      (∫ x, Real.exp (t * D x) * G x ∂μ) / (∫ x, Real.exp (t * D x) ∂μ) := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_eq_mul_inv]
  simp_rw [mul_right_comm (Real.exp (t * D _)) _ (G _)]
  rw [integral_mul_const]

/-- The expectation path is smooth on the entire real line. -/
theorem smooth_expectation [IsProbabilityMeasure μ]
    (hD : Measurable D) (hG : Measurable G) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hDb : ∀ x, |D x| ≤ B) (hGb : ∀ x, |G x| ≤ A) :
    ContDiff ℝ ∞ (fun t => ∫ x, G x ∂μ.tilted (fun x => t * D x)) := by
  simp_rw [integral_eq_ratio]
  apply (smooth_weighted_integral (μ := μ) hD hG hB hA hDb hGb).div
  · simpa only [mul_one] using smooth_weighted_integral (μ := μ) (G := fun _ => (1 : ℝ)) hD measurable_const hB
      (show (0 : ℝ) ≤ 1 by norm_num) hDb (fun _ => by norm_num)
  · intro t
    exact (normalizer_pos hD hB hDb t).ne'

/-- Derivative of a normalized expectation is its covariance with the score. -/
theorem hasDerivAt_expectation [IsProbabilityMeasure μ]
    (hD : Measurable D) (hG : Measurable G) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hDb : ∀ x, |D x| ≤ B) (hGb : ∀ x, |G x| ≤ A) (t : ℝ) :
    HasDerivAt (fun u => ∫ x, G x ∂μ.tilted (fun x => u * D x))
      (covariance G D (μ.tilted (fun x => t * D x))) t := by
  have hw : Integrable (fun x => Real.exp (t * D x)) μ := by
    simpa only [mul_one] using weighted_integrable (μ := μ) (G := fun _ => (1 : ℝ)) hD measurable_const hB
      (show (0 : ℝ) ≤ 1 by norm_num) hDb (fun _ => by norm_num) t
  have := isProbabilityMeasure_tilted hw
  have hG2 : MemLp G 2 (μ.tilted (fun x => t * D x)) :=
    MemLp.of_bound hG.aestronglyMeasurable A (ae_of_all _ hGb)
  have hD2 : MemLp D 2 (μ.tilted (fun x => t * D x)) :=
    MemLp.of_bound hD.aestronglyMeasurable B (ae_of_all _ hDb)
  have hnum := hasDerivAt_weighted_integral (μ := μ) hD hG hB hA hDb hGb t
  have hden : HasDerivAt (fun u => ∫ x, Real.exp (u * D x) ∂μ)
      (∫ x, Real.exp (t * D x) * D x ∂μ) t := by
    simpa only [mul_one] using hasDerivAt_weighted_integral (μ := μ) (G := fun _ => (1 : ℝ)) hD measurable_const hB
      (show (0 : ℝ) ≤ 1 by norm_num) hDb (fun _ => by norm_num) t
  simp_rw [integral_eq_ratio]
  convert hnum.div hden (normalizer_pos hD hB hDb t).ne' using 1
  rw [covariance_eq_sub hG2 hD2]
  simp_rw [integral_eq_ratio]
  simp only [Pi.mul_apply]
  have he : (∫ x, Real.exp (t * D x) * (G x * D x) ∂μ) =
      ∫ x, Real.exp (t * D x) * (D x * G x) ∂μ := by congr 1; funext x; ring
  rw [he]
  field_simp

/-- Integrated covariance identity for any bounded exponential path.
This is the measure-theoretic calculus used in Lemma 6.1, before identifying the physical energy difference. -/
theorem integrated_covariance [IsProbabilityMeasure μ]
    (hD : Measurable D) (hG : Measurable G) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hDb : ∀ x, |D x| ≤ B) (hGb : ∀ x, |G x| ≤ A) (a b : ℝ) :
    IntervalIntegrable (fun t => covariance G D (μ.tilted (fun x => t * D x))) volume a b ∧
    (∫ x, G x ∂μ.tilted (fun x => b * D x)) -
        (∫ x, G x ∂μ.tilted (fun x => a * D x)) =
      ∫ t in a..b, covariance G D (μ.tilted (fun x => t * D x)) := by
  have hs := smooth_expectation (μ := μ) hD hG hB hA hDb hGb
  have he : (fun t => covariance G D (μ.tilted (fun x => t * D x))) =
      deriv (fun t => ∫ x, G x ∂μ.tilted (fun x => t * D x)) :=
    funext fun t => (hasDerivAt_expectation hD hG hB hA hDb hGb t).deriv.symm
  have hi : IntervalIntegrable (fun t => covariance G D (μ.tilted (fun x => t * D x))) volume a b := by
    rw [he]
    exact (hs.continuous_deriv (by simp)).intervalIntegrable _ _
  exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_expectation hD hG hB hA hDb hGb t) hi).symm⟩

/-- The normalized geometric Gibbs path is an exponential tilt of its
initial endpoint. This identity supplies the positive covariance sign when
`D = Ky - Kz`. Integrability of the initial weight is explicit. -/
theorem gibbs_path_eq_tilted (μ : Measure Ω) (P Ky Kz : Ω → ℝ) (β t : ℝ)
    (h0 : Integrable (fun x => Real.exp (-β * (P x + Ky x))) μ) :
    (μ.tilted (fun x => -β * (P x + Ky x))).tilted (fun x => β * t * (Ky x - Kz x)) =
      μ.tilted (fun x => -β * (P x + (1 - t) * Ky x + t * Kz x)) := by
  rw [tilted_tilted h0]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

end Riesz2.BoundedExponentialPath
