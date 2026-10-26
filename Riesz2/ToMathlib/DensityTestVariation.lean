/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.TotalVariation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Density bounds for measurable test functions

Real density differences bound integrals of measurable tests and the supremum over events. All signed integrals have explicit integrability premises.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2

/-- Integrating a real density uses its actual nonnegative values. -/
lemma integral_ofReal_density {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (H : α → ℝ) :
    (∫ x, H x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, f x * H x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

/-- A density difference controls any integrable test, including unbounded tests. -/
lemma ofReal_abs_integral_sub_density_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f g H : α → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hHf : Integrable H (μ.withDensity (fun x => ENNReal.ofReal (f x))))
    (hHg : Integrable H (μ.withDensity (fun x => ENNReal.ofReal (g x)))) :
    ENNReal.ofReal |(∫ x, H x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) -
      (∫ x, H x ∂μ.withDensity (fun x => ENNReal.ofReal (g x)))| ≤
        ∫⁻ x, ENNReal.ofReal (|H x| * |f x - g x|) ∂μ := by
  have hi (u : α → ℝ) (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x)
      (h : Integrable H (μ.withDensity (fun x => ENNReal.ofReal (u x)))) :
      Integrable (fun x => u x * H x) μ := by
    have := (integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp h
    simpa only [ENNReal.toReal_ofReal (hu0 _), smul_eq_mul] using this
  rw [integral_ofReal_density μ hf hf0, integral_ofReal_density μ hg hg0,
    ← integral_sub (hi f hf hf0 hHf) (hi g hg hg0 hHg)]
  have h := enorm_integral_le_lintegral_enorm (μ := μ) (fun x => f x * H x - g x * H x)
  simpa only [← sub_mul, enorm_mul, Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), mul_comm] using h

/-- The event distance is bounded by the full L¹ density difference.
The bound is sufficient for convergence and does not assert a normalization identity. -/
lemma totalVariation_density_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f g : α → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x)))] :
    totalVariation (μ.withDensity (fun x => ENNReal.ofReal (f x)))
      (μ.withDensity (fun x => ENNReal.ofReal (g x))) ≤
      ∫⁻ x, ENNReal.ofReal |f x - g x| ∂μ := by
  apply iSup_le
  rintro ⟨A, hA⟩
  let H : α → ℝ := A.indicator (fun _ => 1)
  have hH : Measurable H := measurable_const.indicator hA
  have hHb : ∀ x, |H x| ≤ 1 := by intro x; by_cases hx : x ∈ A <;> simp [H, hx]
  have hi (ν : Measure α) [IsFiniteMeasure ν] : Integrable H ν :=
    Integrable.of_bound hH.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hHb x)
  have hb := ofReal_abs_integral_sub_density_le μ hf hf0 hg hg0 (hi _) (hi _)
  have hInt (ν : Measure α) [IsFiniteMeasure ν] : ∫ x, H x ∂ν = (ν A).toReal := by
    simp [H, integral_indicator hA, Measure.real]
  rw [hInt, hInt] at hb
  have hevent (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
      (a - b) + (b - a) = ENNReal.ofReal |a.toReal - b.toReal| := by
    rcases le_total a b with h | h
    · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hb h))]
      exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb tsub_le_self)).symm.trans
        (congrArg ENNReal.ofReal (ENNReal.toReal_sub_of_le h hb))
    · rw [tsub_eq_zero_of_le h, add_zero,
        abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono ha h))]
      exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ha tsub_le_self)).symm.trans
        (congrArg ENNReal.ofReal (ENNReal.toReal_sub_of_le h ha))
  rw [hevent _ _ (measure_ne_top _ _) (measure_ne_top _ _)]
  refine hb.trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
  nlinarith [hHb x, abs_nonneg (f x - g x)]

/-- Uniformly bounded measurable multipliers of an integrable weight have a
common density-difference bound. The supremum is extended-valued, so no boundedness
or integrability failure can turn the distance into a junk value. -/
lemma weightedTestSup_density_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f g w : α → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hwf : Integrable w (μ.withDensity (fun x => ENNReal.ofReal (f x))))
    (hwg : Integrable w (μ.withDensity (fun x => ENNReal.ofReal (g x)))) :
    (⨆ F : {F : α → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
      ENNReal.ofReal |(∫ x, w x * F.val x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) -
        (∫ x, w x * F.val x ∂μ.withDensity (fun x => ENNReal.ofReal (g x)))|) ≤
      ∫⁻ x, ENNReal.ofReal (|w x| * |f x - g x|) ∂μ := by
  apply iSup_le
  intro F
  have hb : ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)), ‖F.val x‖ ≤ 1 :=
    ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using F.property.2 x
  have hb' : ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (g x)), ‖F.val x‖ ≤ 1 :=
    ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using F.property.2 x
  refine (ofReal_abs_integral_sub_density_le μ hf hf0 hg hg0
    (hwf.mul_bdd F.property.1.aestronglyMeasurable hb)
    (hwg.mul_bdd F.property.1.aestronglyMeasurable hb')).trans
      (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
  rw [abs_mul]
  calc
    |w x| * |F.val x| * |f x - g x| ≤ |w x| * 1 * |f x - g x| := by
      gcongr; exact F.property.2 x
    _ = _ := by ring

end Riesz2
