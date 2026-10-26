/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Lp contraction of integration against a probability kernel

This is conditional Jensen for the explicit fibre integral. It does not
choose a conditional-expectation representative.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Riesz2

/-- Integrating a measurable scalar test against a Markov kernel contracts
its `Lᵖ` seminorm, for every finite real `p ≥ 1`. -/
theorem eLpNorm_integral_kernel_le {B F : Type*} [MeasurableSpace B] [MeasurableSpace F]
    (μ : Measure B) [SFinite μ] (κ : Kernel B F) [IsMarkovKernel κ]
    {f : B × F → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ y, f (x, y) ∂κ x) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal p) (μ ⊗ₘ κ) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have ht : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hg := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ht hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ht hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp0.le]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  rw [Measure.lintegral_compProd (hf.enorm.pow_const p)]
  apply lintegral_mono
  intro x
  have hfx : Measurable (fun y => f (x, y)) := hf.comp measurable_prodMk_left
  have h := (enorm_integral_le_lintegral_enorm (fun y => f (x, y))).trans
    ((lintegral_enorm_le_eLpNorm_one).trans
      (eLpNorm_le_eLpNorm_of_exponent_le (μ := κ x) (f := fun y => f (x, y)) hpE))
  have hh := ENNReal.rpow_le_rpow h hp0.le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ht hfx.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul,
    one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at hh
  exact hh

end Riesz2
