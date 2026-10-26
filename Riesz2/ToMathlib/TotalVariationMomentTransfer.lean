/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.WeightedTestVariation
public import Riesz2.ToMathlib.WeakMomentTruncation
public import Riesz1.ToMathlib.TotalVariation.VarianceTransfer

/-!
# Moment transfer for the event-supremum distance

The event supremum agrees with the companion library's real distance
on probabilities. This bridge reuses its bounded-test inequality.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Riesz2

/-- The event supremum and the companion half-variation norm have the same
normalization on probabilities. -/
theorem totalVariation_eq_ofReal_riesz1
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariation μ ν = ENNReal.ofReal (Riesz1.totalVariation μ ν) := by
  have hupper : totalVariation μ ν ≤ ENNReal.ofReal (Riesz1.totalVariation μ ν) := by
    apply iSup_le
    rintro ⟨A, hA⟩
    rw [event_difference_eq_ofReal_abs _ _ (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (Riesz1.abs_measureReal_sub_le_totalVariation μ ν hA)
  have hfinite : totalVariation μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  apply le_antisymm hupper
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
  apply (Riesz1.isLUB_abs_measureReal_sub_etvDist μ ν).2
  rintro _ ⟨A, hA, rfl⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
  have he := le_iSup (fun A : {A : Set Ω // MeasurableSet A} =>
    (μ A.val - ν A.val) + (ν A.val - μ A.val)) ⟨A, hA⟩
  change ENNReal.ofReal |(μ A).toReal - (ν A).toReal| ≤ totalVariation μ ν
  rw [← event_difference_eq_ofReal_abs _ _ (measure_ne_top _ _) (measure_ne_top _ _)]
  exact he

/-- Event-supremum convergence implies convergence of every bounded measurable
real test, on an arbitrary measurable space. -/
theorem integral_tendsto_of_totalVariation
    {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω) (ν : Measure Ω)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (htv : Tendsto (fun n => totalVariation (μ n) ν) atTop (𝓝 0))
    (f : Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hreal : Tendsto (fun n => Riesz1.totalVariation (μ n) ν) atTop (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp htv
    simpa only [Function.comp_def, totalVariation_eq_ofReal_riesz1,
      ENNReal.toReal_ofReal (Riesz1.totalVariation_nonneg _ _), ENNReal.toReal_zero] using ht
  have he : Tendsto (fun n => |(∫ x, f x ∂μ n) - ∫ x, f x ∂ν|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun n => Riesz1.abs_integral_sub_le_of_abs_le (μ n) ν hf hB hb)
    simpa only [mul_zero] using hreal.const_mul (2 * B)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using he)

/-- Convergence in event total variation implies weak convergence of real
probability measures. -/
theorem probabilityMeasure_tendsto_of_totalVariation
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (htv : Tendsto (fun n => totalVariation (μ n).toMeasure ν.toMeasure) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply integral_tendsto_of_totalVariation (fun n => (μ n).toMeasure) ν.toMeasure htv
    f f.continuous.measurable ‖f‖ (norm_nonneg _)
  intro x
  simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x

end Riesz2
