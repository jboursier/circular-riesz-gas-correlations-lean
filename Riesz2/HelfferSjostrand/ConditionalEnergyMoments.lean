/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineFibreDisintegration

/-!
# The point-fibre case of conditional energy moments

On an exterior simplex with one gap the intrinsic measure is a point mass.
Normalization preserves it for every finite real energy. The centered
exponential moment is exactly one, and every inverse moment is its point
value. These are the point-fibre cases of Appendix A.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.ConditionalEnergyMoments

private theorem normalizedMeasure_dirac {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (a : A) (w : A → ℝ≥0∞) (hw0 : w a ≠ 0) (hwt : w a ≠ ∞) :
    AffineFibre.normalizedMeasure (Measure.dirac a) w
      (by simpa using hw0) (by simpa using hwt) = Measure.dirac a := by
  unfold AffineFibre.normalizedMeasure
  have he : AffineFibre.normalizedDensity (Measure.dirac a) w
      (by simpa using hw0) (by simpa using hwt) =ᵐ[Measure.dirac a] fun _ => 1 := by
    filter_upwards [ae_eq_dirac (AffineFibre.normalizedDensity (Measure.dirac a) w
      (by simpa using hw0) (by simpa using hwt))] with x hx
    exact hx.trans (by
      simpa only [AffineFibre.normalizedDensity, lintegral_dirac, Function.const_apply] using
        ENNReal.inv_mul_cancel hw0 hwt)
  rw [withDensity_congr_ae he]
  exact withDensity_one

/-- See Appendix A of the paper, the one-exterior-gap moment identities. This is
the actual intrinsic simplex conditional law, for any real energy on it.
Its centered exponential moment attains the factor `2 ^ 0 = 1`. -/
theorem singleExterior_moments {L : ℝ} (hL : 0 < L)
    (U : EuclideanSpace ℝ (Fin 1) → ℝ) :
    let y₀ := AffineSimplex.chart 0 L 0
    let ρ := AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume 0 L)
      (fun y => ENNReal.ofReal (Real.exp (-U y)))
      (by rw [AffineSimplex.simplexVolume_zero hL, lintegral_dirac]
          exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
      (by rw [AffineSimplex.simplexVolume_zero hL, lintegral_dirac]
          exact ENNReal.ofReal_ne_top)
    ρ = Measure.dirac y₀ ∧
      Integrable U ρ ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp ((U y - U y₀) / 2)) ∂ρ) = 1 ∧
      ∀ s : ℝ, ∫⁻ y, ENNReal.ofReal ((y 0) ^ (-s - 2)) ∂ρ =
        ENNReal.ofReal (L ^ (-s - 2)) := by
  intro y₀ ρ
  have hr : ρ = Measure.dirac y₀ := by
    dsimp only [ρ]
    simp only [AffineSimplex.simplexVolume_zero hL]
    exact normalizedMeasure_dirac y₀ (fun y => ENNReal.ofReal (Real.exp (-U y)))
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [hr]
    exact integrable_dirac (by finiteness)
  · rw [hr, lintegral_dirac]
    simp
  · intro s
    rw [hr, lintegral_dirac]
    have hy : y₀ 0 = L := by simp [y₀, AffineSimplex.chart]
    rw [hy]

end Riesz2.ConditionalEnergyMoments
