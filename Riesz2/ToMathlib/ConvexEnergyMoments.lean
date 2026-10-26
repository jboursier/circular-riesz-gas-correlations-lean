/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Riesz1.ToMathlib.LogConcave.Moments
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Analysis.Convex.Function

/-!
# Convex energy moments

Internal analytic ingredients of Appendix A. Contraction toward
a zero of a convex energy controls the ratio of its half-temperature and
full-temperature partition functions by `2 ^ dim`. Normalization uses
`AffineFibre.normalizedMeasure`, with finite positive mass required
explicitly. In particular these statements include dimension zero.

The positive-moment bound uses the companion library's exponential moment theorem.
Applications require a minimizer and a bound on its energy.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.ConvexEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A finite positive factor in the Gibbs weight cancels under the landed
normalization. This is the normalization bridge for subtracting a minimum. -/
theorem normalizedMeasure_const_mul {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {w : A → ℝ≥0∞} (hw : Measurable w)
    (h0 : (∫⁻ y, w y ∂μ) ≠ 0) (ht : (∫⁻ y, w y ∂μ) ≠ ∞)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    AffineFibre.normalizedMeasure μ (fun y => c * w y)
      (by rw [lintegral_const_mul _ hw]; exact mul_ne_zero hc0 h0)
      (by rw [lintegral_const_mul _ hw]; exact ENNReal.mul_ne_top hct ht) =
        AffineFibre.normalizedMeasure μ w h0 ht := by
  unfold AffineFibre.normalizedMeasure
  congr 1
  funext y
  simp only [AffineFibre.normalizedDensity, lintegral_const_mul _ hw]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  calc
    c⁻¹ * (∫⁻ z, w z ∂μ)⁻¹ * (c * w y) =
        (c⁻¹ * c) * ((∫⁻ z, w z ∂μ)⁻¹ * w y) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- Change of variables for a contraction of ratio one half, with its exact
dimension factor. No finiteness or measurability of the test is needed. -/
theorem lintegral_half_affine (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (c : E) :
    ∫⁻ y, f ((2 : ℝ)⁻¹ • y + c) ∂μ =
      (2 : ℝ≥0∞) ^ Module.finrank ℝ E * ∫⁻ y, f y ∂μ := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 ((2 : ℝ)⁻¹) (by norm_num))).toMeasurableEquiv
  have he : ∫⁻ y, f ((2 : ℝ)⁻¹ • y + c) ∂μ =
      ∫⁻ z, f (z + c) ∂μ.map (fun y : E => (2 : ℝ)⁻¹ • y) :=
    (lintegral_map_equiv (fun z => f (z + c)) e).symm
  rw [he, Measure.map_addHaar_smul μ (by norm_num), lintegral_smul_measure,
    lintegral_add_right_eq_self]
  congr 1
  simp [abs_of_nonneg, ENNReal.ofReal_pow]

/-- Internal ingredient of Appendix A: convexity and a zero at
the contraction center bound the half-temperature partition function. -/
theorem partition_half_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {Q : Set E} {w : E → ℝ} (hQ : MeasurableSet Q) (hw : ConvexOn ℝ Q w)
    {y₀ : E} (hy₀ : y₀ ∈ Q) (hzero : w y₀ = 0) :
    ∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y / 2)) ∂μ ≤
      (2 : ℝ≥0∞) ^ Module.finrank ℝ E *
        ∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ := by
  classical
  let f := Q.indicator (fun y => ENNReal.ofReal (Real.exp (-w y)))
  have hbound (y : E) : Q.indicator (fun y => ENNReal.ofReal (Real.exp (-w y / 2))) y ≤
      f ((2 : ℝ)⁻¹ • y + (2 : ℝ)⁻¹ • y₀) := by
    by_cases hy : y ∈ Q
    · have hq := hw.1 hy hy₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)
      have hconv := hw.2 hy hy₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)
      rw [hzero, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at hconv
      rw [indicator_of_mem hy, show f ((2 : ℝ)⁻¹ • y + (2 : ℝ)⁻¹ • y₀) =
          ENNReal.ofReal (Real.exp (-w ((2 : ℝ)⁻¹ • y + (2 : ℝ)⁻¹ • y₀)))
        from indicator_of_mem hq _]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith
    · rw [indicator_of_notMem hy]
      exact bot_le
  calc
    _ = ∫⁻ y, Q.indicator (fun y => ENNReal.ofReal (Real.exp (-w y / 2))) y ∂μ := by
      rw [lintegral_indicator]
      exact hQ
    _ ≤ ∫⁻ y, f ((2 : ℝ)⁻¹ • y + (2 : ℝ)⁻¹ • y₀) ∂μ := lintegral_mono hbound
    _ = _ := by
      rw [lintegral_half_affine, show (∫⁻ y, f y ∂μ) =
        ∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ from
          lintegral_indicator hQ _]

/-- Internal ingredient of Appendix A: the normalized exponential
energy moment is bounded by `2 ^ dim`, as an extended integral. -/
theorem exponential_moment_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {Q : Set E} (hQ : MeasurableSet Q) {w : E → ℝ} (hwm : Measurable w)
    (hw : ConvexOn ℝ Q w) {y₀ : E} (hy₀ : y₀ ∈ Q) (hzero : w y₀ = 0)
    (h0 : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ 0)
    (ht : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ ∞) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (w y / 2))
        ∂AffineFibre.normalizedMeasure (μ.restrict Q)
          (fun y => ENNReal.ofReal (Real.exp (-w y))) h0 ht ≤
      (2 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  rw [AffineFibre.lintegral_normalizedMeasure (w := fun y =>
    ENNReal.ofReal (Real.exp (-w y))) (f := fun y => ENNReal.ofReal (Real.exp (w y / 2)))
    _ (by fun_prop) h0 ht (by fun_prop)]
  have hprod (y : E) : ENNReal.ofReal (Real.exp (-w y)) *
      ENNReal.ofReal (Real.exp (w y / 2)) =
      ENNReal.ofReal (Real.exp (-w y / 2)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  simp_rw [hprod]
  calc
    _ ≤ (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ)⁻¹ *
        ((2 : ℝ≥0∞) ^ Module.finrank ℝ E *
          ∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) :=
      mul_le_mul_right (partition_half_le μ hQ hw hy₀ hzero) _
    _ = _ := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel h0 ht, mul_one]

/-- The exponential energy moment is integrable, so the corresponding real
expectation is never a nonintegrable Bochner value. -/
theorem integrable_exponential (μ : Measure E) [μ.IsAddHaarMeasure]
    {Q : Set E} (hQ : MeasurableSet Q) {w : E → ℝ} (hwm : Measurable w)
    (hw : ConvexOn ℝ Q w) {y₀ : E} (hy₀ : y₀ ∈ Q) (hzero : w y₀ = 0)
    (h0 : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ 0)
    (ht : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ ∞) :
    Integrable (fun y => Real.exp (w y / 2))
      (AffineFibre.normalizedMeasure (μ.restrict Q)
        (fun y => ENNReal.ofReal (Real.exp (-w y))) h0 ht) := by
  refine ⟨((Real.measurable_exp.comp (hwm.div_const 2))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
  exact lt_of_le_of_lt (exponential_moment_le μ hQ hwm hw hy₀ hzero h0 ht)
    (by finiteness)

/-- Internal ingredient of Appendix A: every positive real energy
moment is integrable and explicitly bounded. Nonnegativity is required only
on the integration domain. The proof uses its zero extension. -/
theorem positive_moments (μ : Measure E) [μ.IsAddHaarMeasure]
    {Q : Set E} (hQ : MeasurableSet Q) {w : E → ℝ} (hwm : Measurable w)
    (hw : ConvexOn ℝ Q w) {y₀ : E} (hy₀ : y₀ ∈ Q) (hzero : w y₀ = 0)
    (hwn : ∀ y ∈ Q, 0 ≤ w y)
    (h0 : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ 0)
    (ht : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ ∞)
    {p : ℝ} (hp : 0 < p) :
    let ρ := AffineFibre.normalizedMeasure (μ.restrict Q)
      (fun y => ENNReal.ofReal (Real.exp (-w y))) h0 ht
    Integrable (fun y => w y ^ p) ρ ∧
      ∫ y, w y ^ p ∂ρ ≤ (2 : ℝ) ^ Module.finrank ℝ E *
        (p / Real.exp 1) ^ p / (1 / 2 : ℝ) ^ p := by
  intro ρ
  have hmem : ∀ᵐ y ∂ρ, y ∈ Q :=
    (withDensity_absolutelyContinuous (μ.restrict Q) _).ae_le (ae_restrict_mem hQ)
  let W := Q.indicator w
  have hWm : Measurable W := hwm.indicator hQ
  have hWn (y : E) : 0 ≤ W y := indicator_nonneg hwn y
  have he : W =ᵐ[ρ] w := hmem.mono fun y hy => indicator_of_mem hy w
  have hexp := integrable_exponential μ hQ hwm hw hy₀ hzero h0 ht
  have hle := exponential_moment_le μ hQ hwm hw hy₀ hzero h0 ht
  have hreal : ∫ y, Real.exp (w y / 2) ∂ρ ≤ (2 : ℝ) ^ Module.finrank ℝ E := by
    have hh := ENNReal.toReal_mono (by finiteness) hle
    rw [← ofReal_integral_eq_lintegral_ofReal hexp
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)] at hh
    simpa using hh
  have heexp : (fun y => Real.exp ((1 / 2 : ℝ) * W y)) =ᵐ[ρ]
      fun y => Real.exp (w y / 2) := he.mono fun y hy => by dsimp only; rw [hy]; congr 1; ring
  obtain ⟨hi, hb⟩ := Riesz1.moment_le_of_exp_moment_le (by norm_num : (0 : ℝ) < 1 / 2)
    W hWm hWn (hexp.congr heexp.symm) ((integral_congr_ae heexp).trans_le hreal) p hp
  have hep : (fun y => W y ^ p) =ᵐ[ρ] fun y => w y ^ p :=
    he.mono fun y hy => by dsimp only; rw [hy]
  exact ⟨hi.congr hep, (integral_congr_ae hep).symm.trans_le hb⟩

end Riesz2.ConvexEnergy
