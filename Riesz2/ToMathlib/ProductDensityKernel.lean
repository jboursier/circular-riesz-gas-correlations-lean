/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Normalized product densities as probability kernels

The explicit normalized fibre laws give a Markov kernel whenever every fibre
has finite positive mass. This adds Bochner disintegration to the existing
nonnegative disintegration theorem, without choosing conditional versions.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Riesz2.AffineFibre

variable {B F : Type*} [MeasurableSpace B] [MeasurableSpace F]
variable (ν : Measure F) [SFinite ν] {w : B × F → ℝ≥0∞}

/-- The normalized fibre laws, evaluated at every point of the base carrier. -/
def normalizedKernel (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞) : Kernel B F where
  toFun x := normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x)
  measurable' := Measure.measurable_of_measurable_coe _ fun _ hs =>
    measurable_conditionalMeasure_apply ν hw h0 ht hs

instance normalizedKernel_markov (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞) :
    IsMarkovKernel (normalizedKernel ν hw h0 ht) where
  isProbabilityMeasure x := isProbabilityMeasure_normalizedMeasure ν
    (hw.comp measurable_prodMk_left) (h0 x) (ht x)

variable (μ : Measure B) [SFinite μ]

/-- Equality of measures is the disintegration identity for all tests. -/
theorem withDensity_eq_compProd (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞) :
    (μ.prod ν).withDensity w =
      μ.withDensity (fibreMass ν w) ⊗ₘ normalizedKernel ν hw h0 ht := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf]
  exact lintegral_disintegration μ ν hw h0 ht hf

/-- Bochner disintegration for every integrable test, with no boundedness premise. -/
theorem integral_disintegration {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hw : Measurable w) (h0 : ∀ x, fibreMass ν w x ≠ 0)
    (ht : ∀ x, fibreMass ν w x ≠ ∞) {f : B × F → E}
    (hf : Integrable f ((μ.prod ν).withDensity w)) :
    ∫ p, f p ∂(μ.prod ν).withDensity w =
      ∫ x, (∫ y, f (x, y) ∂normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x))
        ∂μ.withDensity (fibreMass ν w) := by
  rw [withDensity_eq_compProd ν μ hw h0 ht] at hf ⊢
  exact Measure.integral_compProd hf

/-- Integrability of the conditional tests holds almost everywhere, as required
by Fubini. No claim of pointwise integrability for an arbitrary integrable test. -/
theorem ae_integrable_normalizedMeasure {E : Type*} [NormedAddCommGroup E]
    (hw : Measurable w) (h0 : ∀ x, fibreMass ν w x ≠ 0)
    (ht : ∀ x, fibreMass ν w x ≠ ∞) {f : B × F → E}
    (hf : Integrable f ((μ.prod ν).withDensity w)) :
    ∀ᵐ x ∂μ.withDensity (fibreMass ν w),
      Integrable (fun y => f (x, y))
        (normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x)) := by
  rw [withDensity_eq_compProd ν μ hw h0 ht] at hf
  exact (Measure.integrable_compProd_iff hf.aestronglyMeasurable).mp hf |>.1

omit [SFinite μ] in
/-- Restrict a supported product density to its true base carrier. This is a
change of carrier, so no arbitrary conditional law is assigned off the support. -/
theorem withDensity_eq_map_subtypeProd {S : Set B} (hS : MeasurableSet S)
    [SFinite (μ.comap ((↑) : S → B))] (hw : Measurable w)
    (hsupport : ∀ x ∉ S, ∀ y, w (x, y) = 0) :
    (μ.prod ν).withDensity w =
      (((μ.comap ((↑) : S → B)).prod ν).withDensity
        (fun q : S × F => w (q.1.val, q.2))).map
          (fun q : S × F => (q.1.val, q.2)) := by
  have hm : Measurable (fun q : S × F => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  apply Measure.ext_of_lintegral
  intro f hf
  have hw' : Measurable (fun q : S × F => w (q.1.val, q.2)) := hw.comp hm
  have hf' : Measurable (fun q : S × F => f (q.1.val, q.2)) := hf.comp hm
  rw [lintegral_map hf hm, lintegral_withDensity_eq_lintegral_mul _ hw hf,
    lintegral_withDensity_eq_lintegral_mul _ hw' hf',
    lintegral_prod _ (hw.mul hf).aemeasurable,
    lintegral_prod _ (hw'.mul hf').aemeasurable]
  change (∫⁻ x, ∫⁻ y, w (x, y) * f (x, y) ∂ν ∂μ) =
    ∫⁻ x : S, (∫⁻ y, w (x.val, y) * f (x.val, y) ∂ν) ∂μ.comap ((↑) : S → B)
  rw [lintegral_subtype_comap (μ := μ) hS (fun x : B => ∫⁻ y, w (x, y) * f (x, y) ∂ν),
    ← lintegral_indicator hS]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, hsupport x hx, zero_mul, lintegral_zero]

omit [SFinite μ] [SFinite ν] in
/-- A finite positive factor depending only on the base cancels on its fibre. -/
theorem normalizedMeasure_mul_const (hw : Measurable w)
    (x : B) (h0 : fibreMass ν w x ≠ 0) (ht : fibreMass ν w x ≠ ∞)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    normalizedMeasure ν (fun y => c * w (x, y))
      (by rw [lintegral_const_mul _ (show Measurable (fun y => w (x, y)) from hw.comp measurable_prodMk_left)]
          exact mul_ne_zero hc0 h0)
      (by rw [lintegral_const_mul _ (show Measurable (fun y => w (x, y)) from hw.comp measurable_prodMk_left)]
          exact ENNReal.mul_ne_top hct ht) =
      normalizedMeasure ν (fun y => w (x, y)) h0 ht := by
  unfold normalizedMeasure
  congr 1
  funext y
  simp only [normalizedDensity, lintegral_const_mul _ (show Measurable (fun y => w (x, y)) from hw.comp measurable_prodMk_left),
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  calc
    c⁻¹ * (∫⁻ z, w (x, z) ∂ν)⁻¹ * (c * w (x, y)) =
      (c⁻¹ * c) * ((∫⁻ z, w (x, z) ∂ν)⁻¹ * w (x, y)) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hct, one_mul]

omit [SFinite ν] in
/-- A support indicator is precisely restriction of the reference measure. -/
theorem normalizedMeasure_indicator {S : Set F} (hS : MeasurableSet S)
    (v : F → ℝ≥0∞) (h0 : (∫⁻ y in S, v y ∂ν) ≠ 0)
    (ht : (∫⁻ y in S, v y ∂ν) ≠ ∞) :
    normalizedMeasure ν (S.indicator v)
      (by rwa [lintegral_indicator hS]) (by rwa [lintegral_indicator hS]) =
      normalizedMeasure (ν.restrict S) v h0 ht := by
  simp only [normalizedMeasure_eq_smul, lintegral_indicator hS, withDensity_indicator hS]

end Riesz2.AffineFibre
