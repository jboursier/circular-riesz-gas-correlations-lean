/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CommonBaseKernelMoments
public import Riesz2.ToMathlib.ComparisonRates

/-!
# Comparison under dominated marginals

A joint probability may have marginals dominated by measures on different
carriers. No common reference measure on the base of its kernels is required.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.TwoLawComparison

/-- A second moment transfers from a dominating measure through a measurable
map. The finite extended moment proves integrability before real conversion. -/
theorem second_moment_of_map_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (π : Measure Ω) (μ : Measure X) (T : Ω → X) (hT : Measurable T)
    (f : X → ℝ) (hf : Measurable f) {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hdom : π.map T ≤ ENNReal.ofReal a • μ)
    (hm : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ≤ ENNReal.ofReal M) :
    Integrable (fun q => f (T q) ^ 2) π ∧
      (∫ q, f (T q) ^ 2 ∂π) ≤ a*M := by
  have hb : (∫⁻ q, ENNReal.ofReal (f (T q)^2) ∂π) ≤ ENNReal.ofReal (a*M) := by
    rw [← lintegral_map ((hf.pow_const 2).ennreal_ofReal) hT]
    apply (lintegral_mono' hdom le_rfl).trans
    rw [lintegral_smul_measure, smul_eq_mul, ENNReal.ofReal_mul ha]
    exact mul_le_mul' le_rfl hm
  have hh := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    (μ := π) (p := 2) (f := f ∘ T) (hf.comp hT) (mul_nonneg ha hM)
    (by simpa only [Function.comp_def, Real.rpow_two, sq_abs] using hb)
  simpa only [Function.comp_def, Real.rpow_two, sq_abs] using hh

/-- Good/bad comparison from domination of the two actual marginals.
The reference measures can be unrelated. The bad event may depend on both
coordinates. Both moment and probability losses are retained. -/
theorem comparison_of_marginals {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) [IsProbabilityMeasure π] (μ : Measure X) (ν : Measure Y)
    {a M₁ M₂ T₁ T₂ P : ℝ}
    (ha : 0 ≤ a) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hP : 0 ≤ P)
    (hμ : π.fst ≤ ENNReal.ofReal a • μ) (hν : π.snd ≤ ENNReal.ofReal a • ν)
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hmf : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ≤ ENNReal.ofReal M₁)
    (hmg : (∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂ν) ≤ ENNReal.ofReal M₂)
    (E : Set X) (F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hT₁ : μ E ≤ ENNReal.ofReal T₁) (hT₂ : ν F ≤ ENNReal.ofReal T₂)
    (hgood : ∀ᵐ q ∂π.restrict ((Prod.fst ⁻¹' E) ∪ (Prod.snd ⁻¹' F))ᶜ,
      |f q.1-g q.2| ≤ P) :
    |(∫ q, f q.1 ∂π) - ∫ q, g q.2 ∂π| ≤
      P + (Real.sqrt (a*M₁)+Real.sqrt (a*M₂))*
        Real.sqrt (a*(max T₁ 0+max T₂ 0)) := by
  obtain ⟨hi₁,hb₁⟩ := second_moment_of_map_le π μ Prod.fst measurable_fst f hf ha hM₁ hμ hmf
  obtain ⟨hi₂,hb₂⟩ := second_moment_of_map_le π ν Prod.snd measurable_snd g hg ha hM₂ hν hmg
  have hB := (hE.preimage measurable_fst).union (hF.preimage measurable_snd)
  apply integral_difference_le (hf.comp measurable_fst) (hg.comp measurable_snd)
    hi₁ hi₂ hP hb₁ hb₂ hB _ hgood
  have hb : π ((Prod.fst ⁻¹' E) ∪ (Prod.snd ⁻¹' F)) ≤
      ENNReal.ofReal a * ENNReal.ofReal T₁ + ENNReal.ofReal a * ENNReal.ofReal T₂ := by
    apply (measure_union_le _ _).trans
    apply add_le_add
    · rw [← Measure.fst_apply hE]
      exact ((hμ E).trans_eq (Measure.smul_apply _ _ _)).trans (mul_le_mul' le_rfl hT₁)
    · rw [← Measure.snd_apply hF]
      exact ((hν F).trans_eq (Measure.smul_apply _ _ _)).trans (mul_le_mul' le_rfl hT₂)
  have he : ENNReal.ofReal a * ENNReal.ofReal T₁ + ENNReal.ofReal a * ENNReal.ofReal T₂ =
      ENNReal.ofReal (a*(max T₁ 0+max T₂ 0)) := by
    rw [show ENNReal.ofReal T₁ = ENNReal.ofReal (max T₁ 0) by simp,
      show ENNReal.ofReal T₂ = ENNReal.ofReal (max T₂ 0) by simp,
      ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [he] at hb
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb

/-- Pull back domination through a measurable embedding. -/
theorem comap_le_of_le_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) (ρ : Measure Y) (μ : Measure X)
    (a : ℝ≥0∞) (h : ρ ≤ a • μ.map f) : ρ.comap f ≤ a • μ := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [hf.comap_apply, Measure.smul_apply]
  have hh := h (f '' E)
  rw [Measure.smul_apply, hf.map_apply, hf.injective.preimage_image] at hh
  exact hh

end Riesz2.TwoLawComparison

namespace Riesz2.ComparisonRates

/-- Combine the good-event rate and the bad-event moment bound after a
polynomial overlap loss. The output tail power is the minimum of the two
input powers and is independent of prefactors and temperatures. -/
theorem comparison_with_overlap_loss (q r δ₁ δ₂ C c H T ct B : ℝ)
    (_hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hC : 0 ≤ C) (hc : 0 < c)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hct : 0 < ct) (hB : 0 ≤ B) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ x b A D u v : ℝ,
      1 ≤ x → 0 ≤ b → b ≤ B*x^r → 0 ≤ A → 0 ≤ D →
      |u-v| ≤ C*x^q*(A+Real.exp (-c*x^δ₁)*D) +
        (Real.sqrt (b*(H*D^2))+Real.sqrt (b*(H*D^2)))*
          Real.sqrt (b*(T*Real.exp (-ct*x^δ₂)+T*Real.exp (-ct*x^δ₂))) →
      |u-v| ≤ C'*x^q*(A+Real.exp (-c'*x^(min δ₁ δ₂))*D) := by
  obtain ⟨K,hK,hbad⟩ := exceptional_overlap_loss r q δ₂ B H T ct hδ₂ hB hH hT hct
  let c' := min c (ct/4)
  have hc' : 0 < c' := lt_min hc (by positivity)
  refine ⟨C+K,c',by positivity,hc',?_⟩
  intro x b A D u v hx hb hbB hA hD hbound
  have htail (δ d : ℝ) (hδ : min δ₁ δ₂ ≤ δ) (hd : c' ≤ d) (hd0 : 0 ≤ d) :
      Real.exp (-d*x^δ) ≤ Real.exp (-c'*x^(min δ₁ δ₂)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le hx hδ)
      (Real.rpow_nonneg (by linarith : 0 ≤ x) _) hd0
    linarith
  have htail₁ := htail δ₁ c (min_le_left _ _) (min_le_left _ _) hc.le
  have htail₂ := htail δ₂ (ct/4) (min_le_right _ _) (min_le_right _ _) (by positivity)
  have hgood : C*x^q*(A+Real.exp (-c*x^δ₁)*D) ≤
      C*x^q*(A+Real.exp (-c'*x^(min δ₁ δ₂))*D) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right htail₁ hD))
      (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
  have hbad' := (hbad x b D hx hb hbB hD).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail₂
      (mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _))) hD)
  have hh := hbound.trans (add_le_add hgood hbad')
  have he : 0 ≤ K*x^q*A := by positivity
  nlinarith only [hh,he]

end Riesz2.ComparisonRates

namespace Riesz2.ComparisonRates

/-- A positive polynomial lower bound on overlap mass gives exactly the
inverse polynomial domination loss, without an additional power. -/
theorem inverse_overlap_bound {a C x r : ℝ} (ha : 0 < a) (hC : 0 < C) (hx : 0 < x)
    (hmass : C⁻¹*x^(-r) ≤ a) : a⁻¹ ≤ C*x^r := by
  have hh := (inv_le_inv₀ ha (mul_pos (inv_pos.mpr hC)
    (Real.rpow_pos_of_pos hx (-r)))).mpr hmass
  have he : (C⁻¹*x^(-r))⁻¹ = C*x^r := by
    rw [mul_inv_rev, Real.rpow_neg hx.le, inv_inv, inv_inv, mul_comm]
  rw [he] at hh
  exact hh

end Riesz2.ComparisonRates
