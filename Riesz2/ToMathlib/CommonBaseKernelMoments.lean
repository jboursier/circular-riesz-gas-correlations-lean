/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CommonBaseKernel
public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Moment bounds after changing a common base law

Nonnegative moments of either coordinate of a conditional product are
dominated by the corresponding original mixture. The comparison estimate
uses second moments under the original laws, with integrability concluded
before any real integral is estimated.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.CommonBaseKernel

variable {L X Y : Type*} [MeasurableSpace L] [MeasurableSpace X] [MeasurableSpace Y]
variable (κ : Kernel L X) (η : Kernel L Y) [IsMarkovKernel κ] [IsMarkovKernel η]
variable (ρ μ ν : Measure L)

/-- Nonnegative first-coordinate moments transfer through a dominated base law. -/
theorem lintegral_fst_le_smul {a : ℝ≥0∞} (hρ : ρ ≤ a • μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q, f q.1 ∂law κ η ρ) ≤ a * ∫⁻ x, f x ∂(κ ∘ₘ μ) := by
  have he : (∫⁻ q, f q.1 ∂law κ η ρ) = ∫⁻ x, f x ∂(κ ∘ₘ ρ) := by
    rw [← fst_law κ η ρ]
    exact (lintegral_map hf measurable_fst).symm
  rw [he]
  calc
    _ ≤ ∫⁻ x, f x ∂(a • (κ ∘ₘ μ)) :=
      lintegral_mono' (comp_le_smul κ ρ μ a hρ) le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

/-- Nonnegative second-coordinate moments transfer through a dominated base law. -/
theorem lintegral_snd_le_smul {a : ℝ≥0∞} (hρ : ρ ≤ a • ν)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ q, g q.2 ∂law κ η ρ) ≤ a * ∫⁻ y, g y ∂(η ∘ₘ ν) := by
  have he : (∫⁻ q, g q.2 ∂law κ η ρ) = ∫⁻ y, g y ∂(η ∘ₘ ρ) := by
    rw [← snd_law κ η ρ]
    exact (lintegral_map hg measurable_snd).symm
  rw [he]
  calc
    _ ≤ ∫⁻ y, g y ∂(a • (η ∘ₘ ν)) :=
      lintegral_mono' (comp_le_smul η ρ ν a hρ) le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

/-- The original first-coordinate second moment gives integrability and a real
second-moment bound under the common-base conditional product. -/
theorem fst_second_moment {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hρ : ρ ≤ ENNReal.ofReal a • μ) (f : X → ℝ) (hf : Measurable f)
    (hm : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(κ ∘ₘ μ)) ≤ ENNReal.ofReal M) :
    Integrable (fun q => f q.1 ^ 2) (law κ η ρ) ∧
      (∫ q, f q.1 ^ 2 ∂law κ η ρ) ≤ a * M := by
  have hb := (lintegral_fst_le_smul κ η ρ μ hρ
    (fun x => ENNReal.ofReal (f x ^ 2)) ((hf.pow_const 2).ennreal_ofReal)).trans
      (mul_le_mul' le_rfl hm)
  rw [← ENNReal.ofReal_mul ha] at hb
  have hh := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    (μ := law κ η ρ) (p := 2) (f := fun q : X × Y => f q.1)
    (hf.comp measurable_fst) (mul_nonneg ha hM) (by
      simpa only [Real.rpow_two, sq_abs] using hb)
  simpa only [Real.rpow_two, sq_abs] using hh

/-- The corresponding second-coordinate second-moment bound. -/
theorem snd_second_moment {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hρ : ρ ≤ ENNReal.ofReal a • ν) (g : Y → ℝ) (hg : Measurable g)
    (hm : (∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂(η ∘ₘ ν)) ≤ ENNReal.ofReal M) :
    Integrable (fun q => g q.2 ^ 2) (law κ η ρ) ∧
      (∫ q, g q.2 ^ 2 ∂law κ η ρ) ≤ a * M := by
  have hb := (lintegral_snd_le_smul κ η ρ ν hρ
    (fun y => ENNReal.ofReal (g y ^ 2)) ((hg.pow_const 2).ennreal_ofReal)).trans
      (mul_le_mul' le_rfl hm)
  rw [← ENNReal.ofReal_mul ha] at hb
  have hh := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    (μ := law κ η ρ) (p := 2) (f := fun q : X × Y => g q.2)
    (hg.comp measurable_snd) (mul_nonneg ha hM) (by
      simpa only [Real.rpow_two, sq_abs] using hb)
  simpa only [Real.rpow_two, sq_abs] using hh

end Riesz2.CommonBaseKernel

namespace Riesz2.TwoLawComparison

variable {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} [IsProbabilityMeasure π]

/-- Jensen for the square, with an extended second moment. Finiteness of
the right side supplies integrability. Infinite moments remain infinite. -/
theorem ofReal_sq_integral_le_lintegral_sq {f : Ω → ℝ} (hf : Measurable f) :
    ENNReal.ofReal ((∫ q, f q ∂π) ^ 2) ≤ ∫⁻ q, ENNReal.ofReal (f q ^ 2) ∂π := by
  let M := ∫⁻ q, ENNReal.ofReal (f q ^ 2) ∂π
  by_cases hM : M = ⊤
  · change _ ≤ M
    rw [hM]
    exact le_top
  have hb : (∫⁻ q, ENNReal.ofReal (f q ^ 2) ∂π) ≤ ENNReal.ofReal M.toReal := by
    rw [ENNReal.ofReal_toReal hM]
  obtain ⟨hi, _⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    (μ := π) (p := 2) (f := f) hf ENNReal.toReal_nonneg (by
      simpa only [Real.rpow_two, sq_abs] using hb)
  simp only [Real.rpow_two, sq_abs] at hi
  have hh := Riesz1.integral_on_event_le_second_moment hf.aestronglyMeasurable.norm
    (fun q => norm_nonneg (f q)) (by simpa only [Real.norm_eq_abs, sq_abs] using hi)
    MeasurableSet.univ
  simp only [setIntegral_univ, Real.norm_eq_abs, sq_abs, measureReal_def,
    measure_univ, ENNReal.toReal_one, ← Real.sqrt_eq_rpow, Real.sqrt_one, mul_one] at hh
  have he : |∫ q, f q ∂π| ≤ Real.sqrt (∫ q, f q ^ 2 ∂π) :=
    abs_integral_le_integral_abs.trans hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) he 2
  rw [sq_abs, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all π fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hs

/-- An event contribution uses the global second moment, even if the
event depends on both coordinates of a conditional product. -/
theorem integral_abs_on_event_le {f : Ω → ℝ} (hf : Measurable f)
    (hfi : Integrable (fun q => f q ^ 2) π) {M t : ℝ}
    (hm : (∫ q, f q ^ 2 ∂π) ≤ M) {B : Set Ω} (hB : MeasurableSet B)
    (hprob : π.real B ≤ t) :
    (∫ q in B, |f q| ∂π) ≤ Real.sqrt M * Real.sqrt t := by
  have hh := Riesz1.integral_on_event_le_second_moment
    hf.aestronglyMeasurable.norm (fun q => norm_nonneg (f q))
    (by simpa only [Real.norm_eq_abs, sq_abs] using hfi) hB
  simp only [Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow] at hh
  exact hh.trans (mul_le_mul (Real.sqrt_le_sqrt hm) (Real.sqrt_le_sqrt hprob)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Integrate a comparison on the good event and use centered second moments
on its complement. No independence between the observable and event is used. -/
theorem integral_difference_le {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun q => f q ^ 2) π)
    (hgi : Integrable (fun q => g q ^ 2) π)
    {M₁ M₂ t P : ℝ} (hP : 0 ≤ P)
    (hmf : (∫ q, f q ^ 2 ∂π) ≤ M₁) (hmg : (∫ q, g q ^ 2 ∂π) ≤ M₂)
    {B : Set Ω} (hB : MeasurableSet B) (hprob : π.real B ≤ t)
    (hgood : ∀ᵐ q ∂π.restrict Bᶜ, |f q - g q| ≤ P) :
    |(∫ q, f q ∂π) - ∫ q, g q ∂π| ≤
      P + (Real.sqrt M₁ + Real.sqrt M₂) * Real.sqrt t := by
  have hif := MomentEvent.integrable_of_integrable_sq hf hfi
  have hig := MomentEvent.integrable_of_integrable_sq hg hgi
  have hi := hif.sub hig
  have hgoodint : |∫ q in Bᶜ, f q - g q ∂π| ≤ P := by
    apply abs_integral_le_integral_abs.trans
    apply (integral_mono_ae hi.abs.integrableOn (integrable_const P) hgood).trans
    simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    exact mul_le_of_le_one_left hP measureReal_le_one
  have hbadint : |∫ q in B, f q - g q ∂π| ≤
      (Real.sqrt M₁ + Real.sqrt M₂) * Real.sqrt t := by
    calc
      _ ≤ ∫ q in B, |f q - g q| ∂π := abs_integral_le_integral_abs
      _ ≤ ∫ q in B, (|f q| + |g q|) ∂π :=
        integral_mono hi.abs.integrableOn (hif.abs.add hig.abs).integrableOn
          (fun q => abs_sub (f q) (g q))
      _ = (∫ q in B, |f q| ∂π) + ∫ q in B, |g q| ∂π :=
        integral_add hif.abs.integrableOn hig.abs.integrableOn
      _ ≤ Real.sqrt M₁ * Real.sqrt t + Real.sqrt M₂ * Real.sqrt t :=
        add_le_add (integral_abs_on_event_le hf hfi hmf hB hprob)
          (integral_abs_on_event_le hg hgi hmg hB hprob)
      _ = _ := by ring
  rw [← integral_sub hif hig,
    ← integral_add_compl hB (show Integrable (fun q => f q - g q) π from hi)]
  exact (abs_add_le _ _).trans ((add_le_add hbadint hgoodint).trans_eq (by ring))

end Riesz2.TwoLawComparison

namespace Riesz2.CommonBaseKernel

variable {L X Y : Type*} [MeasurableSpace L] [MeasurableSpace X] [MeasurableSpace Y]
variable (κ : Kernel L X) (η : Kernel L Y) [IsMarkovKernel κ] [IsMarkovKernel η]
variable (ρ μ ν : Measure L) [IsProbabilityMeasure ρ]

/-- The second moment of a conditional average is bounded by the original
second moment. This applies to the fixed-exterior active conditional kernel. -/
theorem conditional_average_second_moment (f : X → ℝ) (hf : Measurable f) :
    (∫⁻ l, ENNReal.ofReal ((∫ x, f x ∂κ l) ^ 2) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(κ ∘ₘ μ) := by
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) ((hf.pow_const 2).ennreal_ofReal).aemeasurable]
  exact lintegral_mono fun l => TwoLawComparison.ofReal_sq_integral_le_lintegral_sq hf

/-- Conditional-product comparison from the original marginal moments and
bad-event probabilities. The loss is one factor of the base domination
constant after Cauchy--Schwarz, rather than its square. -/
theorem comparison_le {a M₁ M₂ T₁ T₂ P : ℝ}
    (ha : 0 ≤ a) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hP : 0 ≤ P)
    (hμ : ρ ≤ ENNReal.ofReal a • μ) (hν : ρ ≤ ENNReal.ofReal a • ν)
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hmf : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(κ ∘ₘ μ)) ≤ ENNReal.ofReal M₁)
    (hmg : (∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂(η ∘ₘ ν)) ≤ ENNReal.ofReal M₂)
    (E : Set X) (F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hT₁ : (κ ∘ₘ μ) E ≤ ENNReal.ofReal T₁)
    (hT₂ : (η ∘ₘ ν) F ≤ ENNReal.ofReal T₂)
    (hgood : ∀ᵐ q ∂(law κ η ρ).restrict
      ((Prod.fst ⁻¹' E) ∪ (Prod.snd ⁻¹' F))ᶜ, |f q.1 - g q.2| ≤ P) :
    |(∫ q, f q.1 ∂law κ η ρ) - ∫ q, g q.2 ∂law κ η ρ| ≤
      P + (Real.sqrt (a * M₁) + Real.sqrt (a * M₂)) *
        Real.sqrt (a * (max T₁ 0 + max T₂ 0)) := by
  have hB := (hE.preimage measurable_fst).union (hF.preimage measurable_snd)
  obtain ⟨hi₁, hb₁⟩ := fst_second_moment κ η ρ μ ha hM₁ hμ f hf hmf
  obtain ⟨hi₂, hb₂⟩ := snd_second_moment κ η ρ ν ha hM₂ hν g hg hmg
  apply TwoLawComparison.integral_difference_le
    (hf.comp measurable_fst) (hg.comp measurable_snd) hi₁ hi₂ hP hb₁ hb₂ hB _ hgood
  have hb := (bad_event_le κ η ρ μ ν (ENNReal.ofReal a) hμ hν E F hE hF).trans
    (add_le_add (mul_le_mul' le_rfl hT₁) (mul_le_mul' le_rfl hT₂))
  have he : ENNReal.ofReal a * ENNReal.ofReal T₁ +
      ENNReal.ofReal a * ENNReal.ofReal T₂ =
      ENNReal.ofReal (a * (max T₁ 0 + max T₂ 0)) := by
    rw [show ENNReal.ofReal T₁ = ENNReal.ofReal (max T₁ 0) by simp,
      show ENNReal.ofReal T₂ = ENNReal.ofReal (max T₂ 0) by simp,
      ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [he] at hb
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb

end Riesz2.CommonBaseKernel
