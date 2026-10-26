/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.PolynomialProfileTruncation
public import Riesz2.ToMathlib.CovarianceCauchySchwarz
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Measurability and event pairings for covariance coefficients

Kernel covariances are measurable before any integrability assertion.
The pairing estimate separately concludes absolute integrability and uses
an explicit second moment, so the totalized Bochner integral cannot hide
an infinite moment.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.KernelCovarianceBounds

/-- The covariance of two jointly measurable functions under a measurable
kernel is measurable as a function of its base point. -/
theorem measurable_covariance {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel α Ω)
    [ProbabilityTheory.IsSFiniteKernel κ] {f g : α × Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => ProbabilityTheory.covariance (fun z => f (x,z))
      (fun z => g (x,z)) (κ x)) := by
  have hfm : Measurable (fun x => ∫ z, f (x,z) ∂κ x) :=
    hf.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hgm : Measurable (fun x => ∫ z, g (x,z) ∂κ x) :=
    hg.stronglyMeasurable.integral_kernel_prod_right'.measurable
  exact (((hf.sub (hfm.comp measurable_fst)).mul
    (hg.sub (hgm.comp measurable_fst))).stronglyMeasurable.integral_kernel_prod_right').measurable

/-- A square-root product envelope has a simple additive majorant. This is
useful when its individual nonnegative coefficients already have moments. -/
theorem sqrt_product_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ a + b := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]

/-- An additive nonnegative envelope transfers finite moments. The two
coefficients need not be independent. -/
theorem envelope_norm {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {Y a b : Ω → ℝ} {p : ℝ≥0∞} {A B : ℝ}
    (hp : 1 ≤ p) (hY : Measurable Y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hbound : ∀ x, |Y x| ≤ Real.sqrt (a x) * Real.sqrt (b x))
    (ham : eLpNorm a p ν ≤ ENNReal.ofReal A)
    (hbm : eLpNorm b p ν ≤ ENNReal.ofReal B) :
    eLpNorm Y p ν ≤ ENNReal.ofReal (A + B) := by
  apply (eLpNorm_mono_ae_real hY.aestronglyMeasurable
    (g := a + b) (ae_of_all ν fun x => ?_)).trans
  · apply (eLpNorm_add_le hp).trans
    exact (add_le_add ham hbm).trans_eq (ENNReal.ofReal_add hA hB).symm
  · simpa only [Real.norm_eq_abs, Pi.add_apply] using
      (hbound x).trans (sqrt_product_le_add (ha x) (hb x))

/-- Good-event multiplication plus an explicit exceptional second-moment
bound. All sources are essentially bounded. Their absolute integrability
and the full signed pairing estimate are conclusions. -/
theorem event_pair {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {Y φ η : Ω → ℝ} {G : Set Ω} {P M D c t Mφ Mη : ℝ}
    (hG : MeasurableSet G) (hY : Measurable Y) (hφ : Measurable φ) (hη : Measurable η)
    (hP : 0 ≤ P) (hM : 0 ≤ M) (hD : 0 ≤ D) (hMφ : 0 ≤ Mφ) (hMη : 0 ≤ Mη)
    (hφM : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hηM : ∀ᵐ x ∂ν, |η x| ≤ Mη)
    (hφ2 : MemLp φ 2 ν) (hη2 : MemLp η 2 ν)
    (hb : ∀ x ∈ G, |Y x| ≤ P)
    (hmom : eLpNorm Y 2 ν ≤ ENNReal.ofReal M)
    (hprob : ν Gᶜ ≤ ENNReal.ofReal (D * Real.exp (-c * t))) :
    Integrable (fun x => φ x * η x * Y x) ν ∧
      |∫ x, φ x * η x * Y x ∂ν| ≤
        P * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          M * Real.sqrt D * Real.exp (-(c / 2) * t) * (Mφ * Mη) := by
  classical
  let f := fun x => if |φ x| ≤ Mφ then φ x else 0
  let g := fun x => if |η x| ≤ Mη then η x else 0
  have hf : Measurable f := hφ.ite
    (measurableSet_le (continuous_abs.measurable.comp hφ) measurable_const) measurable_const
  have hg : Measurable g := hη.ite
    (measurableSet_le (continuous_abs.measurable.comp hη) measurable_const) measurable_const
  have hff : ∀ x, |f x| ≤ Mφ := by intro x; dsimp [f]; split_ifs <;> simp_all
  have hgg : ∀ x, |g x| ≤ Mη := by intro x; dsimp [g]; split_ifs <;> simp_all
  have hfe : f =ᵐ[ν] φ := hφM.mono fun x hx => ite_eq_left hx
  have hge : g =ᵐ[ν] η := hηM.mono fun x hx => ite_eq_left hx
  have he : (fun x => f x * g x * Y x) =ᵐ[ν] fun x => φ x * η x * Y x := by
    filter_upwards [hfe, hge] with x hx hy
    rw [hx, hy]
  have hgM : ∀ x, |f x * g x| ≤ Mφ * Mη := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hff x) (hgg x) (abs_nonneg _) hMφ
  obtain ⟨hY2, hYsq⟩ := CoefficientMomentTruncation.sq_integrable_and_integral_le hY hM
    (by simpa only [ENNReal.ofReal_ofNat] using hmom)
  have hi := MomentEvent.integrable_mul_of_abs_le (hf.mul hg)
    (MomentEvent.integrable_of_integrable_sq hY hY2) hgM
  have hgood := (PolynomialProfileTruncation.bounded_coefficient_pair
    hG hY hP hb hf hg ((memLp_congr_ae hfe).mpr hφ2) ((memLp_congr_ae hge).mpr hη2)).2
  have hbad := MomentEvent.abs_integral_mul_le_sqrt_mul_sqrt
    (hf.mul hg) hY (mul_nonneg hMφ hMη) hgM hY2 hG.compl
  have hYs : Real.sqrt (∫ x, Y x ^ 2 ∂ν) ≤ M :=
    (Real.sqrt_le_sqrt hYsq).trans_eq (Real.sqrt_sq hM)
  have hprobR : ν.real Gᶜ ≤ D * Real.exp (-c * t) :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hs : Real.sqrt (ν.real Gᶜ) ≤ Real.sqrt D * Real.exp (-(c / 2) * t) := by
    have heq : (Real.sqrt D * Real.exp (-(c / 2) * t)) ^ 2 = D * Real.exp (-c * t) := by
      rw [mul_pow, Real.sq_sqrt hD, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    exact (Real.sqrt_le_sqrt (hprobR.trans_eq heq.symm)).trans_eq (Real.sqrt_sq (by positivity))
  have hbad' : |∫ x in Gᶜ, f x * g x * Y x ∂ν| ≤
      M * Real.sqrt D * Real.exp (-(c / 2) * t) * (Mφ * Mη) := by
    apply hbad.trans
    calc
      _ ≤ (Mφ * Mη) * M * (Real.sqrt D * Real.exp (-(c / 2) * t)) := by gcongr
      _ = _ := by ring
  have htot := (abs_add_le (∫ x in G, f x * g x * Y x ∂ν)
    (∫ x in Gᶜ, f x * g x * Y x ∂ν)).trans (add_le_add hgood hbad')
  rw [integral_add_compl hG (show Integrable (fun x => f x * g x * Y x) ν from hi)] at htot
  refine ⟨hi.congr he, ?_⟩
  rw [integral_congr_ae he,
    integral_congr_ae (hfe.mono fun _ hx => congrArg (fun u : ℝ => u ^ 2) hx),
    integral_congr_ae (hge.mono fun _ hx => congrArg (fun u : ℝ => u ^ 2) hx)] at htot
  exact htot

/-- A restricted second-moment bound gives the exceptional pairing for
essentially bounded sources on a subprobability event. -/
theorem restricted_pair {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {E : Set Ω} {Y φ η : Ω → ℝ} {M Mφ Mη : ℝ}
    (hY : Measurable Y) (hφ : Measurable φ) (hη : Measurable η)
    (hM : 0 ≤ M) (hMφ : 0 ≤ Mφ) (hMη : 0 ≤ Mη)
    (hφM : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hηM : ∀ᵐ x ∂ν, |η x| ≤ Mη)
    (hmom : eLpNorm Y 2 (ν.restrict E) ≤ ENNReal.ofReal M) :
    IntegrableOn (fun x => φ x * η x * Y x) E ν ∧
      |∫ x in E, φ x * η x * Y x ∂ν| ≤ M * (Mφ * Mη) := by
  have hf := ae_restrict_of_ae hφM (s := E)
  have hg := ae_restrict_of_ae hηM (s := E)
  have hφ2 : MemLp φ 2 (ν.restrict E) := MemLp.of_bound hφ.aestronglyMeasurable.restrict Mφ
    (by simpa only [Real.norm_eq_abs] using hf)
  have hη2 : MemLp η 2 (ν.restrict E) := MemLp.of_bound hη.aestronglyMeasurable.restrict Mη
    (by simpa only [Real.norm_eq_abs] using hg)
  have hp : (ν.restrict E) (∅ : Set Ω)ᶜ ≤ ENNReal.ofReal ((1 : ℝ) * Real.exp (-(0 : ℝ) * 0)) := by
    simpa only [compl_empty, Measure.restrict_apply_univ, zero_mul, neg_zero, Real.exp_zero,
      mul_one, ENNReal.ofReal_one] using (show ν E ≤ 1 from prob_le_one)
  have ht := event_pair (G := ∅) (P := 0) MeasurableSet.empty hY hφ hη le_rfl hM
    zero_le_one hMφ hMη hf hg hφ2 hη2 (by simp) hmom hp
  refine ⟨ht.1, ?_⟩
  simpa only [zero_mul, zero_add, Real.sqrt_one, mul_one, zero_div,
    neg_zero, Real.exp_zero] using ht.2

end Riesz2.KernelCovarianceBounds
