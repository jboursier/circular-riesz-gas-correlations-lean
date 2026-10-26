/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoefficientMomentTruncation
public import Riesz2.ToMathlib.MomentCutoffTail

/-!
# Moment truncation with polynomial spatial profiles

The spatial profile of a column difference can exceed one. Truncation at
twice the profile times the size loss preserves the principal term.
A polynomial upper bound on the profile affects only the exponential
prefactor and rate, leaving the stretched exponential power unchanged.
-/

public section
noncomputable section

open MeasureTheory Set

namespace Riesz2.PolynomialProfileTruncation

/-- Cauchy--Schwarz for a bounded multiplier on a measurable event. The
coefficient need only be bounded on that event. -/
theorem bounded_coefficient_pair {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {Y φ η : Ω → ℝ} {P : ℝ} {G : Set Ω}
    (hG : MeasurableSet G) (hY : Measurable Y) (hP : 0 ≤ P)
    (hb : ∀ x ∈ G, |Y x| ≤ P) (hφ : Measurable φ) (hη : Measurable η)
    (hφ2 : MemLp φ 2 ν) (hη2 : MemLp η 2 ν) :
    IntegrableOn (fun x => φ x * η x * Y x) G ν ∧
      |∫ x in G, φ x * η x * Y x ∂ν| ≤
        P * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) := by
  obtain ⟨hi, hCS⟩ := MomentEvent.integrable_mul_and_integral_abs_mul_le hφ hη
    ((memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mp hφ2)
    ((memLp_two_iff_integrable_sq hη.aestronglyMeasurable).mp hη2)
  have hpt : ∀ᵐ x ∂ν.restrict G, ‖φ x * η x * Y x‖ ≤ P * |φ x * η x| := by
    apply (ae_restrict_iff' hG).mpr
    exact ae_of_all ν fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, mul_comm P]
      exact mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg _)
  have hiY : IntegrableOn (fun x => φ x * η x * Y x) G ν :=
    ((hi.abs.const_mul P).integrableOn).mono'
      ((hφ.mul hη).mul hY).aestronglyMeasurable.restrict hpt
  refine ⟨hiY, ?_⟩
  calc
    _ ≤ ∫ x in G, |φ x * η x * Y x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x in G, P * |φ x * η x| ∂ν :=
      integral_mono_ae hiY.abs (hi.abs.const_mul P).integrableOn
        (hpt.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
    _ = P * ∫ x in G, |φ x * η x| ∂ν := integral_const_mul _ _
    _ ≤ P * ∫ x, |φ x * η x| ∂ν := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hi.abs (ae_of_all ν fun _ => abs_nonneg _)) hP
    _ ≤ _ := mul_le_mul_of_nonneg_left hCS hP

/-- The two inequalities of the manuscript's equation (5.25), for an arbitrary
measurable event `G`. Here `T` is the threshold `n^(κ ε) a`, and `Mφ`, `Mη` are
essential bounds for the two sources. The first inequality retains the exceptional
`L¹` contribution. The second bounds it by Cauchy--Schwarz. The coefficient is
square integrable, as in the applications in Lemma 5.8. -/
theorem coefficient_pair_split_event {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {Y φ η : Ω → ℝ}
    {T Mφ Mη : ℝ} {G : Set Ω} (hG : MeasurableSet G)
    (hY : Measurable Y) (hY2 : MemLp Y 2 ν)
    (hφ : Measurable φ) (hη : Measurable η)
    (hT : 0 ≤ T) (hMφ : 0 ≤ Mφ) (hMη : 0 ≤ Mη)
    (hφM : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hηM : ∀ᵐ x ∂ν, |η x| ≤ Mη)
    (hYG : ∀ᵐ x ∂ν.restrict G, |Y x| ≤ T) :
    Integrable (fun x => φ x * η x * Y x) ν ∧
      |∫ x, φ x * η x * Y x ∂ν| ≤
        T * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          (∫ x in Gᶜ, |Y x| ∂ν) * (Mφ * Mη) ∧
      T * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          (∫ x in Gᶜ, |Y x| ∂ν) * (Mφ * Mη) ≤
        T * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          Real.sqrt (∫ x, Y x ^ 2 ∂ν) * Real.sqrt (ν.real Gᶜ) * (Mφ * Mη) := by
  have hφ2 : MemLp φ 2 ν := MemLp.of_bound hφ.aestronglyMeasurable Mφ
    (hφM.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)
  have hη2 : MemLp η 2 ν := MemLp.of_bound hη.aestronglyMeasurable Mη
    (hηM.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)
  obtain ⟨hiφη, hCS⟩ := MomentEvent.integrable_mul_and_integral_abs_mul_le hφ hη
    ((memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mp hφ2)
    ((memLp_two_iff_integrable_sq hη.aestronglyMeasurable).mp hη2)
  have hiY : Integrable Y ν := hY2.integrable (by norm_num)
  have hM : 0 ≤ Mφ * Mη := mul_nonneg hMφ hMη
  have hprod : ∀ᵐ x ∂ν, |φ x * η x * Y x| ≤ (Mφ * Mη) * |Y x| := by
    filter_upwards [hφM, hηM] with x hx hy
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hx hy (abs_nonneg _) hMφ) (abs_nonneg _)
  have hi : Integrable (fun x => φ x * η x * Y x) ν :=
    (hiY.abs.const_mul (Mφ * Mη)).mono' ((hφ.mul hη).mul hY).aestronglyMeasurable
      (hprod.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)
  have hgood : |∫ x in G, φ x * η x * Y x ∂ν| ≤
      T * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) := by
    have hpt : ∀ᵐ x ∂ν.restrict G, |φ x * η x * Y x| ≤ T * |φ x * η x| := by
      filter_upwards [hYG] with x hx
      rw [abs_mul, mul_comm T]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    calc
      _ ≤ ∫ x in G, |φ x * η x * Y x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x in G, T * |φ x * η x| ∂ν :=
        integral_mono_ae hi.abs.integrableOn (hiφη.abs.const_mul T).integrableOn hpt
      _ = T * ∫ x in G, |φ x * η x| ∂ν := integral_const_mul _ _
      _ ≤ T * ∫ x, |φ x * η x| ∂ν := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hiφη.abs (ae_of_all ν fun _ => abs_nonneg _)) hT
      _ ≤ _ := mul_le_mul_of_nonneg_left hCS hT
  have hbad : |∫ x in Gᶜ, φ x * η x * Y x ∂ν| ≤
      (∫ x in Gᶜ, |Y x| ∂ν) * (Mφ * Mη) := by
    calc
      _ ≤ ∫ x in Gᶜ, |φ x * η x * Y x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x in Gᶜ, (Mφ * Mη) * |Y x| ∂ν :=
        integral_mono_ae hi.abs.integrableOn (hiY.abs.const_mul _).integrableOn
          (ae_restrict_of_ae hprod)
      _ = _ := by rw [integral_const_mul, mul_comm]
  have htail : (∫ x in Gᶜ, |Y x| ∂ν) ≤
      Real.sqrt (∫ x, Y x ^ 2 ∂ν) * Real.sqrt (ν.real Gᶜ) := by
    have h := Riesz1.integral_on_event_le_second_moment
      (continuous_abs.measurable.comp hY).aestronglyMeasurable
      (fun x => abs_nonneg (Y x))
      (by simpa only [Function.comp_apply, sq_abs] using
        (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mp hY2) hG.compl
    simpa only [Function.comp_apply, sq_abs, ← Real.sqrt_eq_rpow] using h
  refine ⟨hi, ?_, add_le_add le_rfl (mul_le_mul_of_nonneg_right htail hM)⟩
  calc
    _ = |(∫ x in G, φ x * η x * Y x ∂ν) +
        ∫ x in Gᶜ, φ x * η x * Y x ∂ν| := congrArg abs (integral_add_compl hG hi).symm
    _ ≤ |∫ x in G, φ x * η x * Y x ∂ν| +
        |∫ x in Gᶜ, φ x * η x * Y x ∂ν| := abs_add_le _ _
    _ ≤ _ := add_le_add hgood hbad

/-- The profile extension of the proof of Lemma 5.8,
used for the column differences in Lemma 5.8. The profile is
positive and can grow by any fixed power of the size. The splitting step is
the manuscript's equation (5.25). -/
theorem moment_truncation {A ε κ C B : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hκ : 0 < κ) (hC : 1 ≤ C) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (h : ℝ), 0 < h →
      h ≤ (n : ℝ) ^ B → ∀ (Y φ η : Ω → ℝ) (Mφ Mη : ℝ),
      Measurable Y → Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
      (∀ x, |φ x| ≤ Mφ) → (∀ x, |η x| ≤ Mη) →
      (∀ p : ℝ, 1 ≤ p → eLpNorm Y (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal (C * p ^ A * h)) →
      Integrable (fun x => φ x * η x * Y x) ν ∧
        |∫ x, φ x * η x * Y x ∂ν| ≤
          D * (n : ℝ) ^ (κ * ε) * h *
            (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          D * Real.exp (-c * (n : ℝ) ^ (κ * ε / (2 * A))) * (Mφ * Mη) := by
  have hδ : 0 < κ * ε / (2 * A) := by positivity
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨D, hD, ht⟩ := MomentEvent.moment_cutoff_tail hA (mul_pos hκ hε) hC0
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := B) hδ (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
  let F := C * (2 : ℝ) ^ A * Real.sqrt D * (K + 1)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨1 / 4, 2 + F, by norm_num, by positivity, ?_⟩
  intro n hn Ω _ ν _ h hh hhn Y φ η Mφ Mη hY hφ hη hMφ hMη hφM hηM hmom
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let T := 2 * (n : ℝ) ^ (κ * ε) * h
  have hT : 0 < T := by dsimp [T]; positivity
  have hM : 0 ≤ C * 2 ^ A * h := by positivity
  obtain ⟨hiY, hY2⟩ := CoefficientMomentTruncation.sq_integrable_and_integral_le
    hY hM (by simpa only [ENNReal.ofReal_ofNat] using hmom 2 (by norm_num))
  have hYs : Real.sqrt (∫ x, Y x ^ 2 ∂ν) ≤ C * 2 ^ A * h :=
    (Real.sqrt_le_sqrt hY2).trans_eq (Real.sqrt_sq hM)
  have hG : MeasurableSet {x | |Y x| < T} :=
    measurableSet_lt (continuous_abs.measurable.comp hY) measurable_const
  obtain ⟨hi, hsplitL1, hsplitL2⟩ := coefficient_pair_split_event hG hY
    ((memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr hiY) hφ hη hT.le hMφ hMη
    (ae_of_all ν hφM) (ae_of_all ν hηM)
    ((ae_restrict_iff' hG).mpr (ae_of_all ν fun _ hx => hx.le))
  have hsplit := hsplitL1.trans hsplitL2
  have hcompl : {x | |Y x| < T}ᶜ = {x | T ≤ |Y x|} := by ext x; simp
  rw [hcompl] at hsplit
  refine ⟨hi, ?_⟩
  have hprob : ν {x | T ≤ |Y x|} ≤
      ENNReal.ofReal (D * Real.exp (-(n : ℝ) ^ (κ * ε / (2 * A)))) := by
    apply (measure_mono (show {x | T ≤ |Y x|} ⊆
        {x | (n : ℝ) ^ (1 * (κ * ε)) * h < |Y x|} from ?_)).trans
      (ht n (by omega) ν Y hY h 1 hh le_rfl hmom)
    intro x hx
    simp only [one_mul, mem_ofPred_eq]
    change T ≤ |Y x| at hx
    have hp : 0 < (n : ℝ) ^ (κ * ε) * h := by positivity
    dsimp only [T] at hx
    linarith
  have hprobR : ν.real {x | T ≤ |Y x|} ≤
      D * Real.exp (-(n : ℝ) ^ (κ * ε / (2 * A))) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hsE : Real.sqrt (ν.real {x | T ≤ |Y x|}) ≤
      Real.sqrt D * Real.exp (-(1 / 2) * (n : ℝ) ^ (κ * ε / (2 * A))) := by
    have he : (Real.sqrt D * Real.exp (-(1 / 2) * (n : ℝ) ^ (κ * ε / (2 * A)))) ^ 2 =
        D * Real.exp (-(n : ℝ) ^ (κ * ε / (2 * A))) := by
      rw [mul_pow, Real.sq_sqrt hD.le, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    exact (Real.sqrt_le_sqrt (hprobR.trans_eq he.symm)).trans_eq
      (Real.sqrt_sq (by positivity))
  have htail : h * Real.exp (-(1 / 2) * (n : ℝ) ^ (κ * ε / (2 * A))) ≤
      (K + 1) * Real.exp (-(1 / 4) * (n : ℝ) ^ (κ * ε / (2 * A))) := by
    exact (mul_le_mul_of_nonneg_right hhn (Real.exp_pos _).le).trans
      ((hpoly (n : ℝ) hn1).trans (by gcongr; linarith only [hK]))
  have herr' : Real.sqrt (∫ x, Y x ^ 2 ∂ν) *
      Real.sqrt (ν.real {x | T ≤ |Y x|}) * (Mφ * Mη) ≤
      F * Real.exp (-(1 / 4) * (n : ℝ) ^ (κ * ε / (2 * A))) * (Mφ * Mη) := by
    calc
      _ ≤ (C * 2 ^ A * h) *
          (Real.sqrt D * Real.exp (-(1 / 2) * (n : ℝ) ^ (κ * ε / (2 * A)))) *
          (Mφ * Mη) := by gcongr
      _ = (Mφ * Mη) * (C * 2 ^ A * Real.sqrt D) *
          (h * Real.exp (-(1 / 2) * (n : ℝ) ^ (κ * ε / (2 * A)))) := by ring
      _ ≤ (Mφ * Mη) * (C * 2 ^ A * Real.sqrt D) *
          ((K + 1) * Real.exp (-(1 / 4) * (n : ℝ) ^ (κ * ε / (2 * A)))) := by gcongr
      _ = _ := by dsimp [F]; ring
  apply (hsplit.trans (add_le_add le_rfl herr')).trans
  dsimp only [T]
  have hmain : 2 ≤ 2 + F := by linarith only [hF]
  have hrem : F ≤ 2 + F := by linarith
  calc
    _ = 2 * (n : ℝ) ^ (κ * ε) * h *
        (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
        F * Real.exp (-(1 / 4) * (n : ℝ) ^ (κ * ε / (2 * A))) * (Mφ * Mη) := by ring
    _ ≤ _ := by gcongr

/-- The same profile estimate for essentially bounded measurable sources.
The constants are chosen before the measurable space and the measure. -/
theorem moment_truncation_ae {A ε κ C B : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hκ : 0 < κ) (hC : 1 ≤ C) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (h : ℝ), 0 < h → h ≤ (n : ℝ) ^ B → ∀ (Y φ η : Ω → ℝ) (Mφ Mη : ℝ),
      Measurable Y → Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
      (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      (∀ p : ℝ, 1 ≤ p → eLpNorm Y (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal (C * p ^ A * h)) →
      Integrable (fun x => φ x * η x * Y x) ν ∧
        |∫ x, φ x * η x * Y x ∂ν| ≤
          D * (n : ℝ) ^ (κ * ε) * h *
            (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          D * Real.exp (-c * (n : ℝ) ^ (κ * ε / (2 * A))) * (Mφ * Mη) := by
  classical
  obtain ⟨c, D, hc, hD, ht⟩ := moment_truncation (B := B) hA hε hκ hC
  refine ⟨c, D, hc, hD, ?_⟩
  intro n hn Ω _ ν _ h hh hhn Y φ η Mφ Mη hY hφ hη hMφ hMη hφM hηM hmom
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
  obtain ⟨hi, hb⟩ := ht n hn ν h hh hhn Y f g Mφ Mη hY hf hg hMφ hMη hff hgg hmom
  refine ⟨hi.congr he, ?_⟩
  rw [integral_congr_ae he,
    integral_congr_ae (hfe.mono fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx),
    integral_congr_ae (hge.mono fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)] at hb
  exact hb

end Riesz2.PolynomialProfileTruncation
