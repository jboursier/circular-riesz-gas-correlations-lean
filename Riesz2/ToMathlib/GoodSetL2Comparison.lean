/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicFourierL2
public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Pairing estimates with a good set

A bounded L² field pairs with a coefficient which is bounded on a good set
and has a squared integrable envelope on its complement. All integrability
claims precede estimates of Bochner integrals. No independence is needed.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped BigOperators

namespace Riesz2.GoodSetL2Comparison

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- On a probability space the integral of the absolute value of an L²
representative is bounded by its L² norm. -/
theorem integral_abs_le_norm [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) :
    (∫ x, |f x| ∂ν) ≤ ‖f‖ := by
  have hsq := (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hh := Riesz1.integral_on_event_le_second_moment
    (Lp.aestronglyMeasurable f).norm (fun x => norm_nonneg (f x))
    (by simpa only [Real.norm_eq_abs, sq_abs] using hsq) MeasurableSet.univ
  simpa only [setIntegral_univ, Real.norm_eq_abs, sq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, Real.sqrt_one,
    Real.one_rpow, mul_one, ← Real.sqrt_eq_rpow, CyclicFourierL2.integral_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)] using hh

/-- A good-set essential bound and a global essential bound control the
source L² norm. In particular a null exceptional event costs nothing. -/
theorem source_norm_le [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν)
    {G : Set X} (hG : MeasurableSet G) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgood : ∀ᵐ x ∂ν.restrict G, |f x| ≤ A)
    (hglobal : ∀ᵐ x ∂ν, |f x| ≤ B) :
    ‖f‖ ≤ A + B * Real.sqrt (ν.real Gᶜ) := by
  have hsq := (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hiG : (∫ x in G, f x ^ 2 ∂ν) ≤ A ^ 2 := by
    calc
      _ ≤ ∫ _ in G, A ^ 2 ∂ν := integral_mono_ae hsq.integrableOn
        (integrable_const _) (hgood.mono fun x hx => by
          dsimp only
          exact (sq_abs (f x)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hx 2))
      _ = ν.real G * A ^ 2 := by
        simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
      _ ≤ A ^ 2 := mul_le_of_le_one_left (sq_nonneg A) measureReal_le_one
  have hiB : (∫ x in Gᶜ, f x ^ 2 ∂ν) ≤ B ^ 2 * ν.real Gᶜ := by
    calc
      _ ≤ ∫ _ in Gᶜ, B ^ 2 ∂ν := integral_mono_ae hsq.integrableOn
        (integrable_const _) ((ae_restrict_of_ae hglobal).mono fun x hx => by
          dsimp only
          exact (sq_abs (f x)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hx 2))
      _ = _ := by
        simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]; ring
  have hsplit := integral_add_compl hG hsq
  rw [CyclicFourierL2.integral_sq] at hsplit
  have hroot := Real.sq_sqrt (measureReal_nonneg (μ := ν) (s := Gᶜ))
  have hcross : 0 ≤ A * (B * Real.sqrt (ν.real Gᶜ)) := by positivity
  have hr : 0 ≤ A + B * Real.sqrt (ν.real Gᶜ) := by positivity
  nlinarith [norm_nonneg f]

/-- A finite nonnegative envelope on an exceptional set gives a finite
coefficient second moment there. The good-set bound supplies the rest. -/
theorem coefficient_memLp_two [IsFiniteMeasure ν]
    (b W : X → ℝ) (hb : AEStronglyMeasurable b ν) {G : Set X}
    (A K : ℝ) (hgood : ∀ᵐ x ∂ν.restrict G, |b x| ≤ A)
    (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, b x ^ 2 ≤ K * W x) :
    MemLp b 2 ν := by
  have hgoodSq : IntegrableOn (fun x => b x ^ 2) G ν :=
    (integrable_const (A ^ 2)).mono' (hb.restrict.pow 2)
      (hgood.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_sq]
        nlinarith [abs_nonneg (b x), sq_abs (b x)])
  have hbadSq : IntegrableOn (fun x => b x ^ 2) Gᶜ ν :=
    (hW.const_mul K).mono' (hb.restrict.pow 2)
      (hsq.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_sq] using hx)
  apply (memLp_two_iff_integrable_sq hb).mpr
  simpa only [union_compl_self, integrableOn_univ] using
    integrableOn_union.mpr ⟨hgoodSq, hbadSq⟩

/-- The exceptional coefficient first moment is at most the square root
of its squared envelope mass. -/
theorem exceptional_integral_abs_le [IsProbabilityMeasure ν]
    (b W : X → ℝ) (hb : MemLp b 2 ν) {G : Set X}
    {K T : ℝ} (hK : 0 ≤ K) (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, b x ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) :
    (∫ x in Gᶜ, |b x| ∂ν) ≤ Real.sqrt (K * T) := by
  have hbi := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb
  have hmass : (∫ x in Gᶜ, b x ^ 2 ∂ν) ≤ K * T := by
    calc
      _ ≤ ∫ x in Gᶜ, K * W x ∂ν :=
        integral_mono_ae hbi.integrableOn (hW.const_mul K) hsq
      _ = K * ∫ x in Gᶜ, W x ∂ν := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hK
  have hh := Riesz1.integral_on_event_le_second_moment
    (μ := ν.restrict Gᶜ) hb.aestronglyMeasurable.restrict.norm
    (fun x => norm_nonneg (b x))
    (by simpa only [Real.norm_eq_abs, sq_abs] using
      (show Integrable (fun x => b x ^ 2) (ν.restrict Gᶜ) from hbi.integrableOn))
    MeasurableSet.univ
  simp only [setIntegral_univ, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow,
    measureReal_restrict_apply_univ] at hh
  have hp : Real.sqrt (ν.real Gᶜ) ≤ 1 :=
    (Real.sqrt_le_sqrt measureReal_le_one).trans_eq Real.sqrt_one
  exact hh.trans ((mul_le_of_le_one_right (Real.sqrt_nonneg _) hp).trans
    (Real.sqrt_le_sqrt hmass))

/-- Good-set L² pairing and exceptional-set supremum pairing, in one
estimate. A square envelope on the exceptional set proves integrability.
There is no need for a global coefficient second-moment hypothesis. -/
theorem pairing_le [IsProbabilityMeasure ν]
    (b W : X → ℝ) (hb : AEStronglyMeasurable b ν)
    (f : Lp ℝ 2 ν) {G : Set X} (hG : MeasurableSet G)
    {A B K T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgood : ∀ᵐ x ∂ν.restrict G, |b x| ≤ A)
    (hf : ∀ᵐ x ∂ν, |f x| ≤ B)
    (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, b x ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) :
    Integrable (fun x => b x * f x) ν ∧
      |∫ x, b x * f x ∂ν| ≤ A * ‖f‖ + B * Real.sqrt (K * T) := by
  have hb2 := coefficient_memLp_two b W hb A K hgood hW hsq
  have hi : Integrable (fun x => b x * f x) ν := hb2.integrable_mul (Lp.memLp f)
  have hgoodI : |∫ x in G, b x * f x ∂ν| ≤ A * ‖f‖ := by
    calc
      _ ≤ ∫ x in G, |b x * f x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x in G, A * |f x| ∂ν := integral_mono_ae hi.abs.integrableOn
        (((Lp.memLp f).integrable one_le_two).abs.const_mul A).integrableOn
        (hgood.mono fun x hx => by
          dsimp only
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
      _ = A * ∫ x in G, |f x| ∂ν := integral_const_mul _ _
      _ ≤ A * ∫ x, |f x| ∂ν := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral ((Lp.memLp f).integrable one_le_two).abs
          (ae_of_all _ fun x => abs_nonneg (f x))) hA
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_norm f) hA
  have hbadI : |∫ x in Gᶜ, b x * f x ∂ν| ≤ B * Real.sqrt (K * T) := by
    calc
      _ ≤ ∫ x in Gᶜ, |b x * f x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x in Gᶜ, B * |b x| ∂ν := integral_mono_ae hi.abs.integrableOn
        ((hb2.integrable one_le_two).abs.const_mul B).integrableOn
        ((ae_restrict_of_ae hf).mono fun x hx => by
          dsimp only
          rw [abs_mul, mul_comm B]
          exact mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = B * ∫ x in Gᶜ, |b x| ∂ν := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (exceptional_integral_abs_le b W hb2 hK hW hsq htail) hB
  refine ⟨hi, ?_⟩
  rw [← integral_add_compl hG hi]
  exact (abs_add_le _ _).trans (add_le_add hgoodI hbadI)

/-- A finite extended weighted tail gives both an integrable envelope
and a real tail bound. If the weight is at least one, it also bounds the
exceptional probability. -/
theorem tail_data [IsProbabilityMeasure ν] (W : X → ℝ)
    (hW : AEStronglyMeasurable W ν) {E : Set X} {T : ℝ} (hT : 0 ≤ T)
    (hWone : ∀ᵐ x ∂ν.restrict E, 1 ≤ W x)
    (htail : (∫⁻ x in E, ENNReal.ofReal (W x) ∂ν) ≤ ENNReal.ofReal T) :
    IntegrableOn W E ν ∧ (∫ x in E, W x ∂ν) ≤ T ∧ ν.real E ≤ T := by
  have hn : ∀ᵐ x ∂ν.restrict E, 0 ≤ W x := hWone.mono fun x hx => by linarith
  have hi : IntegrableOn W E ν := ⟨hW.restrict,
    (hasFiniteIntegral_iff_ofReal hn).mpr (htail.trans_lt ENNReal.ofReal_lt_top)⟩
  have hreal : (∫ x in E, W x ∂ν) ≤ T := by
    apply (ENNReal.ofReal_le_ofReal_iff hT).mp
    rwa [ofReal_integral_eq_lintegral_ofReal hi hn]
  refine ⟨hi, hreal, ?_⟩
  have hh := integral_mono_ae (integrable_const (1 : ℝ)) hi hWone
  simp only [integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hh
  exact hh.trans hreal

/-- Sum the component pairings without losing a factor in the good-set
term. The exceptional term costs exactly the number of components. -/
theorem vector_pairing_le [IsProbabilityMeasure ν]
    {ι : Type*} [Fintype ι] (b : ι → X → ℝ) (W : X → ℝ)
    (hb : ∀ j, AEStronglyMeasurable (b j) ν) (f : ι → Lp ℝ 2 ν)
    {G : Set X} (hG : MeasurableSet G)
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    {A ρ B K T : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgood : ∀ j, ∀ᵐ x ∂ν.restrict G, |b j x| ≤ A * (w j + ρ))
    (hf : ∀ j, ∀ᵐ x ∂ν, |f j x| ≤ B)
    (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ j, ∀ᵐ x ∂ν.restrict Gᶜ, b j x ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) :
    Integrable (fun x => ∑ j, b j x * f j x) ν ∧
      |∫ x, ∑ j, b j x * f j x ∂ν| ≤
        A * ((∑ j, w j * ‖f j‖) + ρ * ∑ j, ‖f j‖) +
          (Fintype.card ι : ℝ) * B * Real.sqrt (K * T) := by
  have hpair (j : ι) := pairing_le (b j) W (hb j) (f j) hG
    (mul_nonneg hA (add_nonneg (hw j) hρ)) hB hK (hgood j) (hf j) hW (hsq j) htail
  have hi := integrable_finsetSum Finset.univ fun j _ => (hpair j).1
  refine ⟨hi, ?_⟩
  rw [integral_finsetSum _ fun j _ => (hpair j).1]
  calc
    _ ≤ ∑ j, |∫ x, b j x * f j x ∂ν| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (A * (w j + ρ) * ‖f j‖ + B * Real.sqrt (K * T)) :=
      Finset.sum_le_sum fun j _ => (hpair j).2
    _ = _ := by
      simp only [add_mul, mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Taking a square root of a stretched-exponential tail and multiplying
by any fixed real power preserves a stretched-exponential bound. -/
theorem sqrt_tail_absorption {A c δ a : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
      n ^ a * Real.sqrt (A * Real.exp (-c * n ^ δ)) ≤
        C * Real.exp (-(c / 4) * n ^ δ) := by
  obtain ⟨M, hM, hm⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := a) (c := c / 2) (c' := c / 4) hδ (by linarith)
  refine ⟨Real.sqrt A * M + 1, by positivity, fun n hn => ?_⟩
  have he : Real.sqrt (A * Real.exp (-c * n ^ δ)) =
      Real.sqrt A * Real.exp (-(c / 2) * n ^ δ) := by
    rw [Real.sqrt_mul hA]
    simp only [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 2
    ring
  rw [he]
  calc
    _ = Real.sqrt A * (n ^ a * Real.exp (-(c / 2) * n ^ δ)) := by ring
    _ ≤ Real.sqrt A * (M * Real.exp (-(c / 4) * n ^ δ)) :=
      mul_le_mul_of_nonneg_left (hm n hn) (Real.sqrt_nonneg _)
    _ ≤ _ := by nlinarith [Real.exp_pos (-(c / 4) * n ^ δ)]

end Riesz2.GoodSetL2Comparison
