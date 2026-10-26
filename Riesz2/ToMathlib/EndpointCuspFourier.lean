/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.EndpointCuspCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The near/far Fourier split at a cusp

Step 1 of Lemma 2.4: direct estimation of the near part and
repeated integration by parts on the far part, which vanishes near the seams.
These estimates are valid for every positive cusp order and every derivative
order. In particular the integration-by-parts step makes no exclusion at
`α = 1`. The remaining power-envelope estimate is separate from this module.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz2.DiscreteInterpolation

/-- A function supported near the two ends of an interval has a short integral.
The estimate also covers overlapping endpoint neighborhoods. It is the direct
bound used in Lemma 2.4, Steps 1 and 3. -/
theorem norm_integral_le_endpoint_support {f : ℝ → ℂ} {T L B : ℝ}
    (hT : 0 < T) (hL : 0 < L) (hB : 0 ≤ B) (hf : Continuous f)
    (hbound : ∀ x ∈ Icc 0 T, ‖f x‖ ≤ B)
    (hzero : ∀ x ∈ Ioo L (T - L), f x = 0) :
    ‖∫ x in (0 : ℝ)..T, f x‖ ≤ 2 * L * B := by
  by_cases hhalf : T ≤ 2 * L
  · have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := T) (C := B) (fun x hx =>
        hbound x (by rw [uIoc_of_le hT.le] at hx; exact ⟨hx.1.le, hx.2⟩))
    simp only [sub_zero, abs_of_pos hT] at hi
    exact hi.trans (by nlinarith)
  · have hLT : L ≤ T - L := by linarith
    have hi0 : (∫ x in L..T - L, f x) = 0 := by
      calc
        _ = ∫ x in L..T - L, (0 : ℂ) := by
          exact intervalIntegral.integral_congr_Ioo_of_le hLT hzero
        _ = 0 := by simp
    have he := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (hf.intervalIntegrable 0 L) (hf.intervalIntegrable L (T - L))
    have he' := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (hf.intervalIntegrable 0 (T - L)) (hf.intervalIntegrable (T - L) T)
    rw [← he', ← he, hi0, add_zero]
    have hb0 : ‖∫ x in (0 : ℝ)..L, f x‖ ≤ B * L := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := L) (C := B) (fun x hx => hbound x (by
          rw [uIoc_of_le hL.le] at hx
          exact ⟨hx.1.le, by linarith [hx.2]⟩))
      simpa only [sub_zero, abs_of_pos hL] using hi
    have hbT : ‖∫ x in T - L..T, f x‖ ≤ B * L := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := T - L) (b := T) (C := B) (fun x hx => hbound x (by
          rw [uIoc_of_le (by linarith : T - L ≤ T)] at hx
          exact ⟨by linarith [hx.1], hx.2⟩))
      simpa only [sub_sub_cancel, abs_of_pos hL] using hi
    exact (norm_add_le _ _).trans (by linarith)

end Riesz2.DiscreteInterpolation

namespace Riesz2.EndpointCuspFourier

open EndpointCuspCutoff

/-- Local smoothness of a derivative for Lemma 2.4, Step 1. -/
theorem contDiffAt_iteratedDeriv {F : ℝ → ℂ} {x : ℝ} {r j m : ℕ}
    (hF : ContDiffAt ℝ r F x) (hjm : m + j ≤ r) :
    ContDiffAt ℝ m (iteratedDeriv j F) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℂ).symm.contDiff.contDiffAt.comp x
    (hF.iteratedFDeriv_right (by exact_mod_cast hjm))

/-- Unit modulus of the Fourier character in Lemma 2.4. -/
private theorem norm_character (n : ℤ) (x : ℝ) :
    ‖Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Derivative of the Fourier character in Lemma 2.4. -/
private theorem hasDerivAt_character (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(n : ℂ) * Complex.I * (y : ℂ)))
      ((-(n : ℂ) * Complex.I) * Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))) x := by
  have hd : HasDerivAt (fun y : ℝ => -(n : ℂ) * Complex.I * (y : ℂ))
      (-(n : ℂ) * Complex.I) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(n : ℂ) * Complex.I)
  simpa only [mul_comm (Complex.exp _) (-(n : ℂ) * Complex.I)] using hd.cexp

/-- The direct bound for the near part of Lemma 2.4, Step 1.
The support has length at most `4a` and the symbol there is at most `B(2a)^α`. -/
theorem near_integral_bound {T a B α : ℝ} (hT : 0 < T) (ha : 0 < a)
    (hTa : 4 * a ≤ T) (hB : 0 ≤ B) (hα : 0 < α) {F : ℝ → ℂ}
    (hF : Continuous F)
    (hb : ∀ x ∈ Icc 0 T, ‖F x‖ ≤ B * (min x (T - x)) ^ α) (n : ℤ) :
    ‖∫ x in (0 : ℝ)..T, (cutoff T a x • F x) *
      Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ ≤
        4 * a * (B * (2 * a) ^ α) := by
  rw [show 4 * a = 2 * (2 * a) by ring]
  apply DiscreteInterpolation.norm_integral_le_endpoint_support (L := 2 * a) hT (by positivity)
    (by positivity)
    (show Continuous (fun x => (cutoff T a x • F x) *
      Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))) from
      ((cutoff_contDiff T a).continuous.smul hF).mul (by fun_prop))
  · intro x hx
    rw [norm_mul, norm_character, mul_one, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (cutoff_mem_Icc ha hTa x).1]
    by_cases hr : min x (T - x) ≤ 2 * a
    · have hp := Real.rpow_le_rpow
        (le_min hx.1 (by linarith [hx.2])) hr hα.le
      exact (mul_le_mul_of_nonneg_right (cutoff_mem_Icc ha hTa x).2 (norm_nonneg _)).trans
        (by
          simpa only [one_mul] using (hb x hx).trans
            (mul_le_mul_of_nonneg_left hp hB))
    · rw [cutoff_eq_zero_of_le_radius ha (le_of_not_ge hr), zero_mul]
      positivity
  · intro x hx
    rw [cutoff_eq_zero ha hx.1.le (by linarith [hx.2]), zero_smul, zero_mul]

/-- Internal repeated integration by parts for Lemma 2.4, Step 1.
All lower boundary jets vanish. The identity is proved for arbitrary finite order,
before any cusp envelope is imposed. -/
theorem integral_eq_inv_pow_mul_iteratedDeriv_internal {T : ℝ} {r : ℕ}
    (hT : 0 < T) {G : ℝ → ℂ}
    (hG : ∀ x ∈ Icc 0 T, ContDiffAt ℝ r G x)
    (hz : ∀ j : ℕ, j < r → iteratedDeriv j G 0 = 0 ∧ iteratedDeriv j G T = 0)
    (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..T, G x * Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))) =
      ((n : ℂ) * Complex.I)⁻¹ ^ r *
        ∫ x in (0 : ℝ)..T, iteratedDeriv r G x *
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ)) := by
  let w := fun x : ℝ => Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))
  let J := fun j : ℕ => ∫ x in (0 : ℝ)..T, iteratedDeriv j G x * w x
  have hw : Continuous w := by fun_prop
  have hc : (n : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
  have hcont (j : ℕ) (hj : j ≤ r) : ContinuousOn (iteratedDeriv j G) (Icc 0 T) := by
    intro x hx
    exact (contDiffAt_iteratedDeriv (hG x hx) (by omega : 0 + j ≤ r)).continuousAt.continuousWithinAt
  have hstep (j : ℕ) (hj : j < r) : J j = ((n : ℂ) * Complex.I)⁻¹ * J (j + 1) := by
    have hjc := hcont j hj.le
    have hj1c := hcont (j + 1) (by omega)
    have hi : IntervalIntegrable (fun x => iteratedDeriv j G x * w x) volume 0 T :=
      (hjc.mul hw.continuousOn).intervalIntegrable_of_Icc hT.le
    have hi1 : IntervalIntegrable (fun x => iteratedDeriv (j + 1) G x * w x) volume 0 T :=
      (hj1c.mul hw.continuousOn).intervalIntegrable_of_Icc hT.le
    have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
      (hjc.mul hw.continuousOn)
      (f' := fun x => iteratedDeriv (j + 1) G x * w x +
        (-(n : ℂ) * Complex.I) * (iteratedDeriv j G x * w x))
      (fun x hx => by
        have hd := (contDiffAt_iteratedDeriv (hG x (Ioo_subset_Icc_self hx))
          (by omega : 1 + j ≤ r)).differentiableAt (by norm_num)
        convert hd.hasDerivAt.mul (hasDerivAt_character n x) using 1
        dsimp only [w]
        rw [iteratedDeriv_succ]
        ring)
      (hi1.add (hi.const_mul (-(n : ℂ) * Complex.I)))
    rw [intervalIntegral.integral_add hi1 (hi.const_mul _),
      intervalIntegral.integral_const_mul, Pi.mul_apply, Pi.mul_apply, (hz j hj).1, (hz j hj).2,
      zero_mul, zero_mul, sub_self] at hp
    change J (j + 1) + (-(n : ℂ) * Complex.I) * J j = 0 at hp
    apply (mul_left_cancel₀ hc)
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    linear_combination -hp
  have hind (j : ℕ) (hj : j ≤ r) : J 0 = ((n : ℂ) * Complex.I)⁻¹ ^ j * J j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih (by omega), hstep j (by omega), pow_succ]
      ring
  simpa only [J, iteratedDeriv_zero] using hind r le_rfl

/-- The far part of Lemma 2.4, Step 1, can be integrated by parts
`r` times without boundary terms. This includes `r = 3, α = 1`: no seam extension
of a derivative of the original symbol is required. -/
theorem far_integral_eq_inv_pow_mul_iteratedDeriv {T a : ℝ} {r : ℕ}
    (hT : 0 < T) (ha : 0 < a) (hTa : 3 * a ≤ T) {F : ℝ → ℂ}
    (hF : ContDiffOn ℝ r F (Ioo 0 T)) (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..T, farPart T a F x *
      Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))) =
      ((n : ℂ) * Complex.I)⁻¹ ^ r *
        ∫ x in (0 : ℝ)..T, iteratedDeriv r (farPart T a F) x *
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ)) := by
  exact integral_eq_inv_pow_mul_iteratedDeriv_internal hT
    (fun _ hx => farPart_contDiffAt ha hTa hF hx)
    (fun j _ => farPart_endpoint_derivatives ha hTa F j) n hn

/-- The high-frequency cost of the far part in Lemma 2.4, Step 1,
is exactly `|n|⁻ʳ` before estimating the highest derivative integral. -/
theorem far_integral_norm_eq {T a : ℝ} {r : ℕ}
    (hT : 0 < T) (ha : 0 < a) (hTa : 3 * a ≤ T) {F : ℝ → ℂ}
    (hF : ContDiffOn ℝ r F (Ioo 0 T)) (n : ℤ) (hn : n ≠ 0) :
    ‖∫ x in (0 : ℝ)..T, farPart T a F x *
      Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ =
      |(n : ℝ)|⁻¹ ^ r * ‖∫ x in (0 : ℝ)..T,
        iteratedDeriv r (farPart T a F) x *
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ := by
  rw [far_integral_eq_inv_pow_mul_iteratedDeriv hT ha hTa hF n hn,
    norm_mul, norm_pow, norm_inv, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_intCast]

/-- The near/far estimate of Lemma 2.4, Step 1, before the
Leibniz and power-envelope estimate of the highest far derivative. The symbol
is cut off first and only the far part is differentiated. -/
theorem near_far_integral_bound {T a B α : ℝ} {r : ℕ}
    (hT : 0 < T) (ha : 0 < a) (hTa : 4 * a ≤ T) (hB : 0 ≤ B) (hα : 0 < α)
    {F : ℝ → ℂ} (hF : Continuous F) (hFs : ContDiffOn ℝ r F (Ioo 0 T))
    (hb : ∀ x ∈ Icc 0 T, ‖F x‖ ≤ B * (min x (T - x)) ^ α)
    (n : ℤ) (hn : n ≠ 0) :
    ‖∫ x in (0 : ℝ)..T, F x * Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ ≤
      4 * a * (B * (2 * a) ^ α) +
        |(n : ℝ)|⁻¹ ^ r * ‖∫ x in (0 : ℝ)..T,
          iteratedDeriv r (farPart T a F) x *
            Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ := by
  let w := fun x : ℝ => Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))
  have hw : Continuous w := by fun_prop
  have hnear : Continuous (fun x => (cutoff T a x • F x) * w x) :=
    ((cutoff_contDiff T a).continuous.smul hF).mul hw
  have hfar : Continuous (fun x => farPart T a F x * w x) :=
    ((continuous_const.sub (cutoff_contDiff T a).continuous).smul hF).mul hw
  have he : (∫ x in (0 : ℝ)..T, F x * w x) =
      (∫ x in (0 : ℝ)..T, (cutoff T a x • F x) * w x) +
        ∫ x in (0 : ℝ)..T, farPart T a F x * w x := by
    rw [← intervalIntegral.integral_add (hnear.intervalIntegrable 0 T)
      (hfar.intervalIntegrable 0 T)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [← add_mul, near_add_far]
  rw [he]
  have h3 : 3 * a ≤ T := by linarith
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ 4 * a * (B * (2 * a) ^ α) +
        ‖∫ x in (0 : ℝ)..T, farPart T a F x * w x‖ :=
      add_le_add (near_integral_bound hT ha hTa hB hα hF hb n) le_rfl
    _ = _ := by rw [far_integral_norm_eq hT ha h3 hFs n hn]

end Riesz2.EndpointCuspFourier
