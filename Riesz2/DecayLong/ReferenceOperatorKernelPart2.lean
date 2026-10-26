/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ReferenceOperatorKernel

/-!
# Scalar half-generator reference kernel

The scalar spectral `σ = 1/2` entry estimate in the proof of Proposition 5.15. The scalar spectral parameter is uniform,
including zero. The operator calculus and form-domain construction are separate.
-/

@[expose] public section
noncomputable section

open Matrix Set Filter
open scoped BigOperators Fin.NatCast NNReal Topology ContDiff

namespace Riesz2.ReferenceOperatorKernel

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Internal scalar estimate for the half-generator multiplier in the proof of Proposition 5.15. -/
theorem half_resolvent_bound_internal {A μ f : ℝ} (hA : 0 < A) (hμ : 0 ≤ μ)
    (hf : A + μ ≤ f) : Real.sqrt μ * f⁻¹ ≤ (Real.sqrt A)⁻¹ := by
  have hr : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hf0 : 0 < f := by linarith
  have hs := sq_nonneg (Real.sqrt A - Real.sqrt μ)
  have hsA := Real.sq_sqrt hA.le
  have hsμ := Real.sq_sqrt hμ
  rw [← div_eq_mul_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ hf0 hr).mpr
  nlinarith only [hf, hs, hsA, hsμ,
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg μ)]

/-- Internal power envelopes for the first three weighted reciprocal powers.
These are the denominator estimates for the proof of Proposition 5.15. -/
theorem half_reciprocal_powers_internal {c r a μ f : ℝ} (hc : 0 < c)
    (hr : 0 < r) (hμ : 0 ≤ μ) (hf : c * r ^ a + μ ≤ f) :
    Real.sqrt μ * f⁻¹ ≤ (Real.sqrt c)⁻¹ * r ^ (-a / 2) ∧
    Real.sqrt μ * f⁻¹ ^ 2 ≤ (Real.sqrt c)⁻¹ * c⁻¹ * r ^ (-a / 2 - a) ∧
    Real.sqrt μ * f⁻¹ ^ 3 ≤ (Real.sqrt c)⁻¹ * c⁻¹ ^ 2 * r ^ (-a / 2 - 2 * a) := by
  have hf0 : 0 < f := (mul_pos hc (Real.rpow_pos_of_pos hr a)).trans_le (by linarith)
  have hi : f⁻¹ ≤ c⁻¹ * r ^ (-a) := by
    have hh := ReciprocalCusp.inv_bound hc hr (show c * r ^ a ≤ f by linarith)
    rwa [abs_of_pos (inv_pos.mpr hf0)] at hh
  have hh : Real.sqrt μ * f⁻¹ ≤ (Real.sqrt c)⁻¹ * r ^ (-a / 2) := by
    have hb := half_resolvent_bound_internal (mul_pos hc (Real.rpow_pos_of_pos hr a)) hμ hf
    convert hb using 1
    rw [Real.sqrt_mul hc.le, mul_inv]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hr.le, ← Real.rpow_neg hr.le]
    congr 2
    ring
  refine ⟨hh, ?_, ?_⟩
  · calc
      _ = (Real.sqrt μ * f⁻¹) * f⁻¹ := by ring
      _ ≤ ((Real.sqrt c)⁻¹ * r ^ (-a / 2)) * (c⁻¹ * r ^ (-a)) :=
        mul_le_mul hh hi (inv_nonneg.mpr hf0.le) (by positivity)
      _ = _ := by rw [← mul_assoc, mul_right_comm _ _ c⁻¹, mul_assoc,
          ← Real.rpow_add hr]; congr 2
  · calc
      _ = (Real.sqrt μ * f⁻¹) * f⁻¹ ^ 2 := by ring
      _ ≤ ((Real.sqrt c)⁻¹ * r ^ (-a / 2)) * (c⁻¹ * r ^ (-a)) ^ 2 :=
        mul_le_mul hh (pow_le_pow_left₀ (inv_nonneg.mpr hf0.le) hi 2)
          (sq_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le (-a) 2]
        norm_num only [Nat.cast_ofNat]
        calc
          _ = ((Real.sqrt c)⁻¹ * c⁻¹ ^ 2) *
              (r ^ (-a / 2) * r ^ (-a * 2)) := by ring
          _ = _ := by rw [← Real.rpow_add hr]; congr 2; ring

/-- Uniform order-two cusp bounds for the scalar half-generator multiplier
in the proof of Proposition 5.15. -/
theorem half_shifted_reciprocal_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ → ∀ j : ℕ, j ≤ 2 →
      ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        Real.sqrt μ * |iteratedDeriv j (fun y : ℝ =>
          (μ + 2 * (2 + symbolZetaFactor s *
            Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))))⁻¹) θ.val| ≤
          C * symbolEndpointDistance θ ^ ((1 - s.val) / 2 - (j : ℝ)) := by
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  obtain ⟨c, _, hc, _, hlower⟩ := latticeRieszSymbol_power_bounds hz s
  obtain ⟨D, hD, hd1⟩ := latticeRieszSymbol_all_derivatives hz s 1
  obtain ⟨E, hE, hd2⟩ := latticeRieszSymbol_all_derivatives hz s 2
  let c' := 2 * c
  let D' := 2 * D
  let E' := 2 * E
  let b := (Real.sqrt c')⁻¹
  let C := b + D' * b * c'⁻¹ + (2 * D' ^ 2 * b * c'⁻¹ ^ 2 + E' * b * c'⁻¹)
  have hc' : 0 < c' := by dsimp [c']; positivity
  have hb : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr hc')
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hterm1 : 0 ≤ D' * b * c'⁻¹ := by positivity
  have hterm2 : 0 ≤ 2 * D' ^ 2 * b * c'⁻¹ ^ 2 + E' * b * c'⁻¹ := by positivity
  have hC0 : b ≤ C := by dsimp [C]; linarith only [hterm1, hterm2]
  have hC1 : D' * b * c'⁻¹ ≤ C := by dsimp [C]; linarith only [hb, hterm2]
  have hC2 : 2 * D' ^ 2 * b * c'⁻¹ ^ 2 + E' * b * c'⁻¹ ≤ C := by
    dsimp [C]; linarith only [hb, hterm1]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro μ hμ j hj θ
  let Q := fun y : ℝ => μ + 2 * F y
  have hQ : ContDiffOn ℝ 2 Q (Ioo 0 (2 * Real.pi)) :=
    (contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))).of_le
      (by norm_num)
  have hpos (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) : 0 < Q y := by
    have hh : 0 < F y := by
      dsimp [F]
      rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
      exact latticeRieszSymbol_pos s _
    dsimp [Q]
    positivity
  have hne : ∀ y ∈ Ioo 0 (2 * Real.pi), Q y ≠ 0 := fun y hy => (hpos y hy).ne'
  have hρ := symbolEndpointDistance_pos θ
  have hlo : c' * symbolEndpointDistance θ ^ (s.val - 1) + μ ≤ Q θ.val := by
    have hh := (hlower θ).1
    rw [latticeRieszSymbol_eq_hurwitzKernel hz s θ] at hh
    dsimp only [Q, c', F]
    linarith
  have hder1 : |deriv Q θ.val| ≤ D' * symbolEndpointDistance θ ^ (s.val - 1 - 1) := by
    have heq : deriv Q θ.val = 2 * iteratedDeriv 1 F θ.val := by
      rw [show deriv Q θ.val = iteratedDeriv 1 Q θ.val by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      dsimp only [Q]
      rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field]
    rw [heq, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [D', F, Nat.cast_one, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hd1 θ) two_pos.le)
  have hder2 : |deriv (deriv Q) θ.val| ≤ E' * symbolEndpointDistance θ ^ (s.val - 1 - 2) := by
    have heq : deriv (deriv Q) θ.val = 2 * iteratedDeriv 2 F θ.val := by
      rw [show deriv (deriv Q) θ.val = iteratedDeriv 2 Q θ.val by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      dsimp only [Q]
      rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field]
    rw [heq, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [E', F, Nat.cast_ofNat, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hd2 θ) two_pos.le)
  have hQpos := hpos _ θ.property
  obtain ⟨h0, h1, h2⟩ := half_reciprocal_powers_internal hc' hρ hμ hlo
  change Real.sqrt μ * |iteratedDeriv j (fun y => (Q y)⁻¹) θ.val| ≤ _
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    rw [abs_of_pos (inv_pos.mpr (hpos _ θ.property))]
    have he : -(s.val - 1) / 2 = (1 - s.val) / 2 := by ring
    rw [he] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right hC0 (by positivity))
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_one]
    rw [deriv_fun_inv'' ((hQ.contDiffAt (isOpen_Ioo.mem_nhds θ.property)).differentiableAt
      (by norm_num)) (hne _ θ.property)]
    have hh : Real.sqrt μ * |-deriv Q θ.val / Q θ.val ^ 2| ≤
        (D' * b * c'⁻¹) * symbolEndpointDistance θ ^ ((1 - s.val) / 2 - 1) := by
      calc
        _ = |deriv Q θ.val| * (Real.sqrt μ * (Q θ.val)⁻¹ ^ 2) := by
          rw [abs_div, abs_neg, abs_pow, abs_of_pos (hpos _ θ.property)]
          rw [div_eq_mul_inv, ← inv_pow]; ring
        _ ≤ (D' * symbolEndpointDistance θ ^ (s.val - 1 - 1)) *
            (b * c'⁻¹ * symbolEndpointDistance θ ^ (-(s.val - 1) / 2 - (s.val - 1))) :=
          mul_le_mul hder1 h1 (by positivity) (by positivity)
        _ = _ := by
          calc
            _ = (D' * b * c'⁻¹) * (symbolEndpointDistance θ ^ (s.val - 1 - 1) *
                symbolEndpointDistance θ ^ (-(s.val - 1) / 2 - (s.val - 1))) := by ring
            _ = _ := by rw [← Real.rpow_add hρ]; congr 2; ring
    exact hh.trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat]
    rw [ReciprocalCusp.second_derivative isOpen_Ioo hQ hne θ.property]
    have ht1 : Real.sqrt μ * |2 * deriv Q θ.val ^ 2 * (Q θ.val)⁻¹ ^ 3| ≤
        (2 * D' ^ 2 * b * c'⁻¹ ^ 2) *
          symbolEndpointDistance θ ^ ((1 - s.val) / 2 - 2) := by
      calc
        _ = 2 * |deriv Q θ.val| ^ 2 * (Real.sqrt μ * (Q θ.val)⁻¹ ^ 3) := by
          rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (inv_pos.mpr (hpos _ θ.property))]
          norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring
        _ ≤ 2 * (D' * symbolEndpointDistance θ ^ (s.val - 1 - 1)) ^ 2 *
            (b * c'⁻¹ ^ 2 * symbolEndpointDistance θ ^ (-(s.val - 1) / 2 - 2 * (s.val - 1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) hder1 2) (by norm_num)) h2
            (by positivity) (by positivity)
        _ = _ := by
          rw [mul_pow, ← Real.rpow_mul_natCast hρ.le (s.val - 1 - 1) 2]
          norm_num only [Nat.cast_ofNat]
          calc
            _ = (2 * D' ^ 2 * b * c'⁻¹ ^ 2) *
                (symbolEndpointDistance θ ^ ((s.val - 1 - 1) * 2) *
                  symbolEndpointDistance θ ^ (-(s.val - 1) / 2 - 2 * (s.val - 1))) := by ring
            _ = _ := by rw [← Real.rpow_add hρ]; congr 2; ring
    have ht2 : Real.sqrt μ * |deriv (deriv Q) θ.val * (Q θ.val)⁻¹ ^ 2| ≤
        (E' * b * c'⁻¹) * symbolEndpointDistance θ ^ ((1 - s.val) / 2 - 2) := by
      calc
        _ = |deriv (deriv Q) θ.val| * (Real.sqrt μ * (Q θ.val)⁻¹ ^ 2) := by
          rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr (hpos _ θ.property))]; ring
        _ ≤ (E' * symbolEndpointDistance θ ^ (s.val - 1 - 2)) *
            (b * c'⁻¹ * symbolEndpointDistance θ ^ (-(s.val - 1) / 2 - (s.val - 1))) :=
          mul_le_mul hder2 h1 (by positivity) (by positivity)
        _ = _ := by
          calc
            _ = (E' * b * c'⁻¹) * (symbolEndpointDistance θ ^ (s.val - 1 - 2) *
                symbolEndpointDistance θ ^ (-(s.val - 1) / 2 - (s.val - 1))) := by ring
            _ = _ := by rw [← Real.rpow_add hρ]; congr 2; ring
    calc
      _ ≤ Real.sqrt μ * (|2 * deriv Q θ.val ^ 2 * (Q θ.val)⁻¹ ^ 3| +
          |deriv (deriv Q) θ.val * (Q θ.val)⁻¹ ^ 2|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg μ)
      _ ≤ (2 * D' ^ 2 * b * c'⁻¹ ^ 2 + E' * b * c'⁻¹) *
          symbolEndpointDistance θ ^ ((1 - s.val) / 2 - 2) := by
        rw [mul_add]
        exact (add_le_add ht1 ht2).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (by positivity)

/-- Continuous multiplier with the half cusp, uniformly in the spectral shift.
Support for the proof of Proposition 5.15. -/
theorem exists_half_multiplier (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ →
      ∃ H : C(AddCircle (2 * Real.pi), ℂ), H 0 = 0 ∧
        ContDiffOn ℝ 2 (fun y : ℝ => H (y : AddCircle (2 * Real.pi)))
          (Ioo 0 (2 * Real.pi)) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ y ∈ Ioo (0 : ℝ) (2 * Real.pi),
          ‖iteratedDeriv j (fun z : ℝ => H (z : AddCircle (2 * Real.pi))) y‖ ≤
            C * (min y (2 * Real.pi - y)) ^ ((1 - s.val) / 2 - (j : ℝ))) ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          H (θ.val : AddCircle (2 * Real.pi)) =
            ((Real.sqrt μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := half_shifted_reciprocal_bounds hz s
  refine ⟨C, hC, ?_⟩
  intro μ hμ
  let r := reciprocalRieszSymbol s
  let h : AddCircle (2 * Real.pi) → ℝ := fun x => Real.sqrt μ * r x / (2 + μ * r x)
  have hr := continuous_reciprocalRieszSymbol hz s
  have hden (x : AddCircle (2 * Real.pi)) : 2 + μ * r x ≠ 0 := by
    have hh := GlobalResolventKernelInternal.reciprocal_nonneg s x
    exact (by positivity : 0 < 2 + μ * r x).ne'
  have hhc : Continuous h :=
    (continuous_const.mul hr).div (continuous_const.add (continuous_const.mul hr)) hden
  let H : C(AddCircle (2 * Real.pi), ℂ) := ⟨fun x => (h x : ℂ), Complex.continuous_ofReal.comp hhc⟩
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  let Q := fun y : ℝ => μ + 2 * F y
  have hFpos (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) : 0 < F y := by
    dsimp only [F]
    rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    exact latticeRieszSymbol_pos s _
  have hQne : ∀ y ∈ Ioo 0 (2 * Real.pi), Q y ≠ 0 := by
    intro y hy
    have hp := hFpos y hy
    exact (by dsimp [Q]; positivity : 0 < Q y).ne'
  have heq (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      h (y : AddCircle (2 * Real.pi)) = Real.sqrt μ * (Q y)⁻¹ := by
    dsimp only [h, r]
    rw [reciprocalRieszSymbol_coe s ⟨y, hy⟩, latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    change Real.sqrt μ * (F y)⁻¹ / (2 + μ * (F y)⁻¹) = Real.sqrt μ * (Q y)⁻¹
    have hp := hFpos y hy
    have hq := hQne y hy
    have hd : 2 + μ * (F y)⁻¹ ≠ 0 := by positivity
    dsimp only [Q] at hq ⊢
    field_simp
    ring
  have hev {y : ℝ} (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      (fun z : ℝ => h (z : AddCircle (2 * Real.pi))) =ᶠ[𝓝 y]
        (fun z => Real.sqrt μ * (Q z)⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact heq z hz
  have hQ : ContDiffOn ℝ ∞ Q (Ioo 0 (2 * Real.pi)) :=
    contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))
  have hhs : ContDiffOn ℝ 2 (fun z : ℝ => h (z : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) := by
    exact (contDiffOn_const.mul (hQ.inv hQne)).of_le (by norm_num) |>.congr
      (fun y hy => heq y hy)
  refine ⟨H, ?_, Complex.ofRealCLM.contDiff.comp_contDiffOn hhs, ?_, ?_⟩
  · simp only [H, ContinuousMap.coe_mk, h, r,
      reciprocalRieszSymbol_zero, mul_zero, zero_div, Complex.ofReal_zero]
  · intro j hj y hy
    have hs : ContDiffAt ℝ j (fun z : ℝ => h (z : AddCircle (2 * Real.pi))) y :=
      (hhs.contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast hj)
    have hi := iteratedDeriv_smul_const hs (1 : ℂ)
    simp only [Complex.real_smul, mul_one] at hi
    change ‖iteratedDeriv j (fun z : ℝ => (h (z : AddCircle (2 * Real.pi)) : ℂ)) y‖ ≤ _
    rw [hi, Complex.norm_real, Real.norm_eq_abs, (hev hy).iteratedDeriv_eq j,
      iteratedDeriv_const_mul_field, abs_mul, abs_of_nonneg (Real.sqrt_nonneg μ)]
    simpa only [Q, F, symbolEndpointDistance] using hb μ hμ j hj ⟨y, hy⟩
  · intro θ
    change (h (θ.val : AddCircle (2 * Real.pi)) : ℂ) = _
    rw [heq θ θ.property]
    have hFe : F θ.val = latticeRieszSymbol s θ :=
      (latticeRieszSymbol_eq_hurwitzKernel hz s θ).symm
    simp only [Q, hFe, div_eq_mul_inv, add_comm μ]


/-- Absolutely summable scalar half-generator Fourier coefficients, uniform
in the shift (the proof of Proposition 5.15). -/
theorem exists_half_coefficients (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ → ∃ φ : ℤ → ℂ,
      (∀ n : ℤ, ‖φ n‖ ≤ C / (1 + |(n : ℝ)| ^ (1 + (1 - s.val) / 2))) ∧
      ∃ hφ : Summable (fun n => ‖φ n‖), latticeFourier φ hφ 0 = 0 ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          latticeFourier φ hφ θ.val = ((Real.sqrt μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  obtain ⟨A, hA, hm⟩ := exists_half_multiplier hz s
  obtain ⟨K, hK, hb⟩ := FractionalCuspFourier.fractional_cusp_fourier
    (by linarith [s.property.2] : 0 < (1 - s.val) / 2)
    (by linarith [s.property.1] : (1 - s.val) / 2 < 1)
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro μ hμ
  obtain ⟨H, hH0, hHs, hHd, hHe⟩ := hm μ hμ
  obtain ⟨hdec, hφ, hre, _, _⟩ := hb A hA H hH0 hHs hHd
  refine ⟨fourierCoeff H, ?_, hφ, ?_, ?_⟩
  · intro n
    simpa only [mul_assoc] using hdec n
  · simpa only [AddCircle.coe_zero, hH0] using hre 0
  · intro θ
    rw [hre]
    exact hHe θ


/-- Internal aliasing identity for the half multiplier in the proof of Proposition 5.15. The constant mode is retained exactly. -/
theorem half_aliasing_internal (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (μ : ℝ) (hμ : 0 < μ)
    (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (hzero : latticeFourier φ hφ 0 = 0)
    (hfreq : ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      latticeFourier φ hφ θ.val =
        ((Real.sqrt μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ))
    (h : Fin (N : ℕ)) :
    (((Real.sqrt μ)⁻¹ * factorizationMatrix s N hN μ hμ 0 0 h : ℝ) : ℂ) =
      periodizeSequence N φ hφ h +
        ((Real.sqrt μ : ℝ) : ℂ) /
          ((N : ℂ) * (2 * ((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ) + (μ : ℂ))) := by
  let ell : ℝ := 2 * ∑ k, sampledRieszKernel s N hN k
  let c : ℂ := (Real.sqrt μ : ℂ) / ((N : ℂ) * ((ell + μ : ℝ) : ℂ))
  have hr : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hcancel : (Real.sqrt μ)⁻¹ * μ = Real.sqrt μ := by
    calc
      _ = (Real.sqrt μ)⁻¹ * (Real.sqrt μ) ^ 2 :=
        congrArg (fun z : ℝ => (Real.sqrt μ)⁻¹ * z) (Real.sq_sqrt hμ.le).symm
      _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hfour (k : Fin (N : ℕ)) :
      cycleFourier N (fun h => (((Real.sqrt μ)⁻¹ *
        factorizationMatrix s N hN μ hμ 0 0 h : ℝ) : ℂ)) k =
      (((Real.sqrt μ)⁻¹ : ℝ) : ℂ) *
        cycleFourier N (fun h => (factorizationMatrix s N hN μ hμ 0 0 h : ℂ)) k := by
    simp only [cycleFourier, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
  have heq : (fun h => (((Real.sqrt μ)⁻¹ *
      factorizationMatrix s N hN μ hμ 0 0 h : ℝ) : ℂ)) =
      (fun h => periodizeSequence N φ hφ h + c) := by
    apply cycleFourier_injective N
    funext k
    have hs : cycleFourier N (fun h => periodizeSequence N φ hφ h + c) k =
        latticeFourier φ hφ (cycleAngle N k) + (if k = 0 then (N : ℂ) * c else 0) := by
      have hh : cycleFourier N (fun h => periodizeSequence N φ hφ h + c) k =
          cycleFourier N (periodizeSequence N φ hφ) k + cycleFourier N (fun _ => c) k := by
        simp only [cycleFourier, add_mul, Finset.sum_add_distrib]
      rw [hh, inverse_aliasing, cycleFourier_const]
    rw [hfour, hs]
    by_cases hk : k = 0
    · subst k
      rw [factorizationMatrix_fourier_zero]
      simp only [zero_pow (by omega : 2 ≠ 0), zero_div, add_zero,
        cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
        hzero, ↓reduceIte, zero_add]
      change (((Real.sqrt μ)⁻¹ : ℝ) : ℂ) * ((μ / (ell + μ) : ℝ) : ℂ) = (N : ℂ) * c
      have hleft : (Real.sqrt μ)⁻¹ * (μ / (ell + μ)) = Real.sqrt μ / (ell + μ) := by
        rw [div_eq_mul_inv, ← mul_assoc, hcancel, ← div_eq_mul_inv]
      rw [← Complex.ofReal_mul, hleft, Complex.ofReal_div]
      dsimp only [c]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      calc
        _ = ((N : ℂ) * (N : ℂ)⁻¹) *
            ((Real.sqrt μ : ℂ) * ((ell + μ : ℝ) : ℂ)⁻¹) := by
          rw [mul_inv_cancel₀ hN0, one_mul]
        _ = _ := by ring
    · rw [factorizationMatrix_fourier_nonzero s N hN μ hμ 0 k hk,
        hfreq ⟨_, cycleAngle_mem_Ioo N k hk⟩, ite_eq_right hk, add_zero]
      simp only [zero_pow (by omega : 2 ≠ 0), zero_div, add_zero]
      rw [← Complex.ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← mul_assoc, hcancel, ← div_eq_mul_inv]
  simpa only [c, ell, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    congrFun heq h

/-- Uniform half-generator entry decay for the normalized factorization
(the proof of Proposition 5.15, scalar spectral estimate). -/
theorem factorizationMatrix_half_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (μ : ℝ) (hμ : 0 < μ) (h : Fin (N : ℕ)),
      (Real.sqrt μ)⁻¹ * |factorizationMatrix s N hN μ hμ 0 0 h| ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(1 + (1 - s.val) / 2)) := by
  let p := 1 + (1 - s.val) / 2
  have hp : 1 < p := by dsimp [p]; linarith [s.property.2]
  obtain ⟨A, hA, hcoeff⟩ := exists_half_coefficients hz s
  obtain ⟨T, hT, htail⟩ := inverse_power_sum hp
  obtain ⟨c, _, hc, _, hmode⟩ := sampledRieszKernel_zero_mode_bounds s
  refine ⟨(A * T + 2 / Real.sqrt c) * 2 ^ p, by positivity, ?_⟩
  intro N hN μ hμ h
  obtain ⟨φ, hφb, hφ, hzero, hfreq⟩ := hcoeff μ hμ.le
  let mass := ∑ k, sampledRieszKernel s N hN k
  let d : ℝ := Riesz1.cyclicIndexDistance N h 0
  let D := 1 + d ^ p
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hD : 0 < D := by dsimp [D]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlower : c * (N : ℝ) ^ (1 - s.val) ≤ mass := (hmode N hN).1
  have hmass : 0 < mass := (by positivity : 0 < c * (N : ℝ) ^ (1 - s.val)).trans_le hlower
  have hden : 0 < 2 * mass + μ := by positivity
  have hr : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  obtain ⟨hts, htb, hnp⟩ := htail N hN h.val
  rw [GlobalResolventKernelInternal.distance_nat] at htb hnp
  have hperiod : ‖periodizeSequence N φ hφ h‖ ≤ A * T / D := by
    calc
      _ ≤ ∑' l : ℤ, ‖φ ((h.val : ℤ) + l * (N : ℕ))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_periodizeSequence N φ hφ h.val)
      _ ≤ ∑' l : ℤ, A *
          (1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p)) := by
        apply Summable.tsum_le_tsum _ (summable_norm_periodizeSequence N φ hφ h.val) (hts.mul_left _)
        intro l
        convert hφb ((h.val : ℤ) + l * (N : ℕ)) using 1
        push_cast
        ring
      _ = A * ∑' l : ℤ, 1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p) := tsum_mul_left
      _ ≤ A * (T / D) := mul_le_mul_of_nonneg_left htb hA.le
      _ = _ := by ring
  have hmasshalf : Real.sqrt μ * (2 * mass + μ)⁻¹ ≤
      (Real.sqrt c)⁻¹ * (N : ℝ) ^ (-(1 - s.val) / 2) := by
    have hh := half_resolvent_bound_internal
      (mul_pos hc (Real.rpow_pos_of_pos hNpos (1 - s.val))) hμ.le
      (show c * (N : ℝ) ^ (1 - s.val) + μ ≤ 2 * mass + μ by linarith)
    convert hh using 1
    rw [Real.sqrt_mul hc.le, mul_inv]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hNpos.le, ← Real.rpow_neg hNpos.le]
    congr 2
    ring
  have hconst : Real.sqrt μ / ((N : ℝ) * (2 * mass + μ)) ≤
      (2 / Real.sqrt c) / D := by
    calc
      _ = (N : ℝ)⁻¹ * (Real.sqrt μ * (2 * mass + μ)⁻¹) := by
        rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ (N : ℝ)⁻¹ * ((Real.sqrt c)⁻¹ * (N : ℝ) ^ (-(1 - s.val) / 2)) :=
        mul_le_mul_of_nonneg_left hmasshalf (by positivity)
      _ = (Real.sqrt c)⁻¹ * (N : ℝ) ^ (-p) := by
        rw [← Real.rpow_neg_one]
        calc
          _ = (Real.sqrt c)⁻¹ * ((N : ℝ) ^ (-1 : ℝ) *
              (N : ℝ) ^ (-(1 - s.val) / 2)) := by ring
          _ = _ := by rw [← Real.rpow_add hNpos]; dsimp [p]; congr 2; ring
      _ ≤ (Real.sqrt c)⁻¹ * (2 / D) := mul_le_mul_of_nonneg_left hnp (by positivity)
      _ = _ := by ring
  have heq := half_aliasing_internal s N hN μ hμ φ hφ hzero hfreq h
  have hnorm : (Real.sqrt μ)⁻¹ * |factorizationMatrix s N hN μ hμ 0 0 h| ≤
      ‖periodizeSequence N φ hφ h‖ + Real.sqrt μ / ((N : ℝ) * (2 * mass + μ)) := by
    rw [← abs_of_pos (inv_pos.mpr hr), ← abs_mul, ← Real.norm_eq_abs,
      ← Complex.norm_real, heq]
    have hh := norm_add_le (periodizeSequence N φ hφ h)
      ((Real.sqrt μ : ℂ) / ((N : ℂ) * ((2 * mass + μ : ℝ) : ℂ)))
    convert hh using 1
    · simp only [mass, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
    · simp only [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hden]
  have htotal : (Real.sqrt μ)⁻¹ * |factorizationMatrix s N hN μ hμ 0 0 h| ≤
      (A * T + 2 / Real.sqrt c) / D := by
    have hh := hnorm.trans (add_le_add hperiod hconst)
    convert hh using 1
    ring
  have henv := GlobalResolventKernelInternal.power_envelope_compare (by linarith : 0 ≤ p) hd
  calc
    _ ≤ (A * T + 2 / Real.sqrt c) / D := htotal
    _ ≤ (A * T + 2 / Real.sqrt c) * (2 ^ p * (1 + d) ^ (-p)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left henv (by positivity : 0 ≤ A * T + 2 / Real.sqrt c)
    _ = _ := by ring

/-- The uniform scalar spectral half-generator entry estimate of the proof of Proposition 5.15: the constant depends only on `s, β`,
and precedes the cycle size, nonnegative spectral parameter and entry. -/
theorem spectralInverse_half_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0)
      (h : Fin (N : ℕ)),
      Real.sqrt t * |spectralInverse s β N hN t 0 h| ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(1 + (1 - s.val) / 2)) := by
  obtain ⟨A, hA, hb⟩ := factorizationMatrix_half_decay hz s
  have hβroot : 0 < Real.sqrt β.val := Real.sqrt_pos.mpr β.property
  refine ⟨(Real.sqrt β.val)⁻¹ * A, by positivity, ?_⟩
  intro N hN t h
  rcases eq_or_lt_of_le t.property with ht | ht
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp ht.symm
    subst t
    simp only [NNReal.coe_zero, Real.sqrt_zero, zero_mul]
    positivity
  · let μ := (t : ℝ) / β.val
    have hμ : 0 < μ := div_pos ht β.property
    have hscale : Real.sqrt (t : ℝ) * (t : ℝ)⁻¹ =
        (Real.sqrt β.val)⁻¹ * (Real.sqrt μ)⁻¹ := by
      have hrootdiv : Real.sqrt μ = Real.sqrt (t : ℝ) / Real.sqrt β.val :=
        Real.sqrt_div ht.le β.val
      have hrootmul : Real.sqrt β.val * Real.sqrt μ = Real.sqrt (t : ℝ) := by
        simpa only [mul_comm] using (eq_div_iff hβroot.ne').mp hrootdiv
      calc
        _ = (Real.sqrt (t : ℝ))⁻¹ := by
          simpa only [div_eq_mul_inv] using (Real.sqrt_div_self (x := (t : ℝ)))
        _ = (Real.sqrt β.val * Real.sqrt μ)⁻¹ := congrArg Inv.inv hrootmul.symm
        _ = _ := mul_inv _ _
    rw [spectralInverse_eq_factorization s β N hN t ht]
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
    erw [abs_of_pos (inv_pos.mpr ht)]
    calc
      _ = (Real.sqrt β.val)⁻¹ *
          ((Real.sqrt μ)⁻¹ * |factorizationMatrix s N hN μ hμ 0 0 h|) := by
        erw [← mul_assoc, hscale, mul_assoc]
      _ ≤ (Real.sqrt β.val)⁻¹ *
          (A * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(1 + (1 - s.val) / 2))) :=
        mul_le_mul_of_nonneg_left (hb N hN μ hμ h) (inv_nonneg.mpr hβroot.le)
      _ = _ := by ring

end Riesz2.ReferenceOperatorKernel
