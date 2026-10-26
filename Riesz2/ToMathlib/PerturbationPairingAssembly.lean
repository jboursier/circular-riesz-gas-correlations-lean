/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Assembly of signed perturbation pairings

Combining integrable pieces and positive temperature factors does not
require a sign for the resulting multiplication coefficient.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PerturbationPairingAssembly

/-- The norm of an actual L² representative is its square-integral norm. -/
theorem toLp_norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have he : (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx, pow_two]
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- Integrability on the two complementary pieces, together with integrable
signed correction terms, justifies integration of their pointwise sum. -/
theorem integral_defect {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : Set α} (hG : MeasurableSet G) {b f q y d : α → ℝ} {β : ℝ}
    (hb : IntegrableOn b G μ) (hf : IntegrableOn f Gᶜ μ)
    (hq : Integrable q μ) (hy : Integrable y μ)
    (hd : ∀ x, d x = β * (if x ∈ G then b x else f x) + β * q x - β ^ 2 * y x) :
    Integrable d μ ∧ ∫ x, d x ∂μ =
      β * (∫ x in G, b x ∂μ) + β * (∫ x in Gᶜ, f x ∂μ) +
        β * (∫ x, q x ∂μ) - β ^ 2 * (∫ x, y x ∂μ) := by
  classical
  have hp : Integrable (G.piecewise b f) μ :=
    (hb.integrable_indicator hG).add (hf.integrable_indicator hG.compl) |>.congr
      (ae_of_all μ fun x => by by_cases hx : x ∈ G <;> simp [hx])
  have hd' : d = fun x => β * G.piecewise b f x + β * q x - β ^ 2 * y x := funext hd
  rw [hd']
  refine ⟨((hp.const_mul β).add (hq.const_mul β)).sub (hy.const_mul (β ^ 2)), ?_⟩
  have he := integral_sub ((hp.const_mul β).add (hq.const_mul β)) (hy.const_mul (β ^ 2))
  simp only [Pi.add_apply] at he
  rw [he, integral_add (hp.const_mul β) (hq.const_mul β), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_piecewise hG hb hf]
  ring

/-- Five signed contributions with their actual temperature factors.
The common constant controls both the polynomial and exponential parts. -/
theorem five_terms_internal {β H b f q y r P E Cb Cf Cq Cy Cr : ℝ}
    (hβ : 0 ≤ β) (hβH : β ≤ H) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (_hCq : 0 ≤ Cq) (_hCy : 0 ≤ Cy) (hCr : 0 ≤ Cr)
    (hb : |b| ≤ Cb * P) (hf : |f| ≤ Cf * E)
    (hq : |q| ≤ Cq * P + Cq * E) (hy : |y| ≤ Cy * P + Cy * E)
    (hr : |r| ≤ Cr * P) :
    |β * b + β * f + β * q - β ^ 2 * y + β ^ 2 * r| ≤
      (H * (Cb + Cf + Cq) + H ^ 2 * (Cy + Cr)) * P +
      (H * (Cb + Cf + Cq) + H ^ 2 * (Cy + Cr)) * E := by
  have hH : 0 ≤ H := hβ.trans hβH
  have hβ2 : β ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hβ hβH 2
  calc
    _ ≤ β * |b| + β * |f| + β * |q| + β ^ 2 * |y| + β ^ 2 * |r| := by
      calc
        _ ≤ |β*b+β*f+β*q-β^2*y| + |β^2*r| := abs_add_le _ _
        _ ≤ |β*b+β*f+β*q| + |β^2*y| + |β^2*r| := by gcongr; exact abs_sub _ _
        _ ≤ |β*b+β*f| + |β*q| + |β^2*y| + |β^2*r| := by gcongr; exact abs_add_le _ _
        _ ≤ (|β*b| + |β*f|) + |β*q| + |β^2*y| + |β^2*r| := by gcongr; exact abs_add_le _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg hβ, abs_of_nonneg (sq_nonneg β)]
    _ ≤ H * (Cb * P) + H * (Cf * E) + H * (Cq * P + Cq * E) +
        H ^ 2 * (Cy * P + Cy * E) + H ^ 2 * (Cr * P) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hH hCf) hP,
      mul_nonneg (mul_nonneg hH hCb) hE, mul_nonneg (mul_nonneg (sq_nonneg H) hCr) hE]

/-- Piecewise multiplication, compensation, and covariance assembly.
All premises are internal bounds on separately justified integrals. -/
theorem multiplication_internal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : Set α} (hG : MeasurableSet G) {b f q y d : α → ℝ} {β H P E Cb Cf Cq Cy : ℝ}
    (hb : IntegrableOn b G μ) (hf : IntegrableOn f Gᶜ μ)
    (hq : Integrable q μ) (hy : Integrable y μ)
    (hd : ∀ x, d x = β * (if x ∈ G then b x else f x) + β * q x - β ^ 2 * y x)
    (hβ : 0 ≤ β) (hβH : β ≤ H) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCq : 0 ≤ Cq) (hCy : 0 ≤ Cy)
    (hbb : |∫ x in G, b x ∂μ| ≤ Cb * P)
    (hfb : |∫ x in Gᶜ, f x ∂μ| ≤ Cf * E)
    (hqb : |∫ x, q x ∂μ| ≤ Cq * P + Cq * E)
    (hyb : |∫ x, y x ∂μ| ≤ Cy * P + Cy * E) :
    Integrable d μ ∧ |∫ x, d x ∂μ| ≤
      (H * (Cb + Cf + Cq) + H ^ 2 * Cy) * P +
      (H * (Cb + Cf + Cq) + H ^ 2 * Cy) * E := by
  obtain ⟨hi, he⟩ := integral_defect hG hb hf hq hy hd
  refine ⟨hi, ?_⟩
  rw [he]
  have hh := five_terms_internal (r := 0) (Cr := 0) hβ hβH hP hE
    hCb hCf hCq hCy le_rfl hbb hfb hqb hyb (by simp)
  simpa only [mul_zero, add_zero] using hh

/-- Enlarge a prefactor and decrease a stretched-exponential rate while
retaining the exponent exactly. -/
theorem enlarge_internal {u P M C₀ C c₀ c t : ℝ} (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C) (hc : c ≤ c₀) (ht : 0 ≤ t)
    (hu : |u| ≤ C₀ * P + C₀ * Real.exp (-c₀ * t) * M) :
    |u| ≤ C * P + C * Real.exp (-c * t) * M := by
  apply hu.trans
  apply add_le_add (mul_le_mul_of_nonneg_right hC hP)
  apply mul_le_mul_of_nonneg_right _ hM
  apply mul_le_mul hC _ (Real.exp_pos _).le (hC₀.trans hC)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hc) ht

end Riesz2.PerturbationPairingAssembly
