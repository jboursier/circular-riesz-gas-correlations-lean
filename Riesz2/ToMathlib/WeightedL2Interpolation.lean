/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic

/-!
# Interpolation of weighted squared norms

For a measure `ν` on `α`, positive real weights `c i` on a finite index type `ι`, and a function
`f : α → ι → ℝ` whose coordinates are measurable, `weightedSqNorm ν c ρ f` is the extended
integral `∫⁻ a, ∑ i, c i ^ (2ρ) |f a i|² ∂ν`. It is a value in `[0, ∞]`, so no junk value of
the integral occurs.

For `0 ≤ u ≤ v` with `v > 0` and `θ = u / v`, Hölder's inequality gives the log-convexity
`weightedSqNorm ν c u f ≤ weightedSqNorm ν c 0 f ^ (1 - θ) * weightedSqNorm ν c v f ^ θ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz2

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- The weighted squared norm `∫⁻ a, ∑ i, c i ^ (2ρ) |f a i|² ∂ν` of a vector-valued function,
in `[0, ∞]`. -/
def weightedSqNorm (ν : Measure α) (c : ι → ℝ) (ρ : ℝ) (f : α → ι → ℝ) : ℝ≥0∞ :=
  ∫⁻ a, ∑ i, ENNReal.ofReal (c i ^ (2 * ρ)) * ‖f a i‖ₑ ^ 2 ∂ν

/-- For `p : ℝ≥0∞`, `0 ≤ a`, and `0 ≤ θ ≤ 1`, the factor `p^(1 - θ) * (a p)^θ` equals
`a^θ p`. -/
theorem rpow_mul_mul_rpow_eq (p : ℝ≥0∞) {a θ : ℝ} (ha : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    p ^ (1 - θ) * (ENNReal.ofReal a * p) ^ θ = ENNReal.ofReal (a ^ θ) * p := by
  have h1 : 0 ≤ 1 - θ := by linarith
  have hsplit : p ^ (1 - θ) * p ^ θ = p := by
    rw [← ENNReal.rpow_add_of_nonneg (1 - θ) θ h1 hθ0]
    simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, ENNReal.ofReal_rpow_of_nonneg ha hθ0]
  calc p ^ (1 - θ) * (ENNReal.ofReal (a ^ θ) * p ^ θ)
      = (p ^ (1 - θ) * p ^ θ) * ENNReal.ofReal (a ^ θ) := by ring
    _ = ENNReal.ofReal (a ^ θ) * p := by rw [hsplit, mul_comm]

/-- Hölder's inequality for finite sums in `[0, ∞]`, with exponents `1 - θ` and `θ`. -/
theorem sum_rpow_mul_rpow_le (P Q : ι → ℝ≥0∞) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∑ i, P i ^ (1 - θ) * Q i ^ θ ≤ (∑ i, P i) ^ (1 - θ) * (∑ i, Q i) ^ θ := by
  have hpq : (1 - θ)⁻¹.HolderConjugate θ⁻¹ := Real.HolderConjugate.one_sub_inv_inv hθ0 hθ1
  have h := ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun i => P i ^ (1 - θ))
    (fun i => Q i ^ θ) hpq
  have hp : ∀ x : ℝ≥0∞, (x ^ (1 - θ)) ^ (1 - θ)⁻¹ = x := by
    intro x
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by linarith), ENNReal.rpow_one]
  have hq : ∀ x : ℝ≥0∞, (x ^ θ) ^ θ⁻¹ = x := by
    intro x
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hθ0.ne', ENNReal.rpow_one]
  simpa [hp, hq, one_div, inv_inv] using h

/-- Log-convexity of the weighted squared norm in the exponent. For `0 ≤ u ≤ v` with `v > 0`,
`weightedSqNorm ν c u f` is at most `weightedSqNorm ν c 0 f ^ (1 - θ) * weightedSqNorm ν c v f ^ θ`,
where `θ = u / v`. -/
theorem weightedSqNorm_le_mul_rpow (ν : Measure α) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {f : α → ι → ℝ} (hf : ∀ i, Measurable fun a => f a i) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : 0 < v) :
    weightedSqNorm ν c u f ≤
      weightedSqNorm ν c 0 f ^ (1 - u / v) * weightedSqNorm ν c v f ^ (u / v) := by
  have hv0 : v ≠ 0 := hv.ne'
  have hθ0 : 0 ≤ u / v := div_nonneg hu hv.le
  have hθ1 : u / v ≤ 1 := (div_le_one hv).2 huv
  have hzero : weightedSqNorm ν c 0 f = ∫⁻ a, ∑ i, ‖f a i‖ₑ ^ 2 ∂ν := by
    simp [weightedSqNorm]
  rcases hθ0.eq_or_lt with hθ_zero | hθ_pos
  · have hu0 : u = 0 := by
      rcases div_eq_zero_iff.1 hθ_zero.symm with h | h
      · exact h
      · exact absurd h hv0
    subst hu0
    simp
  rcases hθ1.eq_or_lt with hθ_one | hθ_lt
  · have huv_eq : u = v := (div_eq_one_iff_eq hv0).1 hθ_one
    subst huv_eq
    rw [div_self hv0]
    simp
  have hpt : ∀ a, ∑ i, ENNReal.ofReal (c i ^ (2 * u)) * ‖f a i‖ₑ ^ 2 ≤
      (∑ i, ‖f a i‖ₑ ^ 2) ^ (1 - u / v) *
        (∑ i, ENNReal.ofReal (c i ^ (2 * v)) * ‖f a i‖ₑ ^ 2) ^ (u / v) := by
    intro a
    have hterm : ∀ i, ENNReal.ofReal (c i ^ (2 * u)) * ‖f a i‖ₑ ^ 2 =
        (‖f a i‖ₑ ^ 2) ^ (1 - u / v) *
          (ENNReal.ofReal (c i ^ (2 * v)) * ‖f a i‖ₑ ^ 2) ^ (u / v) := by
      intro i
      have hexp : (c i ^ (2 * v)) ^ (u / v) = c i ^ (2 * u) := by
        rw [← Real.rpow_mul (hc i).le]
        congr 1
        field_simp
      rw [rpow_mul_mul_rpow_eq _ (Real.rpow_nonneg (hc i).le _) hθ0 hθ1, hexp]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    exact sum_rpow_mul_rpow_le _ _ hθ_pos hθ_lt
  have hA : Measurable fun a => ∑ i, ‖f a i‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun i _ => (measurable_enorm.comp (hf i)).pow_const 2
  have hB : Measurable fun a => ∑ i, ENNReal.ofReal (c i ^ (2 * v)) * ‖f a i‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_enorm.comp (hf i)).pow_const 2).const_mul _
  have hpq : ((1 - u / v)⁻¹).HolderConjugate (u / v)⁻¹ :=
    Real.HolderConjugate.one_sub_inv_inv hθ_pos hθ_lt
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (hA.pow_const (1 - u / v)).aemeasurable
    (hB.pow_const (u / v)).aemeasurable
  have hpow : ∀ x : ℝ≥0∞, (x ^ (1 - u / v)) ^ (1 - u / v)⁻¹ = x := by
    intro x
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by linarith), ENNReal.rpow_one]
  have hpow' : ∀ x : ℝ≥0∞, (x ^ (u / v)) ^ (u / v)⁻¹ = x := by
    intro x
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hθ_pos.ne', ENNReal.rpow_one]
  simp only [hpow, hpow', one_div, inv_inv] at hH
  calc weightedSqNorm ν c u f
      = ∫⁻ a, ∑ i, ENNReal.ofReal (c i ^ (2 * u)) * ‖f a i‖ₑ ^ 2 ∂ν := rfl
    _ ≤ ∫⁻ a, (∑ i, ‖f a i‖ₑ ^ 2) ^ (1 - u / v) *
          (∑ i, ENNReal.ofReal (c i ^ (2 * v)) * ‖f a i‖ₑ ^ 2) ^ (u / v) ∂ν :=
        lintegral_mono fun a => hpt a
    _ ≤ (∫⁻ a, ∑ i, ‖f a i‖ₑ ^ 2 ∂ν) ^ (1 - u / v) *
          (∫⁻ a, ∑ i, ENNReal.ofReal (c i ^ (2 * v)) * ‖f a i‖ₑ ^ 2 ∂ν) ^ (u / v) := hH
    _ = weightedSqNorm ν c 0 f ^ (1 - u / v) * weightedSqNorm ν c v f ^ (u / v) := by
        rw [hzero]
        rfl

/-- The weighted norm `‖W_ρ f‖₂ = (∫⁻ ∑ᵢ cᵢ^{2ρ}|fᵢ|² dν)^{1/2}` in `[0, ∞]`. -/
def weightedNorm (ν : Measure α) (c : ι → ℝ) (ρ : ℝ) (f : α → ι → ℝ) : ℝ≥0∞ :=
  weightedSqNorm ν c ρ f ^ (2⁻¹ : ℝ)

/-- The interpolation inequality for the weighted norms:
`‖W_u f‖₂ ≤ ‖f‖₂^{1 - u/v} ‖W_v f‖₂^{u/v}` for `0 ≤ u ≤ v` with `v > 0`. -/
theorem weightedNorm_le_mul_rpow (ν : Measure α) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {f : α → ι → ℝ} (hf : ∀ i, Measurable fun a => f a i) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : 0 < v) :
    weightedNorm ν c u f ≤
      weightedNorm ν c 0 f ^ (1 - u / v) * weightedNorm ν c v f ^ (u / v) := by
  have hsq := weightedSqNorm_le_mul_rpow ν hc hf hu huv hv
  have hθ0 : 0 ≤ u / v := div_nonneg hu hv.le
  have hθ1 : 0 ≤ 1 - u / v := by
    have : u / v ≤ 1 := (div_le_one hv).2 huv
    linarith
  unfold weightedNorm
  calc weightedSqNorm ν c u f ^ (2⁻¹ : ℝ)
      ≤ (weightedSqNorm ν c 0 f ^ (1 - u / v) * weightedSqNorm ν c v f ^ (u / v)) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = (weightedSqNorm ν c 0 f ^ (1 - u / v)) ^ (2⁻¹ : ℝ) *
          (weightedSqNorm ν c v f ^ (u / v)) ^ (2⁻¹ : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = (weightedSqNorm ν c 0 f ^ (2⁻¹ : ℝ)) ^ (1 - u / v) *
          (weightedSqNorm ν c v f ^ (2⁻¹ : ℝ)) ^ (u / v) := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          mul_comm (1 - u / v), mul_comm (u / v)]

end Riesz2

end
end
