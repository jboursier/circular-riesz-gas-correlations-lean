/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DiscreteInterpolationPart2
public import Riesz2.ToMathlib.CyclicFourierL2

/-!
# The angular fractional primitive

The auxiliary operator in the proof of Lemma 5.9 uses angular distance
to `2πℤ`. This module gives its multiplier and energy integrability.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Riesz2.DiscreteInterpolation

/-- The multiplier of the primitive of order `a` in Lemma 5.9 in
the paper. The constant mode is removed for every real order. -/
def angularPrimitiveSymbol (N : ℕ+) (a : ℝ) (k : Fin (N : ℕ)) : ℝ :=
  if k = 0 then 0 else FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (-a)

/-- The paper's `Λ⁻ᵃ` in Lemma 5.9 of the paper, with the counting
normalization of the finite inverse transform. -/
def angularPrimitive (N : ℕ+) (a : ℝ) (u : Fin (N : ℕ) → ℂ) : Fin (N : ℕ) → ℂ :=
  cycleFourierInv N (fun k => (angularPrimitiveSymbol N a k : ℂ) * cycleFourier N u k)

/-- Exact multiplier identity for `Λ⁻ᵃ` in Lemma 5.9 of the paper. -/
theorem angularPrimitive_fourier (N : ℕ+) (a : ℝ) (u : Fin (N : ℕ) → ℂ)
    (k : Fin (N : ℕ)) :
    cycleFourier N (angularPrimitive N a u) k =
      (angularPrimitiveSymbol N a k : ℂ) * cycleFourier N u k :=
  cycleFourier_cycleFourierInv _ k

/-- The angular primitive has zero mass, as required in Lemma 5.9
of the paper, even when its input has nonzero mass. -/
theorem sum_angularPrimitive (N : ℕ+) (a : ℝ) (u : Fin (N : ℕ) → ℂ) :
    ∑ i, angularPrimitive N a u i = 0 := by
  have h := angularPrimitive_fourier N a u 0
  simpa [cycleFourier, cycleAngle, angularPrimitiveSymbol] using h

/-- The two radii in Lemma 5.9 of the paper are uniformly comparable
at every nonzero finite frequency. -/
theorem angularRadius_cycle_comparison (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    0 < frequencyRadius (cycleAngle N k) ∧
    frequencyRadius (cycleAngle N k) ≤ FourierMultiplierKernels.angularRadius (cycleAngle N k) ∧
    FourierMultiplierKernels.angularRadius (cycleAngle N k) ≤
      (Real.pi / 2) * frequencyRadius (cycleAngle N k) := by
  have hθ := Ioo_subset_Icc_self (cycleAngle_mem_Ioo N k hk)
  rw [FourierMultiplierKernels.angularRadius_eq_min hθ]
  exact ⟨lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 / (N : ℝ))
    (cycle_frequencyRadius_lower N k hk), radius_le_endpointDistance hθ,
    endpointDistance_le_radius hθ⟩

/-- Parseval compatibility with the sine multiplier for
Lemma 5.9 of the paper. Only the angular estimate supplies the bound. -/
theorem sine_energy_le_angularPrimitive (N : ℕ+) {a : ℝ} (ha : 0 ≤ a)
    (u : Fin (N : ℕ) → ℂ) :
    (∑ i, ‖cycleFourierInv N (fun k =>
        ((if k = 0 then 0 else frequencyRadius (cycleAngle N k) ^ (-a) : ℝ) : ℂ) *
          cycleFourier N u k) i‖ ^ 2) ≤
      ((Real.pi / 2) ^ a) ^ 2 * ∑ i, ‖angularPrimitive N a u i‖ ^ 2 := by
  have hb (k : Fin (N : ℕ)) :
      0 ≤ (if k = 0 then 0 else frequencyRadius (cycleAngle N k) ^ (-a) : ℝ) ∧
      (if k = 0 then 0 else frequencyRadius (cycleAngle N k) ^ (-a) : ℝ) ≤
        (Real.pi / 2) ^ a * angularPrimitiveSymbol N a k := by
    by_cases hk : k = 0
    · simp [angularPrimitiveSymbol, hk]
    obtain ⟨hr, hrρ, hρr⟩ := angularRadius_cycle_comparison N k hk
    have hρ := hr.trans_le hrρ
    simp only [angularPrimitiveSymbol, ite_eq_right hk]
    refine ⟨Real.rpow_nonneg hr.le _, ?_⟩
    have h := Real.rpow_le_rpow_of_nonpos hρ hρr (neg_nonpos.mpr ha)
    rw [Real.mul_rpow (by positivity) hr.le,
      Real.rpow_neg (by positivity : 0 ≤ Real.pi / 2)] at h
    have hp : 0 < (Real.pi / 2) ^ a := Real.rpow_pos_of_pos (by positivity) _
    have hh := mul_le_mul_of_nonneg_left h hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] using hh
  unfold angularPrimitive
  rw [sum_norm_sq_cycleFourier, sum_norm_sq_cycleFourier (cycleFourierInv N _)]
  simp only [cycleFourier_cycleFourierInv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [mul_left_comm (((Real.pi / 2) ^ a) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have h := pow_le_pow_left₀ (hb k).1 (hb k).2 2
  rw [mul_pow] at h
  nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖cycleFourier N u k‖)]

/-- Integrability of the paper's primitive energy in Lemma 5.9
of the paper. -/
theorem angularPrimitive_energy_integrable {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (N : ℕ+) (a : ℝ) (u : Fin (N : ℕ) → Lp ℝ 2 ν) :
    Integrable (fun x => ∑ i, ‖angularPrimitive N a (fun j => (u j x : ℂ)) i‖ ^ 2) ν :=
  (CyclicFourierL2.multiplier_parseval N (angularPrimitiveSymbol N a) u).1


end Riesz2.DiscreteInterpolation
