/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Finite counting-measure interpolation

The deterministic finite-sum Hölder step used in the proof of Lemma 5.9.
The statements use the usual power sums directly and introduce no new norm.
-/

public section

open scoped BigOperators

namespace Riesz2.FiniteNormInterpolation

/-- Interpolation between finite `ℓ¹` and `ℓ²`, with counting measure.
This is the finite-sum Hölder step in the proof of Lemma 5.9. -/
theorem l1_l2_interpolation {ι : Type*} (S : Finset ι) {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ S, f i ^ p) ^ (1 / p) ≤
      (∑ i ∈ S, f i) ^ ((2 - p) / p) *
        (∑ i ∈ S, f i ^ 2) ^ ((p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hq : 1 ≤ (p - 1)⁻¹ := (one_le_inv₀ hpm).2 (by linarith)
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg S hq f
    (fun i => f i ^ (p - 1)) hf (fun i => Real.rpow_nonneg (hf i) _)
  have hprod (i : ι) : f i * f i ^ (p - 1) = f i ^ p := by
    by_cases hi : f i = 0
    · simp only [hi, zero_mul, Real.zero_rpow hp0.ne']
    · have hi0 : 0 < f i := lt_of_le_of_ne (hf i) (Ne.symm hi)
      calc
        _ = f i ^ (1 + (p - 1)) := by rw [Real.rpow_add hi0, Real.rpow_one]
        _ = _ := by congr 1; ring
  have hpower (i : ι) : (f i ^ (p - 1)) ^ (p - 1)⁻¹ = f i := by
    rw [← Real.rpow_mul (hf i), mul_inv_cancel₀ hpm.ne', Real.rpow_one]
  simp only [hprod, hpower, inv_inv] at hh
  have hh' : (∑ i ∈ S, f i ^ p) ≤
      (∑ i ∈ S, f i) ^ (2 - p) * (∑ i ∈ S, f i ^ 2) ^ (p - 1) := by
    simpa only [show 1 - (p - 1) = 2 - p by ring, pow_two] using hh
  have hs : 0 ≤ ∑ i ∈ S, f i := Finset.sum_nonneg (fun i _ => hf i)
  have hs2 : 0 ≤ ∑ i ∈ S, f i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsP : 0 ≤ ∑ i ∈ S, f i ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hf i) _)
  have hr := Real.rpow_le_rpow hsP hh' (by positivity : 0 ≤ 1 / p)
  rw [Real.mul_rpow (Real.rpow_nonneg hs _) (Real.rpow_nonneg hs2 _),
    ← Real.rpow_mul hs, ← Real.rpow_mul hs2] at hr
  simpa only [div_eq_mul_inv, one_mul] using hr

/-- The exponent parametrization used in the proof of Lemma 5.9. -/
theorem l1_l2_interpolation_theta {ι : Type*} (S : Finset ι) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ S, f i ^ (1 - θ / 2)⁻¹) ^ (1 - θ / 2) ≤
      (∑ i ∈ S, f i) ^ (1 - θ) * (∑ i ∈ S, f i ^ 2) ^ (θ / 2) := by
  have hD : 0 < 1 - θ / 2 := by linarith
  have hD1 : 1 - θ / 2 < 1 := by linarith
  have hp : 1 < (1 - θ / 2)⁻¹ := (one_lt_inv₀ hD).2 hD1
  have hp2 : (1 - θ / 2)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hD (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  have h1 : (2 - (1 - θ / 2)⁻¹) / (1 - θ / 2)⁻¹ = 1 - θ := by
    rw [div_inv_eq_mul, sub_mul, inv_mul_cancel₀ hD.ne']
    ring
  have h2 : ((1 - θ / 2)⁻¹ - 1) / (1 - θ / 2)⁻¹ = θ / 2 := by
    rw [div_inv_eq_mul, sub_mul, inv_mul_cancel₀ hD.ne']
    ring
  simpa only [one_div, inv_inv, h1, h2] using l1_l2_interpolation S hp hp2 f hf

/-- Exact scale cancellation in the block interpolation of the proof of Lemma 5.9. No positivity assumption on either endpoint norm is needed. -/
theorem block_scale_cancellation {t A B θ : ℝ} (ht : 0 < t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (t ^ (-θ / 2) * A) ^ (1 - θ) * (t ^ ((1 - θ) / 2) * B) ^ θ =
      A ^ (1 - θ) * B ^ θ := by
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) hA,
    Real.mul_rpow (Real.rpow_nonneg ht.le _) hB,
    ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
  calc
    _ = (t ^ ((-θ / 2) * (1 - θ)) * t ^ (((1 - θ) / 2) * θ)) *
        (A ^ (1 - θ) * B ^ θ) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; ring_nf; simp

end Riesz2.FiniteNormInterpolation
