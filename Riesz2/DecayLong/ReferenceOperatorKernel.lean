/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ReferenceValueMultiplier
public import Riesz2.Preliminaries.InverseRieszMatrix
public import Riesz2.Frozen.InverseTemperature

/-!
# Scalar spectral kernels of the reference inverse

Finite matrix estimates for the proof of Proposition 5.15. The parameter
`t` is a nonnegative scalar spectral value. The sampled circulant is
identified with the full interval matrix.
-/

@[expose] public section
noncomputable section

open Matrix
open scoped BigOperators Fin.NatCast NNReal

namespace Riesz2.ReferenceOperatorKernel

/-- The scalar spectral inverse `(β H₀ + t I)⁻¹`, including `t = 0`.
Its matrix is positive definite on the whole parameter carrier. -/
def spectralInverse (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) :
    Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  ((2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1)⁻¹

/-- The reference coefficient matrix in the proof of Proposition 5.15. -/
theorem reference_eq (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    rieszMatrix s N hN = referenceIntervalMatrix s N hN 1 := by
  ext i j
  exact (referenceIntervalMatrix_full s N hN i j).symm

/-- Strict positivity rules out the junk value of matrix inversion, including
at spectral value zero (the proof of Proposition 5.15). -/
theorem spectralMatrix_posDef (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) :
    ((2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1).PosDef :=
  ((rieszMatrix_posDef s N hN).smul (mul_pos two_pos β.property)).add_posSemidef
    (PosSemidef.one.smul t.property)

/-- Reuse of the factorization at every strictly positive spectral
value. -/
theorem spectralInverse_eq_factorization (s : Riesz1.RieszExponent)
    (β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    spectralInverse s β N hN t =
      (t : ℝ)⁻¹ • factorizationMatrix s N hN (t / β.val) (div_pos ht β.property) 0 := by
  let A := factorizationMatrix s N hN (t / β.val) (div_pos ht β.property) 0
  have he := (factorizationMatrix_shifted_mul s N hN
    (t / β.val) (div_pos ht β.property) 0).1
  simp only [zero_pow (by omega : 2 ≠ 0), zero_div, add_zero] at he
  have hscale : (2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1 =
      β.val • ((2 : ℝ) • rieszMatrix s N hN + (t / β.val) • 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [β.property.ne']
  apply Matrix.inv_eq_left_inv
  rw [hscale, Matrix.smul_mul, Matrix.mul_smul, he, smul_smul, smul_smul]
  have hscalar : (t : ℝ)⁻¹ * β.val * (t / β.val) = 1 := by
    field_simp [β.property.ne', ht.ne']
  rw [hscalar, one_smul]

/-- At spectral zero this is the actual inverse Riesz matrix, with its full
constant mode retained (the proof of Proposition 5.15). -/
theorem spectralInverse_zero (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    spectralInverse s β N hN 0 = (2 * β.val)⁻¹ • (rieszMatrix s N hN)⁻¹ := by
  have hdet := isUnit_iff_ne_zero.mpr (rieszMatrix_posDef s N hN).det_pos.ne'
  apply Matrix.inv_eq_left_inv
  simp only [NNReal.coe_zero, zero_smul, add_zero]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hdet, smul_smul,
    inv_mul_cancel₀ (mul_pos two_pos β.property).ne', one_smul]

/-- Uniform scalar entry decay for `σ = 0`, including the spectral endpoint
`t = 0`. This follows Lemma 2.4 in equation (5.68) in the
proof of Proposition 5.15. -/
theorem spectralInverse_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0)
      (h : Fin (N : ℕ)),
      |spectralInverse s β N hN t 0 h| ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(2 - s.val)) := by
  obtain ⟨C, hC, hb⟩ := ReferenceValueMultiplier.spectralInverse_decay_direct hz s
  refine ⟨β.val⁻¹ * C, mul_pos (inv_pos.mpr β.property) hC, ?_⟩
  intro N hN t h
  let Q := (2 : ℝ) • rieszMatrix s N hN + ((t : ℝ) / β.val) • 1
  have hQ : Q.PosDef :=
    ((rieszMatrix_posDef s N hN).smul two_pos).add_posSemidef
      (PosSemidef.one.smul (div_nonneg t.property β.property.le))
  have hscale : (2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1 = β.val • Q := by
    ext i j
    simp only [Q, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [β.property.ne']
  have hi : spectralInverse s β N hN t = β.val⁻¹ • Q⁻¹ := by
    apply Matrix.inv_eq_left_inv
    change (β.val⁻¹ • Q⁻¹) * ((2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1) = 1
    rw [hscale, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'),
      smul_smul, inv_mul_cancel₀ β.property.ne', one_smul]
  rw [hi, Matrix.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr β.property)]
  have hh := mul_le_mul_of_nonneg_left
    (hb N hN ((t : ℝ) / β.val) (div_nonneg t.property β.property.le) h)
    (inv_nonneg.mpr β.property.le)
  simpa only [Q, mul_assoc] using hh

/-- The exact constant frequency, at every nonnegative spectral value.
This is the mass identity needed by the proof of Proposition 5.15. -/
theorem spectralInverse_row_sum (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) (i : Fin (N : ℕ)) :
    (∑ j, spectralInverse s β N hN t i j) =
      (β.val * (2 * ∑ k, sampledRieszKernel s N hN k) + t)⁻¹ := by
  let D := (2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1
  let ell := β.val * (2 * ∑ k, sampledRieszKernel s N hN k) + t
  have hdet : IsUnit D.det := isUnit_iff_ne_zero.mpr (spectralMatrix_posDef s β N hN t).det_pos.ne'
  obtain ⟨c, _, hc, _, hb⟩ := sampledRieszKernel_zero_mode_bounds s
  have hmass : 0 < ∑ k, sampledRieszKernel s N hN k :=
    (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le (hb N hN).1
  have hell : 0 < ell := add_pos_of_pos_of_nonneg
    (mul_pos β.property (mul_pos two_pos hmass)) t.property
  have he : D *ᵥ (fun _ => 1) = ell • (fun _ => 1) := by
    change ((2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1) *ᵥ _ = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext j
    simp only [
      Matrix.mulVec, dotProduct, mul_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, rieszMatrix_row_sum]
    dsimp only [ell]
    ring
  have hh := congrArg (fun v => D⁻¹ *ᵥ v) he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec,
    Matrix.mulVec_smul] at hh
  have hi := congrFun hh i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_one] at hi
  change (∑ j, D⁻¹ i j) = ell⁻¹
  apply (mul_left_cancel₀ hell.ne')
  rw [mul_inv_cancel₀ hell.ne']
  exact hi.symm

/-- Cyclic translation invariance of the actual scalar inverse, including
spectral zero (the proof of Proposition 5.15, scalar infrastructure). -/
theorem spectralInverse_translate (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) (i j k : Fin (N : ℕ)) :
    spectralInverse s β N hN t (i + k) (j + k) = spectralInverse s β N hN t i j := by
  rcases eq_or_lt_of_le t.property with ht | ht
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp ht.symm
    subst t
    rw [spectralInverse_zero]
    simp only [Matrix.smul_apply, smul_eq_mul]
    congr 1
    apply Complex.ofReal_injective
    have he := sampledRieszMatrix_inverse_formula hz s N hN (i + k) (j + k)
    have he' := sampledRieszMatrix_inverse_formula hz s N hN i j
    change ((rieszMatrix s N hN)⁻¹ (i + k) (j + k) : ℂ) = _ at he
    rw [show j + k - (i + k) = j - i by abel] at he
    exact he.trans he'.symm
  · rw [spectralInverse_eq_factorization s β N hN t ht]
    simp only [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact factorizationMatrix_translate s N hN (t / β.val) (div_pos ht β.property) 0 i j k

/-- A single row defines the scalar cyclic convolution kernel. -/
theorem spectralInverse_kernel (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) (i h : Fin (N : ℕ)) :
    spectralInverse s β N hN t i (i + h) = spectralInverse s β N hN t 0 h := by
  simpa only [zero_add, add_comm h i] using
    spectralInverse_translate hz s β N hN t 0 h i

/-- Uniform mass bounds for both scalar multipliers `σ = 0` and `σ = 1/2`.
Constants precede the size and spectral parameter, as in the proof of Proposition 5.15. The operator-valued lifting is separate. -/
theorem spectralInverse_mass_bounds (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0)
      (i : Fin (N : ℕ)),
      |∑ j, spectralInverse s β N hN t i j| ≤ C * (N : ℝ) ^ (-(1 - s.val)) ∧
      Real.sqrt t * |∑ j, spectralInverse s β N hN t i j| ≤
        C * (N : ℝ) ^ (-(1 - s.val) / 2) := by
  obtain ⟨c, _, hc, _, hb⟩ := global_reference_mass_bounds s
  let B := β.val * c
  have hB : 0 < B := mul_pos β.property hc
  have hroot : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  refine ⟨B⁻¹ + (Real.sqrt B)⁻¹, by positivity, ?_⟩
  intro N hN t i
  let ell := β.val * (2 * ∑ k, sampledRieszKernel s N hN k)
  have hN0 : (0 : ℝ) < N := by positivity
  have hlo : B * (N : ℝ) ^ (1 - s.val) ≤ ell := by
    have hh := mul_le_mul_of_nonneg_left (hb N hN i).1 β.property.le
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum] at hh
    simpa only [B, ell, mul_assoc] using hh
  have hell : 0 < ell := (mul_pos hB (Real.rpow_pos_of_pos hN0 _)).trans_le hlo
  have hden : 0 < ell + t := add_pos_of_pos_of_nonneg hell t.property
  rw [spectralInverse_row_sum, abs_of_pos (inv_pos.mpr hden)]
  have hinv : (ell + t)⁻¹ ≤ B⁻¹ * (N : ℝ) ^ (-(1 - s.val)) := by
    calc
      _ ≤ (B * (N : ℝ) ^ (1 - s.val))⁻¹ :=
        inv_anti₀ (mul_pos hB (Real.rpow_pos_of_pos hN0 _))
          (hlo.trans (le_add_of_nonneg_right t.property))
      _ = _ := by rw [mul_inv, Real.rpow_neg hN0.le]
  have hhalf : Real.sqrt t * (ell + t)⁻¹ ≤ (Real.sqrt ell)⁻¹ := by
    have hr : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
    have hs := sq_nonneg (Real.sqrt ell - Real.sqrt t)
    have hsell : (Real.sqrt ell) ^ 2 = ell := Real.sq_sqrt hell.le
    have hst : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := Real.sq_sqrt t.property
    rw [← div_eq_mul_inv, inv_eq_one_div]
    apply (div_le_div_iff₀ hden hr).mpr
    nlinarith only [hs, hsell, hst,
      mul_nonneg (Real.sqrt_nonneg ell) (Real.sqrt_nonneg (t : ℝ))]
  have hrootinv : (Real.sqrt ell)⁻¹ ≤
      (Real.sqrt B)⁻¹ * (N : ℝ) ^ (-(1 - s.val) / 2) := by
    calc
      _ ≤ (Real.sqrt (B * (N : ℝ) ^ (1 - s.val)))⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.mpr (mul_pos hB (Real.rpow_pos_of_pos hN0 _)))
          (Real.sqrt_le_sqrt hlo)
      _ = _ := by
        rw [Real.sqrt_mul hB.le, mul_inv]
        simp only [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hN0.le,
          ← Real.rpow_neg hN0.le]
        congr 2
        ring
  constructor
  · exact hinv.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (inv_nonneg.mpr hroot.le)) (Real.rpow_nonneg hN0.le _))
  · exact (hhalf.trans hrootinv).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (inv_nonneg.mpr hB.le)) (Real.rpow_nonneg hN0.le _))

end Riesz2.ReferenceOperatorKernel
