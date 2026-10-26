/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityBlocksGeometry
public import Riesz1.Externals.PrekopaLeindlerProof

/-!
# Temperature-independent constrained block means

For constrained blocks of length at least two, the normalizer has a lower bound
depending only on the radius exponent. Together with the universal density error,
this gives a mean bound uniform in the model parameters and a common bound for
the local centered block difference. These estimates support the companion
rigidity theorem.

The objects and analytic estimates come from Riesz 1. Both conclusions include
integrability. The proof supplies the Prékopa–Leindler inequality.
-/

public section

noncomputable section

open MeasureTheory
open Riesz1

namespace Riesz2.ExternalRigidity

/-- Large-block mean interface for the companion rigidity theorem.
The bound depends only on `γ`, uniformly over every model parameter and cutoff.
The observed block can start at any integer label. Only its length is bounded
by the constrained block length. -/
theorem expectation_large_block_uniform {γ : ℝ} (hγ : 0 < γ) :
    ∃ Mγ : ℝ, 0 < Mγ ∧ ∀ (P : Riesz1.Parameters) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (i j : ℤ) (L k : ℕ), 2 ≤ L → 0 < k → k ≤ L →
        Integrable (fun X : Configuration N => blockLength X j k)
          (constrainedLaw P N θ i L ((L : ℝ) ^ (1 + γ))) ∧
        |(∫ X : Configuration N, blockLength X j k
          ∂constrainedLaw P N θ i L ((L : ℝ) ^ (1 + γ))) - (k : ℝ)| ≤ Mγ := by
  obtain ⟨A, hA, error_bound⟩ := expectation_error_cauchy_schwarz_internal
  obtain ⟨K, hK, scale_bound⟩ := exists_scale_exp_bound
    (div_pos blockMomentExponent_pos (show (0 : ℝ) < 2 by norm_num)) hγ
  let δ : ℝ := 1 - (2 : ℝ) ^ (-γ)
  have hδ : 0 < δ := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ))
  refine ⟨A * K / δ, div_pos (mul_pos hA hK) hδ, ?_⟩
  intro P N hN θ hθ i j L k hL hk hkL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hR := Real.rpow_pos_of_pos hLpos (1 + γ)
  refine ⟨(blockLength_constrained_integral P N hθ i L hR j k).1, ?_⟩
  have hz := constrainedNormalizer_ge_two P N hN hθ i hL hγ
  have hinverse : (constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)))⁻¹ ≤ δ⁻¹ :=
    inv_anti₀ hδ hz
  have hratio : (L : ℝ) ^ (1 + γ) / (L : ℝ) = (L : ℝ) ^ γ := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
    exact mul_div_cancel_left₀ _ hLpos.ne'
  have herr := error_bound Externals.prekopa_leindler_proof P N hN θ hθ
    i j L k (by omega) hk _ hR
  rw [hratio] at herr
  have hscale : (k : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2) ≤ K := by
    rw [show -blockMomentExponent * (L : ℝ) ^ γ / 2 =
      -(blockMomentExponent / 2) * (L : ℝ) ^ γ by ring]
    exact (mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ L by exact_mod_cast hkL)
      (Real.exp_pos _).le).trans (scale_bound (L : ℝ) hLpos)
  have hnum : A * (k : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2) ≤
      A * K := by nlinarith
  calc
    _ ≤ (constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)))⁻¹ * (A * K) :=
      herr.trans (mul_le_mul_of_nonneg_left hnum
        (inv_nonneg.mpr (hδ.le.trans hz)))
    _ ≤ δ⁻¹ * (A * K) := mul_le_mul_of_nonneg_right hinverse (mul_pos hA hK).le
    _ = A * K / δ := by ring

/-- Local centered-block mean interface for the companion rigidity theorem.
The universal witness is obtained from `expectation_large_block_uniform` without
enlargement, by the exact finite-average identity. The local block has length
`3k`, so the one-gap normalizer is never used. -/
theorem centered_block_diff_mean_uniform {γ : ℝ} (hγ : 0 < γ) :
    ∃ Mγ : ℝ, 0 < Mγ ∧ ∀ (P : Riesz1.Parameters) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (i : ℤ) (k : ℕ), 1 ≤ k → 3 * k < (N : ℕ) →
        Integrable (fun X : Configuration N => centeredBlockDiff X i k)
          (constrainedLaw P N θ (i - k) (3 * k) (((3 * k : ℕ) : ℝ) ^ (1 + γ))) ∧
        |∫ X : Configuration N, centeredBlockDiff X i k
          ∂constrainedLaw P N θ (i - k) (3 * k)
            (((3 * k : ℕ) : ℝ) ^ (1 + γ))| ≤ Mγ := by
  obtain ⟨M, hM, mean_bound⟩ := expectation_large_block_uniform hγ
  refine ⟨M, hM, ?_⟩
  intro P N hN θ hθ i k hk _hkN
  have hR : 0 < ((3 * k : ℕ) : ℝ) ^ (1 + γ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < 3 * k by omega)) _
  let := isProbabilityMeasure_constrainedLaw P N hθ hR (i - k) (3 * k)
  have blocks (j : ℤ) := mean_bound P N hN θ hθ (i - k) j (3 * k) k
    (by omega) (by omega) (by omega)
  refine ⟨integrable_centeredBlockDiff_constrained P N hθ (i - k) i (3 * k) hR hk, ?_⟩
  rw [Internal.integral_centeredBlockDiff_eq_average i hk (fun j _ => (blocks j).1)]
  have hcard : (0 : ℝ) < (cyclicRep N k i).card := by
    exact_mod_cast cyclicRep_card_pos hk i
  rw [abs_mul, abs_of_pos (inv_pos.mpr hcard)]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_pos.mpr hcard).le).trans
  have hsum := (cyclicRep N k i).sum_le_card_nsmul _ M (fun j _ => (blocks j).2)
  rw [nsmul_eq_mul] at hsum
  convert mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hcard).le using 1
  simp [hcard.ne']

end Riesz2.ExternalRigidity
