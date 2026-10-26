/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.External.RigidityUniformMean
public import Riesz1.Rigidity.RigidityBlocksLinear
public import Riesz1.Rigidity.RigidityBlocksComparison
public import Riesz1.Rigidity.RigidityBlocksCyclic
public import Riesz1.Rigidity.RigidityBlocksRates
public import Riesz1.Externals.BakryEmeryProof

/-!
# Uniform block-difference tails above a temperature floor

Uniform estimates for the companion rigidity theorem. The local mean threshold
from `RigidityUniformMean` is chosen before every model parameter.
The final rate uses the fixed exponent, deviation exponent and positive
temperature floor. The laws, block observables and concentration estimates
are the Riesz 1 objects. The proof supplies both inequality inputs.
-/

public section

noncomputable section

open MeasureTheory Riesz1

namespace Riesz2.ExternalRigidity

/-- Local-tail infrastructure for the companion rigidity theorem.
The mean threshold depends only on `γ`, before all temperatures, exponents,
cutoffs and block data. The concentration coefficient retains its explicit β. -/
theorem rigidity_blocks_local_tail_uniform {γ : ℝ} (hγ : 0 < γ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (P : Riesz1.Parameters) (N : ℕ+),
      2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (i : ℤ) (k : ℕ), 1 ≤ k → 3 * k < (N : ℕ) →
      ∀ v : ℝ, 0 < v → 2 * M ≤ v →
        (Riesz1.gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
          2 * Real.exp (-(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
              (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2) /
            (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ ((parametersExponent P).val + 2))) +
          3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) := by
  obtain ⟨M, hM, means⟩ := centered_block_diff_mean_uniform hγ
  refine ⟨M, hM, ?_⟩
  intro P N hN θ hθ i k hk hlocal v hv hlarge
  let R := ((3 * k : ℕ) : ℝ) ^ (1 + γ)
  let Q := constrainedLaw P N θ (i - k) (3 * k) R
  let m := ∫ X, centeredBlockDiff X i k ∂Q
  have hmean : |m| ≤ M := (means P N hN θ hθ i k hk hlocal).2
  have hR : 1 ≤ R := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ 3 * k by omega)) (by linarith)
  let := isProbabilityMeasure_constrainedLaw P N hθ
    (lt_of_lt_of_le zero_lt_one hR) (i - k) (3 * k)
  have htail := rigidityBlocks_local_centered_tail Externals.bakry_emery_proof
    Externals.prekopa_leindler_proof P N i hlocal hθ hR (half_pos hv)
  change Q.real {X | v / 2 ≤ |centeredBlockDiff X i k - m|} ≤ _ at htail
  have hinclusion : {X : Configuration N | v ≤ |centeredBlockDiff X i k|} ⊆
      {X | v / 2 ≤ |centeredBlockDiff X i k - m|} := by
    intro X hX
    change v ≤ |centeredBlockDiff X i k| at hX
    change v / 2 ≤ |centeredBlockDiff X i k - m|
    have := abs_sub_abs_le_abs_sub (centeredBlockDiff X i k) m
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hden : 0 < R ^ ((parametersExponent P).val + 2) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hR) _
  have hsquare : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [rigidityBlocks_gradient_bound_sq] at htail
  have halgebra : -(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
      (N : ℝ) ^ 2 * (3 * (k : ℝ) + 1) * (v / 2) ^ 2) /
      (2 * R ^ ((parametersExponent P).val + 2) *
        (4 * (N : ℝ) ^ 2 / (2 * k + 1))) =
      -(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
        (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2) /
        (32 * R ^ ((parametersExponent P).val + 2)) := by
    field_simp
    ring
  rw [halgebra] at htail
  have herror : 3 * Real.exp (-blockMomentExponent * ((3 * k : ℕ) : ℝ) ^ γ) ≤
      3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg k)
      (show (k : ℝ) ≤ ((3 * k : ℕ) : ℝ) by push_cast; linarith) hγ.le
    nlinarith [blockMomentExponent_pos]
  exact (rigidityBlocks_tail_transfer Externals.prekopa_leindler_proof P N hN hθ
    (i - k) i (by omega) hlocal γ k v).trans
      (add_le_add ((measureReal_mono hinclusion).trans htail) herror)

/-- Uniform block-difference estimate for the companion rigidity theorem.
For every positive deviation exponent `b`, the positive constants precede
every model of exponent `s` with temperature at least `βlo`, and every
`N ≥ 2`, integer label and `1 ≤ k ≤ N/2`, including even half-cycles. -/
theorem rigidity_blocks_uniform (s : Riesz1.RieszExponent) {b βlo : ℝ}
    (hb : 0 < b) (hβlo : 0 < βlo) :
    ∃ cB CB : ℝ, 0 < cB ∧ 0 < CB ∧ ∀ (P : Riesz1.Parameters),
      parametersExponent P = s → βlo ≤ P.val.1 →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i : ℤ) (k : ℕ),
      1 ≤ k → k ≤ (N : ℕ) / 2 →
        (Riesz1.gibbsMeasure P N).real
          {X | (k : ℝ) ^ (s.val / 2 + b) / 3 ≤ |centeredBlockDiff X i k|} ≤
        CB * Real.exp (-cB * (k : ℝ) ^ (b / (2 * (s.val + 2)))) := by
  let γ := b / (2 * (s.val + 2))
  have hp := Riesz1.Internal.rigidityBlocks_power_parameters s.property.1 hb
  obtain ⟨M, hM, local_tail⟩ := rigidity_blocks_local_tail_uniform hp.1
  let B0 := βlo * rigidityCurvatureConstant s.val
  have hB0 : 0 < B0 := mul_pos hβlo (rigidityCurvatureConstant_pos s)
  let d1 := B0 / (288 * (3 : ℝ) ^ ((1 + γ) * (s.val + 2)))
  let d2 := B0 / (72 * (3 : ℝ) ^ (s.val + 1))
  have hd1 : 0 < d1 := by dsimp [d1]; positivity
  have hd2 : 0 < d2 := by dsimp [d2]; positivity
  let c := min blockMomentExponent (min d1 d2)
  have hc : 0 < c := lt_min blockMomentExponent_pos (lt_min hd1 hd2)
  let C := 5 + Real.exp (6 * c * M)
  refine ⟨c, C, hc, by dsimp [C]; positivity, ?_⟩
  intro P hs hβ N hN i k hk hkN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkhalf : 2 * k ≤ (N : ℕ) := by omega
  let B := P.val.1 * rigidityCurvatureConstant s.val
  have hB : 0 < B := mul_pos P.property.1 (rigidityCurvatureConstant_pos s)
  have hBB : B0 ≤ B := mul_le_mul_of_nonneg_right hβ
    (rigidityCurvatureConstant_pos s).le
  have hc1 : c ≤ B / (288 * (3 : ℝ) ^ ((1 + γ) * (s.val + 2))) :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans
      (div_le_div_of_nonneg_right hBB (by positivity))
  have hc2 : c ≤ B / (72 * (3 : ℝ) ^ (s.val + 1)) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans
      (div_le_div_of_nonneg_right hBB (by positivity))
  let v := (k : ℝ) ^ (s.val / 2 + b) / 3
  have hv : 0 < v := by dsimp [v]; positivity
  have hkg : 0 ≤ (k : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC5 : 5 ≤ C := by dsimp [C]; linarith [Real.exp_pos (6 * c * M)]
  change (Riesz1.gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
    C * Real.exp (-c * (k : ℝ) ^ γ)
  by_cases hlocal : 3 * k < (N : ℕ)
  · by_cases hlarge : 2 * M ≤ v
    · have ht := local_tail P N hN forcingCutoff isForcingCutoff_forcingCutoff
        i k hk hlocal v hv hlarge
      rw [hs] at ht
      have hrate := Riesz1.Internal.rigidityBlocks_local_exponent s.property.1 hb hB hk1
      have hmain : c * (k : ℝ) ^ γ ≤ B * (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2 /
          (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ (s.val + 2)) := by
        apply (mul_le_mul_of_nonneg_right hc1 hkg).trans
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrate
      have he := Real.exp_le_exp.mpr (neg_le_neg hmain)
      have herr := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
        (show c ≤ blockMomentExponent from min_le_left _ _) hkg))
      have hcombined : 2 * Real.exp (-(B * (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2) /
          (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ (s.val + 2))) +
          3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) ≤
          5 * Real.exp (-c * (k : ℝ) ^ γ) := by
        simp only [neg_div, neg_mul] at he herr ⊢
        linarith
      exact ht.trans (hcombined.trans
        (mul_le_mul_of_nonneg_right hC5 (Real.exp_pos _).le))
    · have hpow : (k : ℝ) ^ γ ≤ (k : ℝ) ^ (s.val / 2 + b) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by dsimp [γ]; linarith [hp.2.1, s.property.1])
      have hscale : c * (k : ℝ) ^ γ ≤ 6 * c * M := by
        have hsmall : (k : ℝ) ^ (s.val / 2 + b) < 6 * M := by
          dsimp [v] at hlarge
          linarith
        nlinarith
      have hone : 1 ≤ Real.exp (6 * c * M) * Real.exp (-c * (k : ℝ) ^ γ) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
      let := isProbabilityMeasure_gibbsMeasure P N
      exact (measureReal_le_one (μ := Riesz1.gibbsMeasure P N)).trans
        (hone.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
          (Real.exp_pos _).le))
  · have ht := rigidityBlocks_full_tail Externals.bakry_emery_proof
      Externals.prekopa_leindler_proof P N hN i hk hkhalf hv
    rw [hs] at ht
    have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hNk : (N : ℝ) ≤ 3 * (k : ℝ) := by
      exact_mod_cast (show (N : ℕ) ≤ 3 * k by omega)
    have hspan : (k : ℝ) ≤ cyclicRepSpan N k + 1 := by
      exact_mod_cast (rigidityBlocks_span_bounds hk hkhalf).1
    have hr := Riesz1.Internal.rigidityBlocks_full_exponent s.property.1 hb hB hk1 hNpos hNk hspan
    have he := Real.exp_le_exp.mpr (neg_le_neg
      ((mul_le_mul_of_nonneg_right hc2 hkg).trans hr))
    have hmain : 2 * Real.exp (-(B * (N : ℝ) * (cyclicRepSpan N k + 1) * v ^ 2) /
        (8 * (N : ℝ) ^ (s.val + 2))) ≤ 2 * Real.exp (-c * (k : ℝ) ^ γ) := by
      simp only [neg_div, neg_mul] at he ⊢
      exact mul_le_mul_of_nonneg_left he (by norm_num)
    exact ht.trans (hmain.trans (mul_le_mul_of_nonneg_right
      (by linarith : (2 : ℝ) ≤ C) (Real.exp_pos _).le))

end Riesz2.ExternalRigidity
