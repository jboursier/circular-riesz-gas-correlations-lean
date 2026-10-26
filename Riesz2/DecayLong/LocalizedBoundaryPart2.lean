/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedBoundary
public import Riesz2.DecayLong.LocalizedMatrix
public import Riesz2.DecayLong.GlobalDecayPart3

/-!
# Decay of the original solution on the local window

The first analytic step of the proof of Proposition 5.15: separation
of the local window from the original source converts the global weighted
estimate into a norm bound on the whole window, without a cardinality loss.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Riesz2.LocalizedBoundary

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See the proof of Proposition 5.15 in the paper: separation from the source converts
the weighted norm into a norm of the entire local restriction. -/
theorem window_norm_internal (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 0 < Riesz1.cyclicIndexDistance m j i₀) (a : ℝ) (ha : 0 ≤ a)
    (v : Fin (m : ℕ) → Lp ℝ 2 ν) :
    (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ a *
      Real.sqrt (∑ i ∈ LocalizedMatrix.window m j i₀, ‖v i‖ ^ 2) ≤
    2 ^ a * Real.sqrt (∑ i, (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2) := by
  let R : ℝ := Riesz1.cyclicIndexDistance m j i₀
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast hR
  have hw (i : Fin (m : ℕ)) (hi : i ∈ LocalizedMatrix.window m j i₀) :
      R / 2 ≤ weightRadius m i i₀ := by
    have hs := LocalizedMatrix.window_separation m j i₀ i hi
    have hsR : 7 * R ≤ 8 * (Riesz1.cyclicIndexDistance m i i₀ : ℝ) := by
      dsimp only [R]
      exact_mod_cast hs
    change R / 2 ≤ 1 + (Riesz1.cyclicIndexDistance m i i₀ : ℝ)
    linarith
  have hp (i : Fin (m : ℕ)) (hi : i ∈ LocalizedMatrix.window m j i₀) :
      ((R / 2) ^ a * ‖v i‖) ^ 2 ≤ (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2 := by
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ R / 2) (hw i hi) ha
    have hn := mul_le_mul_of_nonneg_right hpow (norm_nonneg (v i))
    exact pow_le_pow_left₀ (by positivity) hn 2
  have hs := Finset.sum_le_sum hp
  have hsub : (∑ i ∈ LocalizedMatrix.window m j i₀,
      (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2) ≤
      ∑ i, (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  have he : (∑ i ∈ LocalizedMatrix.window m j i₀, ((R / 2) ^ a * ‖v i‖) ^ 2) =
      ((R / 2) ^ a) ^ 2 * ∑ i ∈ LocalizedMatrix.window m j i₀, ‖v i‖ ^ 2 := by
    simp only [mul_pow, Finset.mul_sum]
  rw [he] at hs
  have hroot := Real.sqrt_le_sqrt (hs.trans hsub)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at hroot
  have hscale : R ^ a = 2 ^ a * (R / 2) ^ a := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ R / 2)]
    congr 1
    ring
  change R ^ a * _ ≤ _
  rw [hscale, mul_assoc]
  exact mul_le_mul_of_nonneg_left hroot (by positivity)

/-- See the proof of Proposition 5.15 in the paper: norm decay of the entire original
solution restricted to the local window, the input to the remainder-source
estimate. Only the external periodic-zeta statement is conditional. -/
theorem original_solution_window_decay (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ j : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    0 < Riesz1.cyclicIndexDistance m j i₀ →
    (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val) *
      Real.sqrt (∑ i ∈ LocalizedMatrix.window m j i₀, ‖(u i).val‖ ^ 2) ≤
        C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
  obtain ⟨κ, hκ, hb⟩ := GlobalDecay.global_decay_bounds hzeta s κstar γstar
    hκstar hγstar M₀
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨2 ^ (3 / 2 - s.val) * C, by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ j u hu hR
  obtain ⟨lam, _, _, hweighted, _, _⟩ :=
    hb ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  have hv : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) ≤
      C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
    linarith only [hweighted, Real.sqrt_nonneg
      (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i))]
  exact (window_norm_internal m j i₀ hR (3 / 2 - s.val)
    (by linarith [s.property.2]) (fun i => (u i).val)).trans
      ((mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by ring))

end Riesz2.LocalizedBoundary
