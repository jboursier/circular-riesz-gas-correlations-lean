/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.CountVariance
public import Riesz1.Frozen.FluctuationsGapsDiscrepancy
public import Riesz1.Frozen.NormalizedGap
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.PeriodicZeta
public import Riesz1.Kernel.PeriodicZeta
public import Riesz2.Bridges.GapRigidity
public import Riesz2.Frozen.ConvergesInLawAlong
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.LongParameters
public import Riesz2.Frozen.OfLong
public import Mathlib.Tactic

/-!
# Finite gap central limit theorem and variance profile from Riesz 1

This file applies two results of the companion paper.

* Corollary 1, second assertion, gives the gap central limit theorem through
  `Riesz1.fluctuations_gaps_discrepancy` and `Riesz1.normalizedGap`.
* Lemma 2.3, opening assertion, gives the variance-profile expansion through
  `Riesz1.periodicZeta_pos` and `Riesz1.periodicZeta_asymptotic`.

The paper labels particles `1, …, N`, and Riesz 1 labels them from `0`.
Thus `(x_1, x_{1+k})` is `(cyclicLift X 0, cyclicLift X k)`.
For `s < 1`, `Riesz2.gibbsMeasure (Riesz2.ofLong β s)` is the Riesz 1 law
by `Riesz2.gibbsMeasure_ofLong`.

The law at index `n` has particle number `Riesz1.particleNumber (n + 1)`,
which is `N = n + 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal

namespace Riesz2

/-- The limiting variance `Riesz1.countVariance` of the long-range parameters is nonnegative.
The value is `cot(π s / 2) / (2 β π s)`, which is positive for `0 < s < 1`. -/
theorem companionCountVariance_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    0 ≤ Riesz1.countVariance (longParameters β s) := by
  have hs : 0 < s.val := s.property.1
  have hβ : 0 < β.val := β.property
  have hangle : 0 ≤ Real.pi * s.val / 2 := by positivity
  have hhalf : Real.pi * s.val / 2 ≤ Real.pi / 2 := by
    nlinarith [s.property.2, Real.pi_pos]
  unfold Riesz1.countVariance longParameters
  change 0 ≤ Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
    (2 * β.val * Real.pi * s.val)
  exact div_nonneg
    (div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalf⟩)
      (Real.sin_nonneg_of_mem_Icc ⟨hangle, by linarith [Real.pi_pos]⟩))
    (by positivity)

/-- The gap central limit theorem from Corollary 1 of the companion paper. Let `β > 0` and
`0 < s < 1`. Let `k : ℕ+ → ℕ` satisfy `1 ≤ k N ≤ ⌊N/2⌋` for every `N ≥ 2`, and let `k_N → ∞`
along the particle numbers. Then, for every `N ≥ 2`, the denominator
`sqrt(N^s V_s(k_N/N))` is positive, where `V_s` is `Riesz1.periodicZeta`. Moreover the law of
`(N(x_{1+k_N} - x_1) - k_N) / sqrt(N^s V_s(k_N/N))` under the Gibbs law at `N` converges in law to
the centred Gaussian `N(0, σ²)`, where `σ²` is `Riesz1.countVariance`. The law at index `n` is
the law at `N = n + 2`. -/
theorem companionGapCLT (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (k : ℕ+ → ℕ) (hk : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2)
    (hkTop : Tendsto (fun n : ℕ => k (Riesz1.particleNumber n)) atTop atTop) :
    (∀ N : ℕ+, 2 ≤ (N : ℕ) →
      0 < Real.sqrt ((N : ℝ) ^ s.val *
        Riesz1.periodicZeta s (((k N : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))) ∧
    ConvergesInLawAlong atTop
      (fun n : ℕ => (gibbsMeasure (ofLong β s) (Riesz1.particleNumber (n + 1))).map
        (Riesz1.normalizedGap (longParameters β s) (Riesz1.particleNumber (n + 1))
          (k (Riesz1.particleNumber (n + 1)))
          (hk (Riesz1.particleNumber (n + 1)) (Nat.le_add_left 2 n))))
      (Riesz1.normalLaw ⟨Riesz1.countVariance (longParameters β s),
        companionCountVariance_nonneg β s⟩) := by
  obtain ⟨hpos, hconv⟩ :=
    (Riesz1.fluctuations_gaps_discrepancy β.val s.val β.property s.property.1
      s.property.2).2.2.2 k hk hkTop
  refine ⟨fun N hN => (hpos N hN).1, ?_⟩
  have hv : (⟨Riesz1.countVariance (longParameters β s), companionCountVariance_nonneg β s⟩ : ℝ≥0) =
      Real.toNNReal (Riesz1.countVariance (longParameters β s)) :=
    NNReal.eq (Real.coe_toNNReal _ (companionCountVariance_nonneg β s)).symm
  rw [hv]
  simp only [gibbsMeasure_ofLong]
  exact hconv

/-- The variance-profile expansion from Lemma 2.3 of the companion paper. Let
`0 < s < 1`. Then `V_s(t) = Riesz1.periodicZeta s t` is positive for `0 < t < 1`. Moreover there
exist `C > 0` and `t_s ∈ (0, 1/2]` such that `|V_s(t) - t^s| ≤ C t²` for every `0 < t ≤ t_s`. -/
theorem companionVarianceProfile (s : Riesz1.RieszExponent) :
    (∀ t : ℝ, 0 < t → t < 1 → 0 < Riesz1.periodicZeta s (t : UnitAddCircle)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ ts : ℝ, 0 < ts ∧ ts ≤ 1 / 2 ∧
      ∀ t : ℝ, 0 < t → t ≤ ts →
        |Riesz1.periodicZeta s (t : UnitAddCircle) - t ^ s.val| ≤ C * t ^ 2 := by
  obtain ⟨C, hC, t₀, ht₀, hbound⟩ := Riesz1.periodicZeta_asymptotic s
  refine ⟨fun t ht0 ht1 => Riesz1.periodicZeta_pos s ht0 ht1, C, hC, min t₀ (1 / 2),
    lt_min ht₀ (by norm_num), min_le_right _ _, fun t ht0 ht => hbound t ht0 ?_⟩
  exact ht.trans (min_le_left _ _)

end Riesz2

end
end
