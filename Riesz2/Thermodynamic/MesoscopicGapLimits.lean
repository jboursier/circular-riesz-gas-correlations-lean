/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.GapFluctuations
public import Riesz2.Frozen.CyclicGapSum
public import Riesz1.Auxiliary.LoopMomentsLifts
public import Mathlib.Tactic

/-!
# Mesoscopic span normalization

Deterministic normalization bridges and finite span identities for the proof of
Corollary 1.1. The companion periodic profile is used literally.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz2

/-- A mesoscopic pair eventually lies in the proper half-cycle range.
This also proves eventual positivity of every power base used for normalization. -/
lemma mesoscopic_pairs_eventually_admissible (K : ℕ → ℕ) (N : ℕ → ℕ+)
    (hK : Tendsto K atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, 1 ≤ K j ∧ K j ≤ (N j : ℕ) / 2 := by
  filter_upwards [hK.eventually_ge_atTop 1,
    hKN.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with j hj hratio
  have hN : (0 : ℝ) < N j := by exact_mod_cast (N j).pos
  have hle : 2 * K j ≤ (N j : ℕ) := by
    have := (div_lt_iff₀ hN).mp hratio
    have : (2 : ℝ) * (K j : ℝ) ≤ (N j : ℝ) := by linarith
    exact_mod_cast this
  exact ⟨hj, by omega⟩

/-- The periodic profile divided by its leading power tends to one, along every positive
sequence tending to zero. This is the deterministic part of
the proof of Corollary 1.1. -/
theorem periodicVarianceProfile_ratio_limit (s : Riesz1.RieszExponent)
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun j => (t j) ^ (-s.val) * Riesz1.periodicZeta s (t j : UnitAddCircle))
      atTop (𝓝 1) := by
  obtain ⟨-, C, hC, ts, hts, -, hb⟩ := companionVarianceProfile s
  have hbound : ∀ᶠ j in atTop,
      |(t j) ^ (-s.val) * Riesz1.periodicZeta s (t j : UnitAddCircle) - 1| ≤
        C * (t j) ^ (2 - s.val) := by
    filter_upwards [ht0.eventually (eventually_le_nhds hts)] with j hj
    have h := mul_le_mul_of_nonneg_left (hb (t j) (ht j) hj)
      (Real.rpow_nonneg (ht j).le (-s.val))
    have hcancel : (t j) ^ (-s.val) * (t j) ^ s.val = 1 := by
      rw [← Real.rpow_add (ht j)]; simp
    have hp : (t j) ^ (-s.val) * (t j) ^ 2 = (t j) ^ (2 - s.val) := by
      rw [← Real.rpow_two, ← Real.rpow_add (ht j)]; congr 1; ring
    rw [← abs_of_nonneg (Real.rpow_nonneg (ht j).le (-s.val)), ← abs_mul, mul_sub, hcancel] at h
    calc _ ≤ (t j) ^ (-s.val) * (C * (t j) ^ 2) := by
            simpa only [abs_of_nonneg (Real.rpow_nonneg (ht j).le (-s.val))] using h
      _ = _ := by rw [mul_left_comm, hp]
  have hzero : Tendsto (fun j => C * (t j) ^ (2 - s.val)) atTop (𝓝 0) := by
    simpa using (ht0.rpow_const_nhds_zero (by linarith [s.property.2] : 0 < 2 - s.val)).const_mul C
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (hbound.mono fun _ h => by simpa only [Real.dist_eq] using h) hzero

/-- See the proof of Corollary 1.1 in the paper: cancellation of the two volume powers
in the companion normalization, with no assumption that the volumes form a monotone sequence. -/
theorem mesoscopic_gap_profile_ratio_limit (s : Riesz1.RieszExponent)
    (K N : ℕ → ℕ+) (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => (N j : ℝ) ^ s.val *
      Riesz1.periodicZeta s (((K j : ℝ) / (N j : ℝ) : ℝ) : UnitAddCircle) /
        (K j : ℝ) ^ s.val) atTop (𝓝 1) := by
  have hposK : ∀ j, (0 : ℝ) < K j := fun j => by exact_mod_cast (K j).pos
  have hposN : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast (N j).pos
  have h := periodicVarianceProfile_ratio_limit s (fun j => (K j : ℝ) / (N j : ℝ))
    (fun j => div_pos (hposK j) (hposN j)) hKN
  convert h using 1
  funext j
  rw [Real.div_rpow (hposK j).le (hposN j).le,
    Real.rpow_neg (hposK j).le, Real.rpow_neg (hposN j).le]
  have hKpow := (Real.rpow_pos_of_pos (hposK j) s.val).ne'
  have hNpow := (Real.rpow_pos_of_pos (hposN j) s.val).ne'
  field_simp

/-- The companion standard deviation divided by `K^{s/2}` tends to one.
See the proof of Corollary 1.1 in the paper, the Slutsky factor. -/
theorem mesoscopic_gap_sqrt_ratio_limit (s : Riesz1.RieszExponent)
    (K N : ℕ → ℕ+) (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => Real.sqrt ((N j : ℝ) ^ s.val *
      Riesz1.periodicZeta s (((K j : ℝ) / (N j : ℝ) : ℝ) : UnitAddCircle)) /
        (K j : ℝ) ^ (s.val / 2)) atTop (𝓝 1) := by
  have h := (mesoscopic_gap_profile_ratio_limit s K N hKN).sqrt
  rw [Real.sqrt_one] at h
  convert h using 1
  funext j
  rw [Real.sqrt_div' _ (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (K j : ℝ)) _)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (K j : ℝ))]
  congr 1
  ring

/-- The cyclic sum at label zero is the library's microscopic span.
See the proof of Corollary 1.1 in the paper: no second span encoding is introduced.
The empty sum and the full-cycle boundary are included. -/
theorem cyclicGapSum_zero_eq_span {N : ℕ+} (X : Riesz1.Configuration N) (K : ℕ)
    (hK : K ≤ (N : ℕ)) :
    cyclicGapSum N ⟨0, N.pos⟩ K (gapVector X) =
      (N : ℝ) * (Riesz1.cyclicLift X K - Riesz1.cyclicLift X 0) := by
  rw [cyclicGapSum]
  have heq : (∑ a ∈ Finset.range K,
      gapVector X ⟨(0 + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩) =
      ∑ a ∈ Finset.range K, Riesz1.gap X (0 + (a : ℤ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    have haN : a < (N : ℕ) := lt_of_lt_of_le (Finset.mem_range.mp ha) hK
    simp only [Nat.mod_eq_of_lt haN, zero_add]
    rfl
  rw [heq, Riesz1.sum_gap_range_eq_blockLength]
  simp only [Riesz1.blockLength, zero_add]

/-- The bridge to the exact companion normalized variable, with the cyclic sum.
See the proof of Corollary 1.1 in the paper. -/
theorem normalizedGap_eq_cyclicGapSum (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (K : ℕ) (hK : 1 ≤ K ∧ K ≤ (N : ℕ) / 2) (X : Riesz1.Configuration N) :
    Riesz1.normalizedGap (longParameters β s) N K hK X =
      (cyclicGapSum N ⟨0, N.pos⟩ K (gapVector X) - K) /
        Real.sqrt ((N : ℝ) ^ s.val *
          Riesz1.periodicZeta s (((K : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) := by
  rw [cyclicGapSum_zero_eq_span X K (hK.2.trans (Nat.div_le_self _ _))]
  rfl

end Riesz2

end
