/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GoodBlockEvent
public import Riesz1.Rigidity.GapLawSimplex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# The middle-normalized interaction differential

Finite algebra for Lemma 6.4 and the period-error estimate in the proof of Proposition
6.6. A vector of pinned particle forces determines exactly one middle-normalized gap
differential.
-/

public section
noncomputable section
open scoped BigOperators
open Finset

namespace Riesz2.InteractionDifferential

/-- The boundary weight of Lemma 6.4. The single formula
equals the displayed expression in each of the two exponent regimes. -/
@[expose] def boundaryWeight (s : ℝ) (n : ℕ+) (j : Fin (n : ℕ)) : ℝ :=
  (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (min s 1 / 2 - s)

/-- The long-range weight has the source exponent `-s/2`. -/
theorem boundaryWeight_long {s : ℝ} (hs : s < 1) (n : ℕ+) (j : Fin (n : ℕ)) :
    boundaryWeight s n j =
      (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s / 2 : ℝ) := by
  unfold boundaryWeight
  rw [min_eq_left hs.le]
  congr 1
  ring

/-- The short-range weight has the source exponent `1/2-s`. -/
theorem boundaryWeight_short {s : ℝ} (hs : 1 < s) (n : ℕ+) (j : Fin (n : ℕ)) :
    boundaryWeight s n j =
      (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ ((1 : ℝ) / 2 - s) := by
  simp only [boundaryWeight, min_eq_right hs.le]

/-- The boundary distance is always positive, including both endpoints
and the singleton. Thus the real powers have no zero-base ambiguity. -/
theorem boundary_distance_pos (n : ℕ+) (j : Fin (n : ℕ)) :
    (0 : ℝ) < (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
  have hj := j.isLt
  have h : 0 < min (j.val + 1) ((n : ℕ) - j.val) := by omega
  exact_mod_cast h

/-- Positivity of the source boundary weights. -/
theorem boundaryWeight_pos (s : ℝ) (n : ℕ+) (j : Fin (n : ℕ)) :
    0 < boundaryWeight s n j :=
  Real.rpow_pos_of_pos (boundary_distance_pos n j) _

/-- The small loss in the exterior-force power sum is absorbed into
`n^ε`, exactly as in the proof of Proposition 6.6. -/
theorem boundary_power_loss (s : ℝ) (n : ℕ+) (j : Fin (n : ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (min s 1 / 2 + ε - s) ≤
      (n : ℝ) ^ ε * boundaryWeight s n j := by
  have hd := boundary_distance_pos n j
  have hn : (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ≤ (n : ℕ) := by omega
  have hnr : ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := Real.rpow_le_rpow hd.le hnr hε
  have he : min s 1 / 2 + ε - s = (min s 1 / 2 - s) + ε := by ring
  rw [he, Real.rpow_add hd]
  exact (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hd.le _)).trans_eq (mul_comm _ _)

/-- The zero-based middle label, corresponding to `⌈(n+1)/2⌉` in the
one-based convention for `n+1` gaps. -/
@[expose] def middle (n : ℕ) : Fin (n + 1) := ⟨n / 2, by omega⟩

/-- The representative of Lemma 6.4 reconstructed from all
`n` pinned forces. It has `n+1` components. No endpoint force is invented. -/
@[expose] def pinnedRepresentative {n : ℕ} (f : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  (∑ i ∈ univ.filter (fun i : Fin n => i.val < (middle n).val), f i) -
    ∑ i ∈ univ.filter (fun i : Fin n => i.val < j.val), f i

/-- The specified middle component is zero. This includes the singleton. -/
theorem pinnedRepresentative_middle {n : ℕ} (f : Fin n → ℝ) :
    pinnedRepresentative f (middle n) = 0 := by
  simp only [pinnedRepresentative, sub_self]

/-- Consecutive prefixes differ by precisely one pinned force. -/
theorem prefix_succ {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ i ∈ univ.filter (fun i : Fin n => i.val < j.val + 1), f i) =
      (∑ i ∈ univ.filter (fun i : Fin n => i.val < j.val), f i) + f j := by
  simpa only [Riesz1.partialSum_eq_sum_filter_real, Fin.val_succ, Fin.val_castSucc] using
    Fin.partialSum_succ f j

/-- The reconstruction satisfies every prescribed adjacent difference. -/
theorem pinnedRepresentative_sub {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    pinnedRepresentative f j.castSucc - pinnedRepresentative f j.succ = f j := by
  simp only [pinnedRepresentative, Fin.val_castSucc, Fin.val_succ, prefix_succ]
  ring

/-- A zero-middle representative is unique. This supplies the uniqueness
clause of Lemma 6.4 without a non-unique choice. -/
theorem pinnedRepresentative_unique {n : ℕ} (f : Fin n → ℝ)
    (b : Fin (n + 1) → ℝ) (hm : b (middle n) = 0)
    (hb : ∀ j : Fin n, b j.castSucc - b j.succ = f j) :
    b = pinnedRepresentative f := by
  have hdiff : ∀ j : Fin (n + 1),
      b j - pinnedRepresentative f j = b 0 - pinnedRepresentative f 0 := by
    apply Fin.induction
    · rfl
    · intro j hj
      have hp := pinnedRepresentative_sub f j
      have h := hb j
      linarith
  have hmid := hdiff (middle n)
  rw [hm, pinnedRepresentative_middle] at hmid
  funext j
  have h := hdiff j
  linarith

/-- The reconstructed representative acts on a zero-sum gap vector by
the prefix velocities in the pinned particle chart. This is exactly the
summation-by-parts identity in Lemma 6.4. -/
theorem pinnedRepresentative_pairing {n : ℕ} (f : Fin n → ℝ)
    (v : Fin (n + 1) → ℝ) (hv : ∑ j, v j = 0) :
    (∑ j, pinnedRepresentative f j * v j) =
      ∑ i, f i * ∑ j ∈ univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), v j := by
  classical
  simp only [pinnedRepresentative, sub_mul, sum_sub_distrib, ← mul_sum, hv, mul_zero,
    zero_sub]
  simp_rw [sum_mul, sum_filter]
  rw [sum_comm, ← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  have hsplit := sum_filter_add_sum_filter_not univ
    (fun j : Fin (n + 1) => j.val ≤ i.val) v
  rw [hv] at hsplit
  have he : (∑ j : Fin (n + 1), if i.val < j.val then f i * v j else 0) =
      f i * ∑ j ∈ univ.filter (fun j : Fin (n + 1) => ¬j.val ≤ i.val), v j := by
    simp only [mul_sum, sum_filter, not_le, mul_ite, mul_zero]
  rw [he]
  simp only [sum_filter] at hsplit ⊢
  linear_combination -(f i) * hsplit

/-- An ambient gap differential and the reconstructed pinned differential
differ exactly by their middle component. This is independent of which
ambient extension represents the intrinsic differential (Lemma 6.4). -/
theorem pinnedRepresentative_of_coefficients {n : ℕ} (q : Fin (n + 1) → ℝ) :
    pinnedRepresentative (fun i : Fin n => q i.castSucc - q i.succ) =
      fun j => q j - q (middle n) := by
  symm
  apply pinnedRepresentative_unique
  · exact sub_self _
  · intro j
    ring

/-- Subtracting the middle coefficient preserves the action on every
tangent gap vector, as required by Lemma 6.4. -/
theorem pinnedRepresentative_coefficient_pairing {n : ℕ} (q v : Fin (n + 1) → ℝ)
    (hv : ∑ j, v j = 0) :
    (∑ j, pinnedRepresentative (fun i : Fin n => q i.castSucc - q i.succ) j * v j) =
      ∑ j, q j * v j := by
  rw [pinnedRepresentative_of_coefficients]
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, hv, mul_zero, sub_zero]

/-- To the left of the middle, reconstruction is the sum towards that
middle, as used in the proof of Proposition 6.6. -/
theorem pinnedRepresentative_left {n : ℕ} (f : Fin n → ℝ) (j : Fin (n + 1))
    (hj : j.val ≤ (middle n).val) :
    pinnedRepresentative f j =
      ∑ i ∈ univ.filter (fun i : Fin n => j.val ≤ i.val ∧ i.val < (middle n).val), f i := by
  classical
  let S := univ.filter (fun i : Fin n => i.val < (middle n).val)
  let T := univ.filter (fun i : Fin n => i.val < j.val)
  have hTS : T ⊆ S := fun i hi => by
    simp only [T, S, mem_filter, mem_univ, true_and] at hi ⊢
    omega
  have he : S \ T = univ.filter (fun i : Fin n => j.val ≤ i.val ∧ i.val < (middle n).val) := by
    ext i
    simp only [S, T, mem_sdiff, mem_filter, mem_univ, true_and]
    omega
  rw [pinnedRepresentative, ← sum_sdiff hTS, he]
  simp only [T, add_sub_cancel_right]

/-- To the right of the pinned middle, reconstruction is the negative
sum towards that middle, with the correct two endpoints. -/
theorem pinnedRepresentative_right {n : ℕ} (f : Fin n → ℝ) (j : Fin (n + 1))
    (hj : (middle n).val ≤ j.val) :
    pinnedRepresentative f j =
      -(∑ i ∈ univ.filter (fun i : Fin n => (middle n).val ≤ i.val ∧ i.val < j.val), f i) := by
  classical
  let S := univ.filter (fun i : Fin n => i.val < j.val)
  let T := univ.filter (fun i : Fin n => i.val < (middle n).val)
  have hTS : T ⊆ S := fun i hi => by
    simp only [T, S, mem_filter, mem_univ, true_and] at hi ⊢
    omega
  have he : S \ T = univ.filter (fun i : Fin n => (middle n).val ≤ i.val ∧ i.val < j.val) := by
    ext i
    simp only [S, T, mem_sdiff, mem_filter, mem_univ, true_and]
    omega
  rw [pinnedRepresentative, ← neg_sub (∑ i ∈ S, f i) (∑ i ∈ T, f i),
    ← sum_sdiff hTS, he]
  rw [add_sub_cancel_right]

/-- The force sum used in the proof of Proposition 6.6 runs only
between the component and its middle pin. No spurious full-row factor
is introduced by choosing the representative. -/
theorem pinnedRepresentative_abs_le {n : ℕ} (f : Fin n → ℝ) (j : Fin (n + 1)) :
    |pinnedRepresentative f j| ≤
      ∑ i ∈ univ.filter (fun i : Fin n =>
        min j.val (middle n).val ≤ i.val ∧ i.val < max j.val (middle n).val), |f i| := by
  rcases le_total j.val (middle n).val with hj | hj
  · rw [pinnedRepresentative_left f j hj, min_eq_left hj, max_eq_right hj]
    exact abs_sum_le_sum_abs _ _
  · rw [pinnedRepresentative_right f j hj, min_eq_right hj, max_eq_left hj, abs_neg]
    exact abs_sum_le_sum_abs _ _

/-- The finite-period correction in the proof of Proposition 6.6, with no asymptotic size restriction. -/
theorem period_error_le {s n N : ℝ} (hs : 0 < s) (hn : 0 < n) (hN : 0 < N)
    (hsize : n ^ (2 / s) ≤ N) :
    n * N ^ (-s) ≤ n⁻¹ := by
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hn.le (2 / s)) hsize hs.le
  rw [← Real.rpow_mul hn.le, div_mul_cancel₀ 2 hs.ne', Real.rpow_two] at hpow
  rw [Real.rpow_neg hN.le]
  have hNpow : 0 < N ^ s := Real.rpow_pos_of_pos hN s
  calc
    n * (N ^ s)⁻¹ ≤ n * (n ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left ((inv_le_inv₀ hNpow (sq_pos_of_pos hn)).mpr hpow) hn.le
    _ = n⁻¹ := by field_simp

end Riesz2.InteractionDifferential
