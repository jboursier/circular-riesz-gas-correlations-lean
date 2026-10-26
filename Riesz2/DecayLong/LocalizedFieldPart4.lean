/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedFieldPart2
public import Riesz2.DecayLong.LocalizedFieldPart3
public import Riesz2.DecayLong.LocalizedMatrixPart6

/-!
# Exterior field: boundary truncation and sharp translation estimates

Supporting estimates for the proof of Proposition 5.15. All truncations
are literal restrictions of the given sequence, with zero extension on its
existing component cycle.
-/

@[expose] public section
noncomputable section

open MeasureTheory Finset
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.ScalarDirichletScaling

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- Scalar multiplication of the bilinear form on its original domain. -/
@[reducible] def scale (c : ℝ) (Q : ScalarFormData ν) : ScalarFormData ν :=
  ⟨Q.1, c • Q.2⟩

/-- Positive scaling preserves the closed Dirichlet form properties. -/
theorem isClosed_scale (c : ℝ) (hc : 0 < c) (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) :
    IsClosedScalarDirichletForm (scale c Q) := by
  have he (f g : Q.1) : (scale c Q).2 f g = c * Q.2 f g := rfl
  refine ⟨hQ.1, ?_, ?_, ?_, ?_⟩
  · intro f g
    rw [he, he, hQ.2.1]
  · intro f
    rw [he]
    exact mul_nonneg hc.le (hQ.2.2.1 f)
  · intro f u hfu hfc
    have hcf : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ i j : ℕ, k ≤ i → k ≤ j →
        ‖(f i).val - (f j).val‖ ^ 2 + Q.2 (f i - f j) (f i - f j) < ε := by
      intro ε hε
      let d := min 1 c
      have hd : 0 < d := lt_min zero_lt_one hc
      obtain ⟨k, hk⟩ := hfc (d * ε) (mul_pos hd hε)
      refine ⟨k, fun i j hi hj => ?_⟩
      have h := hk i j hi hj
      rw [he] at h
      have hnorm := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) c)
        (sq_nonneg ‖(f i).val - (f j).val‖)
      have henergy := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) c)
        (hQ.2.2.1 (f i - f j))
      have hh : d * (‖(f i).val - (f j).val‖ ^ 2 + Q.2 (f i - f j) (f i - f j)) < d * ε := by
        dsimp only [d] at *
        nlinarith only [hnorm, henergy, h]
      exact (mul_lt_mul_iff_right₀ hd).mp hh
    obtain ⟨g, hg, hfg⟩ := hQ.2.2.2.1 f u hfu hcf
    refine ⟨g, hg, ?_⟩
    simpa only [he, mul_zero] using hfg.const_mul c
  · intro φ hφ hφ0 f
    obtain ⟨g, hg, hge⟩ := hQ.2.2.2.2 φ hφ hφ0 f
    exact ⟨g, hg, mul_le_mul_of_nonneg_left hge hc.le⟩

end Riesz2.ScalarDirichletScaling

namespace Riesz2.LocalizedFieldPart4

/-- See the proof of Proposition 5.15 in the paper: each positive distance from the two
ends of an interval occurs at most twice. No monotonicity is required. -/
theorem endpoint_profile_sum_internal (n : ℕ+) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    (∑ i : Fin (n : ℕ), w (min (i.val + 1) ((n : ℕ) - i.val))) ≤
      2 * ∑ k ∈ Icc 1 (n : ℕ), w k := by
  have hf : (∑ i : Fin (n : ℕ), w (i.val + 1)) ≤ ∑ k ∈ Icc 1 (n : ℕ), w k := by
    apply sum_le_sum_of_injOn (fun i : Fin (n : ℕ) => i.val + 1)
    · intro i _ j _ hij
      dsimp only at hij
      apply Fin.ext
      omega
    · intro k hk
      obtain ⟨i, _, rfl⟩ := mem_image.mp hk
      exact mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
    · intro i _
      exact le_rfl
    · intro k _ _
      exact hw k
  have hb : (∑ i : Fin (n : ℕ), w ((n : ℕ) - i.val)) ≤ ∑ k ∈ Icc 1 (n : ℕ), w k := by
    apply sum_le_sum_of_injOn (fun i : Fin (n : ℕ) => (n : ℕ) - i.val)
    · intro i _ j _ hij
      dsimp only at hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · intro k hk
      obtain ⟨i, _, rfl⟩ := mem_image.mp hk
      exact mem_Icc.mpr ⟨by have := i.isLt; omega, Nat.sub_le _ _⟩
    · intro i _
      exact le_rfl
    · intro k _ _
      exact hw k
  calc
    _ ≤ ∑ i : Fin (n : ℕ), (w (i.val + 1) + w ((n : ℕ) - i.val)) := by
      apply sum_le_sum
      intro i _
      rcases le_total (i.val + 1) ((n : ℕ) - i.val) with h | h
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (hw _)
      · rw [min_eq_right h]
        exact le_add_of_nonneg_left (hw _)
    _ ≤ _ := by rw [sum_add_distrib]; linarith

/-- See the proof of Proposition 5.15 in the paper: the discarded endpoint strips of
width k have subcritical power mass, including overlapping strips. -/
theorem boundary_strip_sum_internal (n : ℕ+) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ i : Fin (n : ℕ), if min (i.val + 1) ((n : ℕ) - i.val) ≤ k then
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a) else 0) ≤
      (2 / (1 - a)) * (k : ℝ) ^ (1 - a) := by
  have hp := endpoint_profile_sum_internal n
    (fun t => if t ≤ k then (t : ℝ) ^ (-a) else 0)
    (fun t => by split_ifs <;> positivity)
  have hs : (∑ t ∈ Icc 1 (n : ℕ), if t ≤ k then (t : ℝ) ^ (-a) else 0) ≤
      ∑ t ∈ Icc 1 k, (t : ℝ) ^ (-a) := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro t ht
      exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp ht).1).1, (mem_filter.mp ht).2⟩
    · intro t _ _
      positivity
  have hb := (subcritical_power_sum ha ha1 hk).2
  calc
    _ ≤ 2 * ∑ t ∈ Icc 1 k, (t : ℝ) ^ (-a) := hp.trans (by gcongr)
    _ ≤ 2 * ((k : ℝ) ^ (1 - a) / (1 - a)) := by gcongr
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: the increment power tail after
removing k endpoints. The positive cutoff avoids the value of a power at zero. -/
theorem increment_power_tail_internal (a : ℝ) (ha : 0 < a)
    (k N : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Icc 1 N, if k < t then (t : ℝ) ^ (-1 - a) else 0) ≤
      (1 + 1 / a) * (k : ℝ) ^ (-a) := by
  have hf : (∑ t : Fin N, if (k : ℝ) ≤ (t.val + 1 : ℝ) then
      (t.val + 1 : ℝ) ^ (-(1 + a)) else 0) =
      ∑ t ∈ Icc 1 N, if k ≤ t then (t : ℝ) ^ (-1 - a) else 0 := by
    rw [show Icc 1 N = Ico 1 (N + 1) by ext t; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => if (k : ℝ) ≤ (t : ℝ) + 1 then
      ((t : ℝ) + 1) ^ (-(1 + a)) else 0) N]
    apply sum_congr rfl
    intro t _
    have hc : k ≤ t + 1 ↔ (k : ℝ) ≤ (t : ℝ) + 1 := by
      exact_mod_cast (Iff.rfl : k ≤ t + 1 ↔ k ≤ t + 1)
    simp only [Nat.cast_add, Nat.cast_one, add_comm 1, hc,
      show -(1 + a) = -1 - a by ring]
  have h := BoundaryEntries.finite_length_tail_internal (R := (k : ℝ))
    (by linarith : 1 < 1 + a) (by exact_mod_cast hk) N
  rw [hf] at h
  have hh : (1 + 1 / (1 + a - 1)) * (k : ℝ) ^ (1 - (1 + a)) =
      (1 + 1 / a) * (k : ℝ) ^ (-a) := by congr 2 <;> ring
  rw [hh] at h
  apply le_trans _ h
  apply sum_le_sum
  intro t _
  split_ifs <;> first | exact le_rfl | positivity | omega

section Truncation

variable {V : Type*} [NormedAddCommGroup V]

/-- See the proof of Proposition 5.15 in the paper: literal interior truncation discards
only the two endpoint strips. Its error bound includes their possible overlap. -/
theorem truncation_error_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (a A : ℝ) (ha : 0 < a) (ha1 : a < 1) (hA : 0 ≤ A)
    (f : Fin (m : ℕ) → V) (hsupport : ∀ i, (n : ℕ) ≤ i.val → f i = 0)
    (hf : ∀ i : Fin (n : ℕ), ‖f (i.castLE hnm)‖ ≤ A *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a))
    (k : ℕ) (hk : 1 ≤ k) :
    let g := fun i : Fin (m : ℕ) => if k ≤ i.val ∧ i.val + k < (n : ℕ) then f i else 0
    (∑ i, ‖f i - g i‖) ≤ A * (2 / (1 - a)) * (k : ℝ) ^ (1 - a) := by
  intro g
  have hsup (i : Fin (m : ℕ)) (hi : (n : ℕ) ≤ i.val) : ‖f i - g i‖ = 0 := by
    have hh : ¬(k ≤ i.val ∧ i.val + k < (n : ℕ)) := by omega
    simp only [g, ite_eq_right hh, hsupport i hi, sub_zero, norm_zero]
  rw [LocalizedBoundary.sum_active_internal n m hnm (fun i => ‖f i - g i‖) hsup]
  calc
    _ ≤ A * ∑ i : Fin (n : ℕ), if min (i.val + 1) ((n : ℕ) - i.val) ≤ k then
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a) else 0 := by
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      by_cases h : k ≤ i.val ∧ i.val + k < (n : ℕ)
      · have hh : ¬min (i.val + 1) ((n : ℕ) - i.val) ≤ k := by have := i.isLt; omega
        simp only [g, Fin.val_castLE, ite_eq_left h, sub_self, norm_zero, ite_eq_right hh, mul_zero, le_refl]
      · have hh : min (i.val + 1) ((n : ℕ) - i.val) ≤ k := by have := i.isLt; omega
        simpa only [g, Fin.val_castLE, ite_eq_right h, sub_zero, ite_eq_left hh] using hf i
    _ ≤ A * ((2 / (1 - a)) * (k : ℝ) ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left (boundary_strip_sum_internal n a ha ha1 k hk) hA
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: variation of the interior truncation.
The first two summands on the right are its two cutoff jumps. The last
summand sums the retained neighboring increments. -/
theorem truncation_variation_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (f : Fin (m : ℕ) → V)
    (hf : ∀ i : Fin (n : ℕ), ‖f (i.castLE hnm)‖ ≤ A *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a))
    (hinc : ∀ i : Fin (m : ℕ), 0 < i.val → i.val < (n : ℕ) →
      ‖f i - f (i - 1)‖ ≤ A *
        ((min i.val ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-1 - a))
    (k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k < (n : ℕ)) :
    let g := fun i : Fin (m : ℕ) => if k ≤ i.val ∧ i.val + k < (n : ℕ) then f i else 0
    (∑ i, ‖g (i - 1) - g i‖) ≤
      A * (2 + 2 * (1 + 1 / a)) * (k : ℝ) ^ (-a) := by
  intro g
  have hm : 2 ≤ (m : ℕ) := by omega
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpoint (i : Fin (m : ℕ)) :
      ‖g (i - 1) - g i‖ ≤
        (if i.val = k then A * (k : ℝ) ^ (-a) else 0) +
        (if i.val = (n : ℕ) - k then A * (k : ℝ) ^ (-a) else 0) +
        (if k < i.val ∧ i.val + k < (n : ℕ) then
          A * ((i.val : ℝ) ^ (-1 - a) + (((n : ℕ) - i.val : ℕ) : ℝ) ^ (-1 - a)) else 0) := by
    have hnon : 0 ≤
        (if i.val = k then A * (k : ℝ) ^ (-a) else 0) +
        (if i.val = (n : ℕ) - k then A * (k : ℝ) ^ (-a) else 0) +
        (if k < i.val ∧ i.val + k < (n : ℕ) then
          A * ((i.val : ℝ) ^ (-1 - a) + (((n : ℕ) - i.val : ℕ) : ℝ) ^ (-1 - a)) else 0) := by positivity
    by_cases hiz : i = 0
    · subst i
      have hp : (0 - 1 : Fin (m : ℕ)).val = (m : ℕ) - 1 := by
        simp [Fin.val_neg', Nat.mod_eq_of_lt (by omega : 1 < (m : ℕ))]
      have h0 : ¬(k ≤ (0 : Fin (m : ℕ)).val ∧ (0 : Fin (m : ℕ)).val + k < (n : ℕ)) := by simp; omega
      have hp0 : ¬(k ≤ (0 - 1 : Fin (m : ℕ)).val ∧
          (0 - 1 : Fin (m : ℕ)).val + k < (n : ℕ)) := by rw [hp]; omega
      simpa only [g, ite_eq_right hp0, ite_eq_right h0, sub_self, norm_zero] using hnon
    have hp : (i - 1).val = i.val - 1 := Fin.val_sub_one_of_ne_zero hiz
    by_cases hi : k ≤ i.val ∧ i.val + k < (n : ℕ)
    · by_cases hj : k ≤ (i - 1).val ∧ (i - 1).val + k < (n : ℕ)
      · have hint : k < i.val ∧ i.val + k < (n : ℕ) := by rw [hp] at hj; omega
        have hb := hinc i (by omega) (by omega)
        have hmin : ((min i.val ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-1 - a) ≤
            (i.val : ℝ) ^ (-1 - a) + (((n : ℕ) - i.val : ℕ) : ℝ) ^ (-1 - a) := by
          rcases le_total i.val ((n : ℕ) - i.val) with h | h
          · rw [min_eq_left h]; exact le_add_of_nonneg_right (by positivity)
          · rw [min_eq_right h]; exact le_add_of_nonneg_left (by positivity)
        rw [show g (i - 1) = f (i - 1) from ite_eq_left hj, show g i = f i from ite_eq_left hi, norm_sub_rev]
        exact (hb.trans (mul_le_mul_of_nonneg_left hmin hA)).trans (by rw [ite_eq_left hint]; exact le_add_of_nonneg_left (by positivity))
      · have he : i.val = k := by rw [hp] at hj; omega
        have hright : i.val ≠ (n : ℕ) - k := by omega
        have hint : ¬(k < i.val ∧ i.val + k < (n : ℕ)) := by omega
        have hfi := hf ⟨i.val, by omega⟩
        have hid : (⟨i.val, by omega⟩ : Fin (n : ℕ)).castLE hnm = i := Fin.ext rfl
        rw [hid] at hfi
        have hd : k ≤ min (i.val + 1) ((n : ℕ) - i.val) := by omega
        have hb := Real.rpow_le_rpow_of_nonpos hkp
          (show (k : ℝ) ≤ ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) by exact_mod_cast hd)
          (by linarith : -a ≤ 0)
        simpa only [g, ite_eq_left hi, ite_eq_right hj, zero_sub, norm_neg, ite_eq_left he, ite_eq_right hright,
          ite_eq_right hint, add_zero] using hfi.trans (mul_le_mul_of_nonneg_left hb hA)
    · by_cases hj : k ≤ (i - 1).val ∧ (i - 1).val + k < (n : ℕ)
      · have he : i.val = (n : ℕ) - k := by rw [hp] at hj; omega
        have hleft : i.val ≠ k := by omega
        have hint : ¬(k < i.val ∧ i.val + k < (n : ℕ)) := by omega
        have hfi := hf ⟨(i - 1).val, by rw [hp]; omega⟩
        have hid : (⟨(i - 1).val, by rw [hp]; omega⟩ : Fin (n : ℕ)).castLE hnm = i - 1 := Fin.ext rfl
        rw [hid] at hfi
        have hd : k ≤ min ((i - 1).val + 1) ((n : ℕ) - (i - 1).val) := by rw [hp]; omega
        have hb := Real.rpow_le_rpow_of_nonpos hkp
          (show (k : ℝ) ≤ ((min ((i - 1).val + 1) ((n : ℕ) - (i - 1).val) : ℕ) : ℝ) by exact_mod_cast hd)
          (by linarith : -a ≤ 0)
        simpa only [g, ite_eq_right hi, ite_eq_left hj, sub_zero, ite_eq_left he, ite_eq_right hleft,
          ite_eq_right hint, zero_add, add_zero] using hfi.trans (mul_le_mul_of_nonneg_left hb hA)
      · simpa only [g, ite_eq_right hi, ite_eq_right hj, sub_self, norm_zero] using hnon
  let S := univ.filter (fun i : Fin (m : ℕ) => k < i.val ∧ i.val + k < (n : ℕ))
  have hfront : (∑ i ∈ S, (i.val : ℝ) ^ (-1 - a)) ≤
      (1 + 1 / a) * (k : ℝ) ^ (-a) := by
    apply le_trans _ (increment_power_tail_internal a ha k (n : ℕ) hk)
    apply sum_le_sum_of_injOn (fun i : Fin (m : ℕ) => i.val)
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
      have hh := (mem_filter.mp hi).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi
      have hh := (mem_filter.mp hi).2
      simp only [ite_eq_left hh.1, le_refl]
    · intro t _ _
      positivity
  have hback : (∑ i ∈ S, (((n : ℕ) - i.val : ℕ) : ℝ) ^ (-1 - a)) ≤
      (1 + 1 / a) * (k : ℝ) ^ (-a) := by
    apply le_trans _ (increment_power_tail_internal a ha k (n : ℕ) hk)
    apply sum_le_sum_of_injOn (fun i : Fin (m : ℕ) => (n : ℕ) - i.val)
    · intro i hi j hj hij
      dsimp only at hij
      have hi := (mem_filter.mp hi).2
      have hj := (mem_filter.mp hj).2
      apply Fin.ext
      omega
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
      have hh := (mem_filter.mp hi).2
      exact mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩
    · intro i hi
      have hh : k < (n : ℕ) - i.val := by have := (mem_filter.mp hi).2; omega
      simp only [ite_eq_left hh, le_refl]
    · intro t _ _
      positivity
  have hjump (t : ℕ) (ht : t < (m : ℕ)) :
      (∑ i : Fin (m : ℕ), if i.val = t then A * (k : ℝ) ^ (-a) else 0) = A * (k : ℝ) ^ (-a) := by
    have he (i : Fin (m : ℕ)) : i.val = t ↔ i = ⟨t, ht⟩ := by
      constructor
      · exact fun h => Fin.ext h
      · exact fun h => congrArg Fin.val h
    simp only [he, sum_ite_eq', mem_univ, ite_true]
  calc
    _ ≤ ∑ i : Fin (m : ℕ),
        ((if i.val = k then A * (k : ℝ) ^ (-a) else 0) +
        (if i.val = (n : ℕ) - k then A * (k : ℝ) ^ (-a) else 0) +
        (if k < i.val ∧ i.val + k < (n : ℕ) then
          A * ((i.val : ℝ) ^ (-1 - a) + (((n : ℕ) - i.val : ℕ) : ℝ) ^ (-1 - a)) else 0)) :=
      sum_le_sum fun i _ => hpoint i
    _ = 2 * (A * (k : ℝ) ^ (-a)) +
        A * ((∑ i ∈ S, (i.val : ℝ) ^ (-1 - a)) +
          ∑ i ∈ S, (((n : ℕ) - i.val : ℕ) : ℝ) ^ (-1 - a)) := by
      rw [sum_add_distrib, sum_add_distrib, hjump k (by omega), hjump ((n : ℕ) - k) (by omega)]
      rw [← sum_filter, ← mul_sum, sum_add_distrib]
      dsimp only [S]
      ring
    _ ≤ 2 * (A * (k : ℝ) ^ (-a)) +
        A * (2 * ((1 + 1 / a) * (k : ℝ) ^ (-a))) := by gcongr; linarith
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: a translation costs at most twice
the full mass, without a support or regularity assumption. -/
theorem shift_mass_internal (m : ℕ+) (f : Fin (m : ℕ) → V) (h : Fin (m : ℕ)) :
    (∑ i, ‖f (i - h) - f i‖) ≤ 2 * ∑ i, ‖f i‖ := by
  calc
    _ ≤ ∑ i, (‖f (i - h)‖ + ‖f i‖) := sum_le_sum fun i _ => norm_sub_le _ _
    _ = _ := by rw [sum_add_distrib, LocalizedField.sum_norm_shift_internal]; ring

/-- See the proof of Proposition 5.15 in the paper: the sharp exponent `1-a` follows
from entry and increment bounds on a zero-extended interval. The cutoff
jumps are retained, and every cyclic shift, including zero, is covered. -/
theorem boundary_power_translation_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (a A : ℝ) (ha : 0 < a) (ha1 : a < 1) (hA : 0 ≤ A)
    (f : Fin (m : ℕ) → V) (hsupport : ∀ i, (n : ℕ) ≤ i.val → f i = 0)
    (hf : ∀ i : Fin (n : ℕ), ‖f (i.castLE hnm)‖ ≤ A *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a))
    (hinc : ∀ i : Fin (m : ℕ), 0 < i.val → i.val < (n : ℕ) →
      ‖f i - f (i - 1)‖ ≤ A *
        ((min i.val ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-1 - a))
    (h : Fin (m : ℕ)) :
    (∑ i, ‖f (i - h) - f i‖) ≤
      A * (8 / (1 - a) + 4 + 2 / a) *
        (Riesz1.cyclicIndexDistance m h 0 : ℝ) ^ (1 - a) := by
  let k := Riesz1.cyclicIndexDistance m h 0
  have hb : 0 < 1 - a := sub_pos.mpr ha1
  have hC : 0 ≤ 8 / (1 - a) + 4 + 2 / a := by positivity
  by_cases hkz : k = 0
  · have hh : h = 0 := (cyclicIndexDistance_eq_zero_iff h 0).mp hkz
    subst h
    simp only [sub_zero, sub_self, norm_zero, sum_const_zero]
    positivity
  have hk : 1 ≤ k := by omega
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmass := LocalizedField.extended_mass_internal n m hnm a A ha ha1 hA f hsupport hf
  by_cases hkn : 2 * k < (n : ℕ)
  · let g := fun i : Fin (m : ℕ) => if k ≤ i.val ∧ i.val + k < (n : ℕ) then f i else 0
    have he := truncation_error_internal n m hnm a A ha ha1 hA f hsupport hf k hk
    have hv := truncation_variation_internal n m hnm a A ha hA f hf hinc k hk hkn
    have hs := LocalizedField.shift_approximation_internal m f g h
    have hpow : (k : ℝ) * (k : ℝ) ^ (-a) = (k : ℝ) ^ (1 - a) := by
      rw [show 1 - a = -a + 1 by ring, Real.rpow_add_one hkp.ne']
      ring
    calc
      _ ≤ 2 * (A * (2 / (1 - a)) * (k : ℝ) ^ (1 - a)) +
          (k : ℝ) * (A * (2 + 2 * (1 + 1 / a)) * (k : ℝ) ^ (-a)) :=
        hs.trans (add_le_add (mul_le_mul_of_nonneg_left he (by norm_num))
          (mul_le_mul_of_nonneg_left hv hkp.le))
      _ = A * (4 / (1 - a) + 4 + 2 / a) * (k : ℝ) ^ (1 - a) := by
        calc
          _ = A * (4 / (1 - a)) * (k : ℝ) ^ (1 - a) +
              A * (4 + 2 / a) * ((k : ℝ) * (k : ℝ) ^ (-a)) := by ring
          _ = _ := by rw [hpow]; ring
      _ ≤ _ := by dsimp only [k]; gcongr; linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb.le]
  · have hnk : (n : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show (n : ℕ) ≤ 2 * k by omega)
    have htwo : (2 : ℝ) ^ (1 - a) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith : 1 - a ≤ 1)
    have hn : (n : ℝ) ^ (1 - a) ≤ 2 * (k : ℝ) ^ (1 - a) := by
      calc
        _ ≤ (2 * (k : ℝ)) ^ (1 - a) := Real.rpow_le_rpow (by positivity) hnk hb.le
        _ = (2 : ℝ) ^ (1 - a) * (k : ℝ) ^ (1 - a) := Real.mul_rpow (by norm_num) hkp.le
        _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)
    calc
      _ ≤ 2 * (A * (2 / (1 - a)) * (n : ℝ) ^ (1 - a)) :=
        (shift_mass_internal m f h).trans (mul_le_mul_of_nonneg_left hmass (by norm_num))
      _ ≤ 2 * (A * (2 / (1 - a)) * (2 * (k : ℝ) ^ (1 - a))) := by gcongr
      _ = A * (8 / (1 - a)) * (k : ℝ) ^ (1 - a) := by ring
      _ ≤ _ := by dsimp only [k]; gcongr; linarith [div_pos (by norm_num : (0 : ℝ) < 2) ha]

/-- See the proof of Proposition 5.15 and equation (5.67) of the paper: scale-normalized
mass and sharp translation modulus from the two local bounds. The single
constant depends only on s, and n is the ordered active interval length. -/
theorem sharp_translation_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (R A : ℝ)
    (hR : 0 < R) (hnR : (n : ℝ) ≤ R) (hA : 0 ≤ A)
    (f : Fin (m : ℕ) → V) (hsupport : ∀ i, (n : ℕ) ≤ i.val → f i = 0)
    (hf : ∀ i : Fin (n : ℕ), ‖f (i.castLE hnm)‖ ≤ A * R ^ (-1 + s.val / 2) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2))
    (hinc : ∀ i : Fin (m : ℕ), 0 < i.val → i.val < (n : ℕ) →
      ‖f i - f (i - 1)‖ ≤ A * R ^ (-1 + s.val / 2) *
        ((min i.val ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-1 - s.val / 2)) :
    let C := 8 / (1 - s.val / 2) + 4 + 2 / (s.val / 2)
    (∑ i, ‖f i‖) ≤ C * A ∧
    ∀ h : Fin (m : ℕ), (∑ i, ‖f (i - h) - f i‖) ≤
      C * A * min 1 (((Riesz1.cyclicIndexDistance m h 0 : ℝ) / R) ^ (1 - s.val / 2)) := by
  intro C
  have ha : 0 < s.val / 2 := by linarith [s.property.1]
  have ha1 : s.val / 2 < 1 := by linarith [s.property.2]
  have hb : 0 < 1 - s.val / 2 := sub_pos.mpr ha1
  have hcoef : 4 / (1 - s.val / 2) ≤ C := by
    dsimp only [C]
    rw [show (8 : ℝ) / (1 - s.val / 2) = 4 / (1 - s.val / 2) + 4 / (1 - s.val / 2) by ring]
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb.le,
      div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le]
  have hmass := LocalizedField.scaled_extended_mass_internal s n m hnm R A hR hnR hA f hsupport hf
  have hnon : 0 ≤ C * A := by dsimp only [C]; positivity
  constructor
  · apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hA
    calc
      2 / (1 - s.val / 2) ≤ 4 / (1 - s.val / 2) :=
        div_le_div_of_nonneg_right (by norm_num) hb.le
      _ ≤ C := hcoef
  intro h
  have htotal : (∑ i, ‖f (i - h) - f i‖) ≤ C * A := by
    calc
      _ ≤ 2 * ((2 / (1 - s.val / 2)) * A) :=
        (shift_mass_internal m f h).trans (mul_le_mul_of_nonneg_left hmass (by norm_num))
      _ = (4 / (1 - s.val / 2)) * A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hA
  have hshift := boundary_power_translation_internal n m hnm (s.val / 2)
    (A * R ^ (-1 + s.val / 2)) ha ha1 (by positivity) f hsupport
    (by simpa only [neg_div] using hf) hinc h
  have hp : R ^ (-1 + s.val / 2) *
      (Riesz1.cyclicIndexDistance m h 0 : ℝ) ^ (1 - s.val / 2) =
      ((Riesz1.cyclicIndexDistance m h 0 : ℝ) / R) ^ (1 - s.val / 2) := by
    have hr : R ^ (-1 + s.val / 2) = (R ^ (1 - s.val / 2))⁻¹ := by
      rw [← Real.rpow_neg hR.le]
      congr 1
      ring
    rw [Real.div_rpow (by positivity) hR.le, hr, mul_comm]
    exact (div_eq_mul_inv _ _).symm
  have hsmall : (∑ i, ‖f (i - h) - f i‖) ≤ C * A *
      ((Riesz1.cyclicIndexDistance m h 0 : ℝ) / R) ^ (1 - s.val / 2) := by
    convert hshift using 1
    change C * A * _ = (A * R ^ (-1 + s.val / 2)) * C * _
    rw [← hp]
    ring
  rw [mul_min_of_nonneg _ _ hnon, mul_one]
  exact le_min htotal hsmall

end Truncation

/-- See the proof of Proposition 5.15 in the paper: transfer a positive power from an
endpoint distance to the larger separation radius. -/
theorem transfer_radius_power_internal {R δ : ℝ} (hδ : 0 < δ) (hδR : δ ≤ R)
    (p q t : ℝ) (ht : 0 ≤ t) :
    R ^ p * δ ^ q ≤ R ^ (p + t) * δ ^ (q - t) := by
  have hR : 0 < R := hδ.trans_le hδR
  have hh := Real.rpow_le_rpow hδ.le hδR ht
  calc
    _ = (R ^ p * δ ^ (q - t)) * δ ^ t := by
      rw [mul_assoc, ← Real.rpow_add hδ, sub_add_cancel]
    _ ≤ (R ^ p * δ ^ (q - t)) * R ^ t :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [mul_right_comm, ← Real.rpow_add hR]

/-- See the proof of Proposition 5.15, equations (5.65) and (5.66): normalize the
two centered exterior profiles to the claimed boundary powers. The same
constant works at and on both sides of s=1/2. -/
theorem exterior_profiles_internal (s : Riesz1.RieszExponent) :
    ∃ P : ℝ, 0 < P ∧ ∀ R δ : ℕ, 1 ≤ δ → δ ≤ R →
      ((R : ℝ) ^ (-1 : ℝ) + (R : ℝ) ^ (-(3 / 2 - s.val)) *
        Real.sqrt (∑ t ∈ Icc δ (4 * R), (t : ℝ) ^ (-2 * s.val))) ≤
        P * (R : ℝ) ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) ∧
      ((R : ℝ) ^ (-2 : ℝ) + (R : ℝ) ^ (-(3 / 2 - s.val)) *
        (δ : ℝ) ^ (-(1 / 2 + s.val))) ≤
        P * (R : ℝ) ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2) := by
  let B : ℝ := Real.sqrt (1 / (1 - s.val)) * 4 ^ ((1 - s.val) / 2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨2 + B, by positivity, ?_⟩
  intro R δ hδ hδR
  have hδp : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
  have hRp : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hδR' : (δ : ℝ) ≤ R := by exact_mod_cast hδR
  have hs := s.property.1
  have hs1 := s.property.2
  have hsum := LocalizedField.truncated_square_power_sum_internal s δ (4 * R) hδ (by omega)
  have hroot : Real.sqrt (∑ t ∈ Icc δ (4 * R), (t : ℝ) ^ (-2 * s.val)) ≤
      B * (R : ℝ) ^ ((1 - s.val) / 2) * (δ : ℝ) ^ (-s.val / 2) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    convert hsum using 1
    simp only [B, mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1 / (1 - s.val)),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.rpow_mul_natCast hRp.le, ← Real.rpow_mul_natCast hδp.le]
    norm_num only [Nat.cast_ofNat, Nat.cast_mul]
    rw [show (1 - s.val) / 2 * 2 = 1 - s.val by ring,
      show -s.val / 2 * 2 = -s.val by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hRp.le]
    ring
  have hbase₀ := transfer_radius_power_internal hδp hδR' (-1) 0 (s.val / 2) (by positivity)
  have hbase₁ := transfer_radius_power_internal hδp hδR' (-2) 0 (1 + s.val / 2) (by positivity)
  have htail := transfer_radius_power_internal hδp hδR' (-(3 / 2 - s.val))
    (-(1 / 2 + s.val)) ((1 - s.val) / 2) (by positivity)
  simp only [Real.rpow_zero, mul_one, zero_sub,
    show (-2 : ℝ) + (1 + s.val / 2) = -1 + s.val / 2 by ring,
    show -(1 + s.val / 2) = -1 - s.val / 2 by ring] at hbase₀ hbase₁
  rw [show -(s.val / 2) = -s.val / 2 by ring] at hbase₀
  rw [show -(3 / 2 - s.val) + (1 - s.val) / 2 = -1 + s.val / 2 by ring,
    show -(1 / 2 + s.val) - (1 - s.val) / 2 = -1 - s.val / 2 by ring] at htail
  constructor
  · have hh := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ (R : ℝ) ^ (-(3 / 2 - s.val)) by positivity)
    have he : (R : ℝ) ^ (-(3 / 2 - s.val)) *
        (B * (R : ℝ) ^ ((1 - s.val) / 2) * (δ : ℝ) ^ (-s.val / 2)) =
        B * ((R : ℝ) ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2)) := by
      calc
        _ = B * ((R : ℝ) ^ (-(3 / 2 - s.val)) * (R : ℝ) ^ ((1 - s.val) / 2)) *
            (δ : ℝ) ^ (-s.val / 2) := by ring
        _ = _ := by
          rw [← Real.rpow_add hRp,
          show -(3 / 2 - s.val) + (1 - s.val) / 2 = -1 + s.val / 2 by ring]
          ring
    rw [he] at hh
    nlinarith [show 0 ≤ (R : ℝ) ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) by positivity]
  · nlinarith [mul_nonneg hB
      (show 0 ≤ (R : ℝ) ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2) by positivity)]

/-- See the proof of Proposition 5.15 in the paper: the actual parent exterior row has
both claimed boundary powers, with one loss exponent before ε and common
prefactors on each compact positive temperature interval. This theorem
estimates U only. The Schur row and multiplier are assembled separately. -/
theorem constrained_exterior_sharp_bounds (hzeta : External.PeriodicZeta)
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
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ j : Fin (m : ℕ), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
    ∃ U : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
      ∀ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
        let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
        let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
        ‖U l‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) ∧
        ∀ hl : 0 < l.val,
          let prev : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
          let δpair := min δ (min (prev.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - prev.val))
          ‖U l - U prev‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
            R ^ (-1 + s.val / 2) * (δpair : ℝ) ^ (-1 - s.val / 2) := by
  obtain ⟨κ, hκ, hbound⟩ := LocalizedField.constrained_exterior_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨P, hP, hprofile⟩ := exterior_profiles_internal s
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hbound ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C * P, by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu j hR
  obtain ⟨U, hU, hb⟩ := hbound ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu j hR
  have hn₀ : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ Riesz1.cyclicIndexDistance m j i₀ := by
    have hc := LocalizedMatrix.window_card m j i₀
    change (LocalizedMatrix.windowSize m j i₀ : ℕ) = _ at hc
    omega
  refine ⟨U, hU, ?_⟩
  intro l R δ
  have hδ : 1 ≤ δ := by dsimp only [δ]; have := l.isLt; omega
  have hδR : δ ≤ Riesz1.cyclicIndexDistance m j i₀ := by dsimp only [δ]; omega
  constructor
  · have hh := (hprofile _ δ hδ hδR).1
    have he := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ by positivity)
    exact (hb l).1.trans (by convert he using 1; ring)
  · intro hl prev δpair
    have hdp : 1 ≤ δpair := by dsimp only [δpair, δ, prev]; have := l.isLt; omega
    have hdR : δpair ≤ Riesz1.cyclicIndexDistance m j i₀ := by dsimp only [δpair]; omega
    have hh := (hprofile _ δpair hdp hdR).2
    have he := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ by positivity)
    exact ((hb l).2 hl).trans (by convert he using 1; ring)

/-- See the proof of Proposition 5.15 in the paper: normalize the actual exterior equation
by scaling its scalar form. The coefficient C precedes every positive β.
The field bound has the explicit factor β, hence is uniform on compact
temperature intervals. Conditional exterior equations remain internal. -/
theorem normalized_schur_temperature_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β →
    ∀ (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ))
      (K : ℕ) (_hK : 1 ≤ K) (_hKm : K ≤ (m : ℕ) / 4),
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    ∀ (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
      (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ),
    (∀ v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ,
      β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) →
    let field := fun l : Fin (n : ℕ) => β • LocalizedFieldPart3.referenceRow Q hQ s n m hm K
      (LocalizedFieldPart3.exteriorReindex Q hQ n m hnm w) (l.castLE hnm)
    let weight := fun i : Fin (n : ℕ) =>
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2)
    (∀ l, ‖field l‖ ≤ β * C * (K : ℝ) ^ 2 * weight l *
      ∑ i, weight i * ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖) ∧
    (∀ l k, ‖field l - field k‖ ≤ β * C * (K : ℝ) ^ 2 * (Nat.dist l.val k.val : ℝ) *
      (min (min (l.val + 1) ((n : ℕ) - l.val))
        (min (k.val + 1) ((n : ℕ) - k.val)) : ℕ) ^ (-1 - s.val / 2) *
      ∑ i, weight i * ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖) := by
  obtain ⟨C, hC, hb⟩ := LocalizedFieldPart3.normalized_schur_bounds_internal hzeta s 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hnm hm K hK hKm Ω _ ν Q hQ p w hw
  let Q' := ScalarDirichletScaling.scale β⁻¹ Q
  have hQ' : IsClosedScalarDirichletForm Q' :=
    ScalarDirichletScaling.isClosed_scale β⁻¹ (inv_pos.mpr hβ) Q hQ
  have hw' : ∀ v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q' hQ',
      (1 : ℝ)⁻¹ * (∑ i, Q'.2 (MatrixEnergy.vectorEquiv Q' hQ' w i) (MatrixEnergy.vectorEquiv Q' hQ' v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q' hQ' (SchurRestriction.assemble Q' hQ' n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q' hQ' (SchurRestriction.assemble Q' hQ' n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q' hQ' (SchurRestriction.assemble Q' hQ' n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q' hQ' (SchurRestriction.assemble Q' hQ' n m hnm (0, v)) i).val) x ∂ν := by
    intro v
    change (1 : ℝ)⁻¹ * (∑ i, β⁻¹ * Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν
    rw [inv_one, one_mul, ← mul_sum]
    exact hw v
  have hb' := hb n m hnm hm K hK hKm ν Q' hQ' p w hw'
  dsimp only at hb' ⊢
  simp only [one_smul] at hb'
  have hrow (i : Fin (m : ℕ)) :
      LocalizedFieldPart3.referenceRow Q' hQ' s n m hm K
        (LocalizedFieldPart3.exteriorReindex Q' hQ' n m hnm w) i =
      LocalizedFieldPart3.referenceRow Q hQ s n m hm K
        (LocalizedFieldPart3.exteriorReindex Q hQ n m hnm w) i := by rfl
  have hval (i : Fin (n : ℕ)) : (MatrixEnergy.vectorEquiv Q' hQ' p i).val =
      (MatrixEnergy.vectorEquiv Q hQ p i).val := rfl
  simp_rw [hrow, hval] at hb'
  constructor
  · intro l
    rw [norm_smul, Real.norm_of_nonneg hβ.le]
    have hh := mul_le_mul_of_nonneg_left (hb'.1 l) hβ.le
    convert hh using 1
    ring
  · intro l k
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hβ.le]
    have hh := mul_le_mul_of_nonneg_left (hb'.2 l k) hβ.le
    convert hh using 1
    ring

/-- See Subsection 5.5 of the paper: the adjoint extension is exactly zero
extension of the active L² components, on every component label. -/
theorem extendSource_apply_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (f : Fin (n : ℕ) → Lp ℝ 2 ν) (i : Fin (m : ℕ)) :
    (SchurRestriction.extendSource n m hnm (WithLp.toLp 2 f)) i =
      if hi : i.val < (n : ℕ) then f ⟨i.val, hi⟩ else 0 := by
  let G : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν) :=
    WithLp.toLp 2 (fun j => if hj : j.val < (n : ℕ) then f ⟨j.val, hj⟩ else 0)
  have he : SchurRestriction.extendSource n m hnm (WithLp.toLp 2 f) = G := by
    apply ext_inner_right ℝ
    intro v
    rw [SchurRestriction.extendSource, ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
    change (∑ j : Fin (n : ℕ), inner ℝ (f j) (v (j.castLE hnm))) =
      ∑ j : Fin (m : ℕ), inner ℝ (G j) (v j)
    rw [LocalizedBoundary.sum_active_internal n m hnm (fun j => inner ℝ (G j) (v j))
      (fun j hj => by simp only [G, dite_eq_right (by omega : ¬j.val < (n : ℕ)), inner_zero_left])]
    apply sum_congr rfl
    intro j _
    have hj : (j.castLE hnm).val < (n : ℕ) := j.isLt
    simp only [G, dite_eq_left hj]
    rfl
  rw [he]

/-- See the proof of Proposition 5.15 in the paper: apply the sharp modulus to the
existing embedded field construction, retaining the ordered neighboring
increments before zero extension. This is an internal assembly interface. -/
theorem extended_field_modulus_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (R A : ℝ) (hR : 0 < R) (hnR : (n : ℝ) ≤ R) (hA : 0 ≤ A)
    (v : Fin (n : ℕ) → Lp ℝ 2 ν)
    (hval : ∀ i, ‖v i‖ ≤ A * R ^ (-1 + s.val / 2) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2))
    (hinc : ∀ i : Fin (n : ℕ), ∀ hi : 0 < i.val,
      let prev : Fin (n : ℕ) := ⟨i.val - 1, by have := i.isLt; omega⟩
      ‖v i - v prev‖ ≤ A * R ^ (-1 + s.val / 2) *
        ((min (min (i.val + 1) ((n : ℕ) - i.val))
          (min (prev.val + 1) ((n : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2)) :
    let f := (SchurRestriction.extendSource n m hnm (WithLp.toLp 2 v)).ofLp
    let C := 8 / (1 - s.val / 2) + 4 + 2 / (s.val / 2)
    (∑ i, ‖f i‖) ≤ C * A ∧
      ∀ h, (∑ i, ‖f (i - h) - f i‖) ≤
        C * A * min 1 (((Riesz1.cyclicIndexDistance m h 0 : ℝ) / R) ^ (1 - s.val / 2)) := by
  intro f C
  apply sharp_translation_internal s n m hnm R A hR hnR hA f
  · intro i hi
    exact (extendSource_apply_internal n m hnm v i).trans (dite_eq_right (by omega))
  · intro i
    have he := extendSource_apply_internal n m hnm v (i.castLE hnm)
    have hj : (i.castLE hnm).val < (n : ℕ) := i.isLt
    change ‖(SchurRestriction.extendSource n m hnm (WithLp.toLp 2 v)) (i.castLE hnm)‖ ≤ _
    rw [he, dite_eq_left hj]
    exact hval i
  · intro i hi hin
    let j : Fin (n : ℕ) := ⟨i.val, hin⟩
    let prev : Fin (n : ℕ) := ⟨i.val - 1, by omega⟩
    have hiz : i ≠ 0 := by intro hz; subst i; simp at hi
    have hp : (i - 1).val = i.val - 1 := Fin.val_sub_one_of_ne_zero hiz
    have he := extendSource_apply_internal n m hnm v i
    have hep := extendSource_apply_internal n m hnm v (i - 1)
    have hip : (i - 1).val < (n : ℕ) := by omega
    change ‖(SchurRestriction.extendSource n m hnm (WithLp.toLp 2 v)) i -
      (SchurRestriction.extendSource n m hnm (WithLp.toLp 2 v)) (i - 1)‖ ≤ _
    rw [he, hep, dite_eq_left hin, dite_eq_left hip]
    have hprev : (⟨(i - 1).val, hip⟩ : Fin (n : ℕ)) = prev := Fin.ext hp
    rw [hprev]
    have hh := hinc j hi
    have hd : min (min (j.val + 1) ((n : ℕ) - j.val))
        (min (prev.val + 1) ((n : ℕ) - prev.val)) = min i.val ((n : ℕ) - i.val) := by
      dsimp only [j, prev]
      omega
    simpa only [hd, j, prev] using hh

/-- See Subsection 5.5 of the paper: the normalized exterior equation has one and
only one form solution, including an empty exterior. This constructs the
actual inverse used by the field, from the coercive resolvent. -/
theorem normalized_schur_exists_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : ℝ) (hβ : 0 < β)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKm : K ≤ (m : ℕ) / 4)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    ∃! w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ, ∀ v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ,
      β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν := by
  obtain ⟨_, _, hb⟩ := BoundarySchurBounds.bilinear_schur_cutoff hzeta s β hβ
  obtain ⟨R, hR, huniq, _⟩ := hb m hm K hK hKm (n : ℕ) hnm ν Q hQ
  let E := univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)
  let e := LocalizedFieldPart3.exteriorReindex Q hQ n m hnm
  let t := ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
    (fun a : E => 2 * referenceIntervalMatrix s m hm K (i.castLE hnm) a.val)
    (MatrixEnergy.vectorEquiv Q hQ p i).val
  let w := e.symm (β • R t)
  have hD := (ExteriorForces.exteriorBlock_posDef s m hm hK hKm E).1.posSemidef.smul hβ.le
  have hw : ∀ v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ,
      β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν := by
    intro v
    have he : BoundarySchurBounds.constantForm Q hQ _ hD (e w) (e v) =
        β * inner ℝ t (OperatorSchur.vectorValues Q hQ (e v)) := by
      rw [show e w = β • R t from e.apply_symm_apply _]
      simp only [map_smul, smul_apply, smul_eq_mul]
      exact congrArg (fun r : ℝ => β * r) (hR t (e v))
    rw [LocalizedFieldPart3.exterior_form_internal,
      ← LocalizedFieldPart3.cross_pair_internal Q hQ s n m hnm hm K p v] at he
    have hh := congrArg (fun q : ℝ => β⁻¹ * q) he
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul] using hh
  refine ⟨w, hw, ?_⟩
  intro z hz
  apply e.injective
  exact (LocalizedFieldPart3.reindexed_resolvent_internal Q hQ s n m hnm hm K β hβ hD R huniq p z hz).trans
    (LocalizedFieldPart3.reindexed_resolvent_internal Q hQ s n m hnm hm K β hβ hD R huniq p w hw).symm

/-- See the proof of Proposition 5.15 in the paper: sum over the ordered window equals
sum over its actual parent labels. -/
theorem sum_window_embedding_internal {W : Type*} [AddCommMonoid W]
    (m : ℕ+) (j i₀ : Fin (m : ℕ)) (f : Fin (m : ℕ) → W) :
    (∑ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
      f (LocalizedMatrix.windowEmbedding m j i₀ l)) = ∑ i ∈ LocalizedMatrix.window m j i₀, f i := by
  apply sum_bij (fun l _ => LocalizedMatrix.windowEmbedding m j i₀ l)
  · intro l _
    exact (LocalizedMatrix.mem_window_iff_exists_embedding m j i₀ _).mpr ⟨l, rfl⟩
  · intro l _ k _ h
    have hn : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
      change (LocalizedMatrix.window m j i₀).card ≤ (m : ℕ)
      simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ (LocalizedMatrix.window m j i₀))
    rw [LocalizedMatrix.windowEmbedding_apply m j i₀ l hn,
      LocalizedMatrix.windowEmbedding_apply m j i₀ k hn] at h
    have hc : l.castLE hn = k.castLE hn := add_left_cancel h
    exact Fin.castLE_injective hn hc
  · intro i hi
    obtain ⟨l, hl⟩ := (LocalizedMatrix.mem_window_iff_exists_embedding m j i₀ i).mp hi
    exact ⟨l, mem_univ _, hl⟩
  · intro l _
    rfl

/-- See the proof of Proposition 5.15: the actual
weighted window source obeys the sharp separation power. -/
theorem window_schur_source_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀) (v : Fin (m : ℕ) → Lp ℝ 2 ν) :
    let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
    let n₀ := LocalizedMatrix.windowSize m j i₀
    (∑ i : Fin (n₀ : ℕ), ((min (i.val + 1) ((n₀ : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      ‖v (LocalizedMatrix.windowEmbedding m j i₀ i)‖) ≤
      (Real.sqrt (2 / (1 - s.val)) * 2 ^ (3 / 2 - s.val)) * R ^ (-1 + s.val / 2) *
        Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖v i‖) ^ 2) := by
  intro R n₀
  let a := 3 / 2 - s.val
  let c := (1 - s.val) / 2
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hc : 0 ≤ c := by dsimp only [c]; linarith [s.property.2]
  have hnR : (n₀ : ℝ) ≤ R := by
    have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.1
    change (n₀ : ℝ) ≤ R / 2 at this
    linarith
  have hs := LocalizedField.schur_source_weight_internal s n₀
    (fun i => v (LocalizedMatrix.windowEmbedding m j i₀ i))
  rw [sum_window_embedding_internal m j i₀ (fun i => ‖v i‖ ^ 2)] at hs
  have hw := LocalizedBoundary.window_norm_internal m j i₀ (by omega) a
    (by dsimp only [a]; linarith [s.property.2]) v
  have hwin : Real.sqrt (∑ i ∈ LocalizedMatrix.window m j i₀, ‖v i‖ ^ 2) ≤
      2 ^ a * Real.sqrt (∑ i, (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2) / R ^ a := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hRp a)).mpr
    simpa only [mul_comm] using hw
  have hn := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ n₀) hnR hc
  calc
    _ ≤ Real.sqrt (2 / (1 - s.val)) * (n₀ : ℝ) ^ c *
        Real.sqrt (∑ i ∈ LocalizedMatrix.window m j i₀, ‖v i‖ ^ 2) := hs
    _ ≤ Real.sqrt (2 / (1 - s.val)) * R ^ c *
        (2 ^ a * Real.sqrt (∑ i, (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2) / R ^ a) := by gcongr
    _ = _ := by
      have he : R ^ c / R ^ a = R ^ (-1 + s.val / 2) := by
        rw [← Real.rpow_sub hRp]
        congr 1
        dsimp only [a, c]
        ring
      calc
        _ = (Real.sqrt (2 / (1 - s.val)) * 2 ^ a) * (R ^ c / R ^ a) *
            Real.sqrt (∑ i, (weightRadius m i i₀ ^ a * ‖v i‖) ^ 2) := by ring
        _ = _ := by rw [he]

/-- See the proof of Proposition 5.15 in the paper: triangle inequality for its three sources. -/
theorem three_sources_norm_internal {V : Type*} [NormedAddCommGroup V]
    (p q r : V) (T : ℝ) (hp : ‖p‖ ≤ T) (hq : ‖q‖ ≤ T) (hr : ‖r‖ ≤ T) :
    ‖p - q + r‖ ≤ 3 * T := by
  calc
    _ ≤ (‖p‖ + ‖q‖) + ‖r‖ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (T + T) + T := add_le_add (add_le_add hp hq) hr
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: triangle inequality after the
constant multiplier cancels in an increment. -/
theorem two_sources_norm_internal {V : Type*} [NormedAddCommGroup V]
    (p q : V) (T : ℝ) (hT : 0 ≤ T) (hp : ‖p‖ ≤ T) (hq : ‖q‖ ≤ T) :
    ‖p - q‖ ≤ 3 * T := by
  calc
    _ ≤ ‖p‖ + ‖q‖ := norm_sub_le _ _
    _ ≤ T + T := add_le_add hp hq
    _ ≤ _ := by linarith only [hT]

/-- See the proof of Proposition 5.15 in the paper: internal assembly of three actual
L² sources after their separate estimates. The multiplier cancels in
increments, and the existing zero extension supplies the sharp modulus. -/
theorem field_profile_assembly_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (n₀ m₀ : ℕ+) (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ))
    (R A P T β : ℝ) (hRp : 0 < R) (hnR : (n₀ : ℝ) ≤ R)
    (hA : 0 ≤ A) (hβ : 0 < β) (hP : β * P ≤ A)
    (hT : T ≤ A * R ^ (-1 + s.val / 2))
    (U W : Fin (n₀ : ℕ) → Lp ℝ 2 ν) (lam : Lp ℝ 2 ν)
    (hU : ∀ l : Fin (n₀ : ℕ),
      ‖U l‖ ≤ P * R ^ (-1 + s.val / 2) *
        ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2) ∧
      ∀ hl : 0 < l.val,
        let prev : Fin (n₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
        ‖U l - U prev‖ ≤ P * R ^ (-1 + s.val / 2) *
          ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
            (min (prev.val + 1) ((n₀ : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2))
    (hW : ∀ l, ‖W l‖ ≤ T * ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2))
    (hWi : ∀ l k, ‖W l - W k‖ ≤ T * (Nat.dist l.val k.val : ℝ) *
      ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
        (min (k.val + 1) ((n₀ : ℕ) - k.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2))
    (hlamProfile : ∀ δ : ℕ, 1 ≤ δ → (δ : ℝ) ≤ R →
      ‖lam‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2)) :
    let V := fun l => (-β) • U l - W l + lam
    (∀ l, ‖V l‖ ≤ (3 * A) * R ^ (-1 + s.val / 2) *
      ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
    (∀ l : Fin (n₀ : ℕ), ∀ hl : 0 < l.val,
      let prev : Fin (n₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
      ‖V l - V prev‖ ≤ (3 * A) * R ^ (-1 + s.val / 2) *
        ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
          (min (prev.val + 1) ((n₀ : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2)) ∧
    (let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
     let Ct := 8 / (1 - s.val / 2) + 4 + 2 / (s.val / 2)
     (∑ i, ‖f i‖) ≤ Ct * (3 * A) ∧
     ∀ h, (∑ i, ‖f (i-h) - f i‖) ≤ Ct * (3 * A) *
       min 1 (((Riesz1.cyclicIndexDistance m₀ h 0 : ℝ) / R) ^ (1 - s.val / 2))) := by
  intro V
  have hentry (l : Fin (n₀ : ℕ)) : ‖V l‖ ≤ (3 * A) * R ^ (-1 + s.val / 2) *
      ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2) := by
    let δ := min (l.val + 1) ((n₀ : ℕ) - l.val)
    have hδ : 1 ≤ δ := by dsimp only [δ]; have := l.isLt; omega
    have hdR : (δ : ℝ) ≤ R := (show (δ : ℝ) ≤ (n₀ : ℝ) by exact_mod_cast (show δ ≤ (n₀ : ℕ) by dsimp only [δ]; omega)).trans hnR
    have hp : ‖(-β) • U l‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
      calc
        _ ≤ β * (P * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2)) :=
          mul_le_mul_of_nonneg_left (hU l).1 hβ.le
        _ ≤ _ := by convert mul_le_mul_of_nonneg_right hP (show 0 ≤ R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) by positivity) using 1 <;> ring
    have hs : ‖W l‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) := by
      exact (hW l).trans (mul_le_mul_of_nonneg_right hT (by positivity))
    have hl := hlamProfile δ hδ hdR
    have ht := three_sources_norm_internal ((-β) • U l) (W l) lam _ hp hs hl
    convert ht using 1
    ring
  have hincrement (l : Fin (n₀ : ℕ)) (hl : 0 < l.val) :
      let prev : Fin (n₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
      ‖V l - V prev‖ ≤ (3 * A) * R ^ (-1 + s.val / 2) *
        ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
          (min (prev.val + 1) ((n₀ : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2) := by
    intro prev
    let δ := min (min (l.val + 1) ((n₀ : ℕ) - l.val))
      (min (prev.val + 1) ((n₀ : ℕ) - prev.val))
    have hdist : Nat.dist l.val prev.val = 1 := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (show prev.val ≤ l.val by dsimp only [prev]; omega)]
      dsimp only [prev]
      omega
    have hp : ‖(-β) • (U l - U prev)‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2) := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
      calc
        _ ≤ β * (P * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2)) :=
          mul_le_mul_of_nonneg_left ((hU l).2 hl) hβ.le
        _ ≤ _ := by convert mul_le_mul_of_nonneg_right hP (show 0 ≤ R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2) by positivity) using 1 <;> ring
    have hs : ‖W l - W prev‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2) := by
      have hh := hWi l prev
      rw [hdist, Nat.cast_one, mul_one] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hT (by positivity))
    have he : V l - V prev = (-β) • (U l - U prev) - (W l - W prev) := by dsimp only [V]; rw [smul_sub]; abel
    rw [he]
    have hnprof : 0 ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-1 - s.val / 2) := by positivity
    have ht := two_sources_norm_internal ((-β) • (U l - U prev)) (W l - W prev) _ hnprof hp hs
    convert ht using 1
    ring
  exact ⟨hentry, hincrement, extended_field_modulus_internal s n₀ m₀ hn₀ R
    (3 * A) hRp hnR (by positivity) V hentry hincrement⟩

/-- See the proof of Proposition 5.15 in the paper, all four conclusions. The field is
specified by its actual parent exterior row, the unique normalized exterior
form solution and the canonical multiplier. Its full-cycle values are the
adjoint zero extension. Loss and separation exponents precede ε and
all prefactors. The latter are uniform on compact positive β intervals. -/
theorem loc_field (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ (j : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]
      omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := n₀.pos
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀] at *
      omega
    let pv := (MatrixEnergy.vectorEquiv Q hQ).symm (fun i => u (LocalizedMatrix.windowEmbedding m j i₀ i))
    let J := SchurRestriction.assemble Q hQ n₀ m₀ hn₀
    let H := fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
    ∃ U : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
    ∃ w : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
      (∀ v : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
        β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
          (∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,w)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,v)) i).val) x ∂ν) =
          ∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (pv,0)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,v)) i).val) x ∂ν) ∧
    ∃ V : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, V l = (-β) • U l - β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀) + lam) ∧
      (∀ l, ‖V l‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-1 + s.val / 2) *
        ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
      (∀ l : Fin (n₀ : ℕ), ∀ hl : 0 < l.val,
        let prev : Fin (n₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
        ‖V l - V prev‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-1 + s.val / 2) *
          ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
            (min (prev.val + 1) ((n₀ : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2)) ∧
      (let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
       (∑ i, ‖f i‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
       ∀ h, (∑ i, ‖f (i - h) - f i‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
         min 1 (((Riesz1.cyclicIndexDistance m₀ h 0 : ℝ) /
           (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (1 - s.val / 2))) := by
  obtain ⟨κu, hκu, hu⟩ := constrained_exterior_sharp_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κg, hκg, hg⟩ := GlobalDecay.global_decay_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨B, hB, hschur⟩ := normalized_schur_temperature_internal hzeta s
  let κ : ℝ := κu + κg + 2 * (M₀ : ℕ)
  let D : ℝ := 8 * ((M₀ : ℕ) + γstar + 1) + 8 * (M₀ : ℕ)
  let Cs : ℝ := Real.sqrt (2 / (1 - s.val)) * 2 ^ (3 / 2 - s.val)
  let Ct : ℝ := 8 / (1 - s.val / 2) + 4 + 2 / (s.val / 2)
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  have hhalf : 0 < 1 - s.val / 2 := by linarith [s.property.2]
  have hsmall : 0 < s.val / 2 := by linarith [s.property.1]
  have hCt : 1 ≤ Ct := by
    dsimp only [Ct]
    have h1 : 0 ≤ 8 / (1 - s.val / 2) := by positivity [s.property.2]
    have h2 : 0 ≤ 2 / (s.val / 2) := by positivity [s.property.1]
    linarith
  refine ⟨κ, D, by dsimp only [κ]; positivity, by dsimp only [D]; positivity, ?_⟩
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cu, hCu, hu⟩ := hu ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cg, hCg, hg⟩ := hg ε hε Cstar hCstar βlo hβlo βhi hβhi
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  let C₀ := 1 + βhi * Cu + βhi * B * Cs * Cg + Cg
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨3 * Ct * C₀, by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu χ i₀ u husol j hR hsep
    n₀ m₀ hn₀ hm₀ pv J H
  have hβ : 0 < β := hβlo.trans_le hβl
  let R : ℝ := Riesz1.cyclicIndexDistance m j i₀
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hnp : (0 : ℝ) < n := by positivity
  have hcutsep : (n : ℝ) ^ ((8 * (M₀ : ℕ)) * ε) ≤ R :=
    (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith [show (0 : ℝ) ≤ (M₀ : ℕ) by positivity]) hε.le)).trans hsep
  obtain ⟨_, hKlocal⟩ := LocalizedMatrix.window_reference_cutoff_admissible s n m ε hε M₀ j i₀ hR hcutsep
  have hKml : K ≤ (m₀ : ℕ) / 4 := by change 4 * K ≤ (m₀ : ℕ) at hKlocal; omega
  obtain ⟨lam, hlam, _, henergy, hlamBound, _⟩ := hg ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u husol
  obtain ⟨U, hU, hUb⟩ := hu ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u husol j hR
  obtain ⟨w, hw, _⟩ := normalized_schur_exists_internal hzeta s β hβ n₀ m₀ hn₀ hm₀ K hK hKml ν Q hQ pv
  obtain ⟨hSp, hSi⟩ := hschur β hβ n₀ m₀ hn₀ hm₀ K hK hKml ν Q hQ pv w hw
  let S := ∑ i : Fin (n₀ : ℕ), ((min (i.val + 1) ((n₀ : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
    ‖(u (LocalizedMatrix.windowEmbedding m j i₀ i)).val‖
  let E := Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2)
  have hE : E ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans henergy
  have hS : S ≤ Cs * R ^ (-1 + s.val / 2) * E :=
    window_schur_source_internal s m j i₀ hR (fun i => (u i).val)
  have hpv (i : Fin (n₀ : ℕ)) : (MatrixEnergy.vectorEquiv Q hQ pv i).val =
      (u (LocalizedMatrix.windowEmbedding m j i₀ i)).val := by
    exact congrArg (fun f : Fin (n₀ : ℕ) → Q.1 => (f i).val)
      ((MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply _)
  simp_rw [hpv] at hSp hSi
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  let A := C₀ * (n : ℝ) ^ (κ * ε) * ‖χ‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcoeff (c k : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C₀) (hk : k ≤ κ) :
      c * (n : ℝ) ^ (k * ε) * ‖χ‖ ≤ A :=
    mul_le_mul_of_nonneg_right
      (LocalizedMatrix.loss_mono_internal hn1 hε.le hc hcC hk) (norm_nonneg _)
  have hpu : β * (Cu * (n : ℝ) ^ (κu * ε) * ‖χ‖) ≤ A := by
    calc
      _ ≤ (βhi * Cu) * (n : ℝ) ^ (κu * ε) * ‖χ‖  := by
        calc
          _ ≤ βhi * (Cu * (n : ℝ) ^ (κu * ε) * ‖χ‖) :=
            mul_le_mul_of_nonneg_right hβu (by positivity)
          _ = _ := by ring
      _ ≤ _ := hcoeff _ _ (by positivity) (by dsimp only [C₀]; linarith [mul_nonneg (mul_nonneg (mul_nonneg hβhi0.le hB.le) hCs) hCg.le])
        (by dsimp only [κ]; linarith [show (0 : ℝ) ≤ 2 * (M₀ : ℕ) by positivity])
  have hpl : Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ ≤ A :=
    hcoeff _ _ hCg.le (by dsimp only [C₀]; linarith [mul_nonneg hβhi0.le hCu.le, mul_nonneg (mul_nonneg (mul_nonneg hβhi0.le hB.le) hCs) hCg.le])
      (by dsimp only [κ]; linarith [show (0 : ℝ) ≤ 2 * (M₀ : ℕ) by positivity])
  have hps : β * B * (K : ℝ) ^ 2 * S ≤ A * R ^ (-1 + s.val / 2) := by
    have hS' := hS.trans (mul_le_mul_of_nonneg_left hE (show 0 ≤ Cs * R ^ (-1 + s.val / 2) by positivity))
    have hks := BoundarySchurBounds.cutoff_sq_le (n : ℕ) (M₀ : ℕ) (by omega) ε
    calc
      _ ≤ βhi * B * (n : ℝ) ^ ((2 * (M₀ : ℕ) : ℝ) * ε) *
          (Cs * R ^ (-1 + s.val / 2) * (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖)) := by
            gcongr
      _ = (βhi * B * Cs * Cg) * (n : ℝ) ^ ((κg + 2 * (M₀ : ℕ)) * ε) * ‖χ‖ * R ^ (-1 + s.val / 2) := by
        rw [show (κg + 2 * (M₀ : ℕ)) * ε = (2 * (M₀ : ℕ)) * ε + κg * ε by ring, Real.rpow_add hnp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcoeff _ _ (by positivity) (by dsimp only [C₀]; linarith [mul_nonneg hβhi0.le hCu.le])
          (by dsimp only [κ]; linarith)) (by positivity)
  let W := fun l : Fin (n₀ : ℕ) => β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
    (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀)
  let V := fun l => (-β) • U l - W l + lam
  have hwsize := LocalizedMatrix.window_size_bounds m j i₀ hR
  have hnR : (n₀ : ℝ) ≤ R := by
    have hnr := hwsize.2.2.1
    change (n₀ : ℝ) ≤ R / 2 at hnr
    linarith
  have hRml : R ≤ (m : ℝ) := by
    have hd : Riesz1.cyclicIndexDistance m j i₀ ≤ (m : ℕ) := by
      simp only [Riesz1.cyclicIndexDistance]
      omega
    dsimp only [R]
    exact_mod_cast hd
  have hlambda (δ : ℕ) (hd : 1 ≤ δ) (hdR : (δ : ℝ) ≤ R) :
      ‖lam‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) := by
    have hdp : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
    have hbase := transfer_radius_power_internal hdp hdR (-1) 0 (s.val / 2) (by positivity [s.property.1])
    simp only [Real.rpow_zero, mul_one, zero_sub] at hbase
    rw [show -(s.val / 2) = -s.val / 2 by ring] at hbase
    have hinv : (m : ℝ)⁻¹ ≤ R ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; exact inv_anti₀ hRp hRml
    calc
      _ ≤ (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) * (m : ℝ)⁻¹ := by convert hlamBound using 1; ring
      _ ≤ A * (R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2)) :=
        mul_le_mul hpl (hinv.trans hbase) (by positivity) hA
      _ = _ := by ring
  have hW (l : Fin (n₀ : ℕ)) : ‖W l‖ ≤ (β * B * (K : ℝ) ^ 2 * S) *
      ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2) := by
    convert hSp l using 1
    ring
  have hWi (l k : Fin (n₀ : ℕ)) : ‖W l - W k‖ ≤ (β * B * (K : ℝ) ^ 2 * S) *
      (Nat.dist l.val k.val : ℝ) *
      ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
        (min (k.val + 1) ((n₀ : ℕ) - k.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2) := by
    convert hSi l k using 1
    ring
  obtain ⟨hentry, hincrement, hmod⟩ := field_profile_assembly_internal s n₀ m₀ hn₀ R A
    (Cu * (n : ℝ) ^ (κu * ε) * ‖χ‖) (β * B * (K : ℝ) ^ 2 * S) β
    hRp hnR hA hβ hpu hps U W lam hUb hW hWi hlambda
  have hbig : 3 * A ≤ (3 * Ct * C₀) * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
    have hh := mul_le_mul_of_nonneg_right hCt (show 0 ≤ 3 * A by positivity)
    convert hh using 1 <;> dsimp only [A] <;> ring
  refine ⟨lam, hlam, U, hU, w, hw, V, fun _ => rfl, ?_, ?_, ?_⟩
  · intro l
    exact (hentry l).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbig (by positivity)) (by positivity))
  · intro l hl
    exact (hincrement l hl).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbig (by positivity)) (by positivity))
  · constructor
    · convert hmod.1 using 1; dsimp only [Ct, A, R]; ring
    · intro h
      convert hmod.2 h using 1; dsimp only [Ct, A, R]; ring

end Riesz2.LocalizedFieldPart4
