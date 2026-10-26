/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationCoefficients
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart9
public import Riesz2.Preliminaries.TruncatedCoercivity

/-!
# Complementary distances for interpolation coefficients

Quantitative geometry for Subsection 6.1. The large-size threshold depends on the
exponent and tolerance alone. All coefficients below are the existing physical image
coefficients.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationCoefficients

/-- See Subsection 6.1 of the paper: a threshold independent of temperature
and both physical volumes makes the geometric error small. -/
theorem complement_threshold (σ ε : ℝ) (hσε : σ + 2 * ε < 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (128 : ℝ) ≤ (n : ℝ) ^ (1 - σ - 2 * ε) := by
  let a := 1 - σ - 2 * ε
  have ha : 0 < a := by dsimp only [a]; linarith
  obtain ⟨k, hk⟩ := exists_nat_ge ((128 : ℝ) ^ (1 / a))
  refine ⟨max 2 k, le_max_left _ _, fun n hn => ?_⟩
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (le_max_right 2 k).trans hn
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 128) _)
    (hk.trans hkn) ha.le
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 128), one_div_mul_cancel ha.ne',
    Real.rpow_one] at hh
  exact hh

/-- Internal numerical step of Subsection 6.1. The explicit
constant `9/128` leaves room for the active mass and half-period rank. -/
theorem complement_error_internal {σ ε n N : ℝ}
    (hn : 1 ≤ n) (hnN : n ≤ N) (hε : 0 ≤ ε)
    (hγ : σ + ε ≤ 1) (hsize : 128 ≤ n ^ (1 - σ - 2 * ε)) :
    n ^ (σ + ε) + 8 * n ^ ε * N ^ (σ + ε) ≤ (9 / 128) * N := by
  have hn0 : 0 < n := by linarith
  have hN0 : 0 < N := hn0.trans_le hnN
  let t := n ^ (σ + 2 * ε - 1)
  have ht : t ≤ (1 : ℝ) / 128 := by
    have hpow : n ^ (1 - σ - 2 * ε) * t = 1 := by
      dsimp only [t]
      rw [← Real.rpow_add hn0]
      rw [show 1 - σ - 2 * ε + (σ + 2 * ε - 1) = 0 by ring, Real.rpow_zero]
    have ht0 : 0 ≤ t := Real.rpow_nonneg hn0.le _
    nlinarith [mul_le_mul_of_nonneg_right hsize ht0]
  have hN : N ^ (σ + ε) ≤ N * n ^ (σ + ε - 1) := by
    have hh := Real.rpow_le_rpow_of_nonpos hn0 hnN (by linarith : σ + ε - 1 ≤ 0)
    have he : N * N ^ (σ + ε - 1) = N ^ (σ + ε) := by
      conv_lhs => lhs; rw [← Real.rpow_one N]
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_left hh hN0.le
  have hsmall : n ^ (σ + ε) ≤ N * t := by
    have he : n * n ^ (σ + ε - 1) = n ^ (σ + ε) := by
      conv_lhs => lhs; rw [← Real.rpow_one n]
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc
      _ = n * n ^ (σ + ε - 1) := he.symm
      _ ≤ N * n ^ (σ + ε - 1) := mul_le_mul_of_nonneg_right hnN (by positivity)
      _ ≤ N * t := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) hN0.le
  have hlarge : n ^ ε * N ^ (σ + ε) ≤ N * t := by
    calc
      _ ≤ n ^ ε * (N * n ^ (σ + ε - 1)) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = N * t := by
        rw [mul_left_comm, ← Real.rpow_add hn0]
        dsimp only [t]
        rw [show ε + (σ + ε - 1) = σ + 2 * ε - 1 by ring]
  nlinarith [mul_le_mul_of_nonneg_left ht hN0.le]

/-- Internal complement estimate of Subsection 6.1, once
the interval has been split into active gaps and its two exterior pieces. -/
theorem complement_lower_internal {σ ε n N L r ℓ : ℝ}
    (hn : 1 ≤ n) (hN : 4 * n ≤ N) (hε : 0 ≤ ε)
    (hγ : σ + ε ≤ 1) (hsize : 128 ≤ n ^ (1 - σ - 2 * ε))
    (hL : L ≤ n + n ^ (σ + ε)) (hr : r ≤ N / 2)
    (hℓ : ℓ ≤ L + r + 8 * n ^ ε * N ^ (σ + ε)) :
    N / 8 ≤ N - ℓ := by
  have hnn : n ≤ N := by linarith
  have hh := complement_error_internal hn hnn hε hγ hsize
  linarith

/-- A nonwrapping interval is the corresponding filter of the finite
physical labels. This identity also handles an empty exterior piece. -/
theorem cyclicGapSum_filter (N : ℕ+) (a r : ℕ) (ha : a < (N : ℕ))
    (har : a + r ≤ (N : ℕ)) (x : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N ⟨a, ha⟩ r x =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => a ≤ j.val ∧ j.val < a + r), x j := by
  rw [InterpolantLocalLaws.cyclicGapSum_nonwrapping N _ r har]
  apply Finset.sum_bij (fun i _ => (⟨a + i.val, by have := i.isLt; omega⟩ : Fin (N : ℕ)))
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := i.isLt; dsimp; omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp at this
    omega
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val - a, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp
    omega
  · intro i _
    rfl

/-- See Subsection 6.1 of the paper: every short cyclic interval meeting the
active block is covered by the active block and at most two exterior pieces, whose total rank is no larger than the interval rank. -/
theorem crossing_interval_cover (N : ℕ+) (n : ℕ) (hn : n < (N : ℕ))
    (i : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ))
    (hmeet : ∃ j ∈ cyclicIndexInterval N i r, j.val < n) :
    ∃ p q : ℕ, p ≤ (N : ℕ) - n ∧ q ≤ (N : ℕ) - n ∧ p + q ≤ r ∧
      ∀ j ∈ cyclicIndexInterval N i r,
        j.val < n ∨ (n ≤ j.val ∧ j.val < n + p) ∨ (N : ℕ) - q ≤ j.val := by
  have hi := i.isLt
  have hm (j : Fin (N : ℕ)) (hj : j ∈ cyclicIndexInterval N i r) :
      (if i.val ≤ j.val then j.val - i.val else j.val + (N : ℕ) - i.val) < r := by
    rw [mem_cyclicIndexInterval_iff N i j hr, Fin.val_sub] at hj
    by_cases hij : i.val ≤ j.val
    · rw [ite_eq_left hij]
      rwa [show (N : ℕ) - i.val + j.val = (j.val - i.val) + (N : ℕ) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by have := j.isLt; omega)] at hj
    · rw [ite_eq_right hij]
      rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)] at hj
      omega
  by_cases hw : (N : ℕ) < i.val + r
  · refine ⟨i.val + r - (N : ℕ) - n, (N : ℕ) - max n i.val,
      by omega, by omega, by omega, ?_⟩
    intro j hj
    have hh := hm j hj
    have hjN := j.isLt
    by_cases hja : j.val < n
    · exact Or.inl hja
    · right
      by_cases hij : i.val ≤ j.val
      · right; omega
      · left
        rw [ite_eq_right hij] at hh
        omega
  · obtain ⟨j, hj, hjn⟩ := hmeet
    have hh := hm j hj
    have hjN := j.isLt
    have hin : i.val < n := by split_ifs at hh <;> omega
    refine ⟨i.val + r - n, 0, by omega, by omega, by omega, ?_⟩
    intro k hk
    have hhk := hm k hk
    have hkN := k.isLt
    by_cases hka : k.val < n
    · exact Or.inl hka
    · right; left
      split_ifs at hhk <;> omega

/-- Internal geometric estimate for Subsection 6.1: exterior prefix and suffix
rank estimates control every interval meeting the active block.
The error uses the total physical period, and the rank term occurs once. -/
theorem crossing_interval_mass_le_internal (N : ℕ+) (n : ℕ)
    (hn : n < (N : ℕ)) (x : Fin (N : ℕ) → ℝ) (hx : ∀ j, 0 ≤ x j)
    (A γ : ℝ)
    (hR : ∀ p : ℕ, p ≤ (N : ℕ) - n →
      (∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val ∧ j.val < n + p), x j) ≤
        (p : ℝ) + 4 * A * (N : ℝ) ^ γ)
    (hL : ∀ q : ℕ, q ≤ (N : ℕ) - n →
      (∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => (N : ℕ) - q ≤ j.val), x j) ≤
        (q : ℝ) + 4 * A * (N : ℝ) ^ γ)
    (i : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ))
    (hmeet : ∃ j ∈ cyclicIndexInterval N i r, j.val < n) :
    cyclicGapSum N i r x ≤ cyclicGapSum N 0 n x + r + 8 * A * (N : ℝ) ^ γ := by
  obtain ⟨p, q, hp, hq, hpq, hcover⟩ := crossing_interval_cover N n hn i r hr hmeet
  have hsum : cyclicGapSum N i r x ≤ cyclicGapSum N 0 n x +
      (∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val ∧ j.val < n + p), x j) +
      ∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => (N : ℕ) - q ≤ j.val), x j := by
    have hz : (⟨0, N.pos⟩ : Fin (N : ℕ)) = 0 := by apply Fin.ext; simp
    have hf := cyclicGapSum_filter N 0 n N.pos (by omega) x
    rw [hz] at hf
    rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N i hr, hf]
    simp only [zero_add, Nat.zero_le, true_and, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply (Finset.sum_le_sum (fun j hj => ?_)).trans
      (Finset.sum_le_univ_sum_of_nonneg (fun j => ?_))
    · rcases hcover j hj with h | h | h
      · simp only [h, ↓reduceIte]
        split_ifs <;> linarith [hx j]
      · simp only [h.1, h.2, and_self, ↓reduceIte]
        split_ifs <;> linarith [hx j]
      · simp only [h, ↓reduceIte]
        split_ifs <;> linarith [hx j]
    · split_ifs <;> linarith [hx j]
  have hpr := hR p hp
  have hql := hL q hq
  have hprq : (p : ℝ) + q ≤ r := by exact_mod_cast hpq
  linarith

/-- See Subsection 6.1 of the paper: the complement of a short physical
interval meeting the active block has mass at least one eighth of the
period, above a threshold independent of the exterior and temperature. -/
theorem crossing_interval_complement_lower (σ ε : ℝ)
    (hε : 0 ≤ ε) (hσε : σ + 2 * ε < 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (N : ℕ+) (n : ℕ), n₀ ≤ n → 4 * n ≤ (N : ℕ) →
      ∀ x : Fin (N : ℕ) → ℝ, (∀ j, 0 ≤ x j) →
      cyclicGapSum N 0 n x ≤ (n : ℝ) + (n : ℝ) ^ (σ + ε) →
      (∀ p : ℕ, p ≤ (N : ℕ) - n →
        (∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val ∧ j.val < n + p), x j) ≤
          (p : ℝ) + 4 * (n : ℝ) ^ ε * (N : ℝ) ^ (σ + ε)) →
      (∀ q : ℕ, q ≤ (N : ℕ) - n →
        (∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => (N : ℕ) - q ≤ j.val), x j) ≤
          (q : ℝ) + 4 * (n : ℝ) ^ ε * (N : ℝ) ^ (σ + ε)) →
      ∀ (i : Fin (N : ℕ)) (r : ℕ), 2 * r ≤ (N : ℕ) →
        (∃ j ∈ cyclicIndexInterval N i r, j.val < n) →
          (N : ℝ) / 8 ≤ (N : ℝ) - cyclicGapSum N i r x := by
  obtain ⟨n₀, hn₀, hthreshold⟩ := complement_threshold σ ε hσε
  refine ⟨n₀, hn₀, ?_⟩
  intro N n hnn hnN x hx hmass hR hL i r hr hmeet
  have hn : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN' : 4 * (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hγ : σ + ε ≤ 1 := by linarith
  have hh := crossing_interval_mass_le_internal N n (by omega) x hx
    ((n : ℝ) ^ ε) (σ + ε) hR hL i r (by omega) hmeet
  have hr' : 2 * (r : ℝ) ≤ N := by exact_mod_cast hr
  exact complement_lower_internal hn' hN' hε hγ (hthreshold n hnn) hmass
    (by linarith) hh

/-- See Subsection 6.1 of the paper: the two exterior filters of the actual assembled
configuration are literally the filters in `exteriorGeometry`. Empty and
full exterior pieces are included. -/
theorem assembled_exterior_filters (e a r : ℕ) (hr : r ≤ e)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1))) :
    let x := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y u
    (∑ j ∈ Finset.univ.filter (fun j : Fin (e + a + 1) =>
      a + 1 ≤ j.val ∧ j.val < a + 1 + r), x j) =
        (∑ k ∈ Finset.univ.filter (fun k : Fin e => k.val < r), y k) ∧
    (∑ j ∈ Finset.univ.filter (fun j : Fin (e + a + 1) => e + a + 1 - r ≤ j.val), x j) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin e => e - r ≤ k.val), y k := by
  intro x
  constructor
  · symm
    apply Finset.sum_bij (fun k _ => (⟨a + 1 + k.val, by have := k.isLt; omega⟩ : Fin (e + a + 1)))
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
    · intro k _ l _ h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp at this
      omega
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hjN := j.isLt
      refine ⟨⟨j.val - (a + 1), by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
      apply Fin.ext
      dsimp
      omega
    · intro k _
      exact (InterpolantLocalLaws.assemble_exterior_retained e a y u k).symm
  · symm
    apply Finset.sum_bij (fun k _ => (⟨a + 1 + k.val, by have := k.isLt; omega⟩ : Fin (e + a + 1)))
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
    · intro k _ l _ h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp at this
      omega
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hjN := j.isLt
      refine ⟨⟨j.val - (a + 1), by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
      apply Fin.ext
      dsimp
      omega
    · intro k _
      exact (InterpolantLocalLaws.assemble_exterior_retained e a y u k).symm

/-- See Subsection 6.1 of the paper, geometric clause for the literal
fixed-exterior simplex. Above a size threshold, every short interval
meeting the active block is uniformly separated from the other image
collision, for every active point and every geometrically admissible exterior. -/
theorem physical_crossing_complement_lower (s ε : ℝ) (hs : 0 ≤ s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (e a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      ∀ (i : Fin (e + a + 1)) (r : ℕ), 2 * r ≤ e + a + 1 →
      (∃ j ∈ cyclicIndexInterval (e + a).succPNat i r, j.val < a + 1) →
        (e + a + 1 : ℝ) / 8 ≤ (e + a + 1 : ℝ) -
          cyclicGapSum (e + a).succPNat i r
            (WithLp.ofLp (RetainedSimplex.assemble e a
              (InterpolatingDensities.exteriorPermutation e a) y.val u)) := by
  have hσ : 0 ≤ min s 1 / 2 := by positivity
  obtain ⟨n₀, hn₀, hbound⟩ := crossing_interval_complement_lower
    (min s 1 / 2) ε hε hσε
  refine ⟨n₀, hn₀, ?_⟩
  intro e a hnn hsize y hgeom u hu i r hr hmeet
  let N := (e + a).succPNat
  let x := WithLp.ofLp (RetainedSimplex.assemble e a
    (InterpolatingDensities.exteriorPermutation e a) y.val u)
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hactive : cyclicGapSum N 0 (a + 1) x = ∑ k, u k := by
    have hz : (⟨0, by change 0 < e + a + 1; omega⟩ : Fin (N : ℕ)) = 0 := by
      apply Fin.ext; simp
    have hh := InterpolantLocalLaws.cyclicGapSum_assembled_active e a 0 (a + 1)
      (by omega) (by omega) y.val u
    rw [hz] at hh
    simpa only [Nat.zero_add] using hh
  have hmass : cyclicGapSum N 0 (a + 1) x ≤
      (a + 1 : ℝ) + (a + 1 : ℝ) ^ (min s 1 / 2 + ε) := by
    rw [hactive, hu.2]
    have hh := (abs_le.mp hgeom.1).2
    push_cast at hh ⊢
    linarith
  have hpieces (r : ℕ) (hre : r ≤ e) :
      (∑ k ∈ Finset.univ.filter (fun k : Fin e => k.val < r), y.val k) ≤
        (r : ℝ) + 4 * (a + 1 : ℝ) ^ ε * (N : ℝ) ^ (min s 1 / 2 + ε) ∧
      (∑ k ∈ Finset.univ.filter (fun k : Fin e => e - r ≤ k.val), y.val k) ≤
        (r : ℝ) + 4 * (a + 1 : ℝ) ^ ε * (N : ℝ) ^ (min s 1 / 2 + ε) := by
    by_cases hr0 : r = 0
    · subst r
      simp only [not_lt_zero, Finset.filter_false, Finset.sum_empty, Nat.sub_zero, Nat.cast_zero,
        zero_add]
      have he : (Finset.univ.filter (fun k : Fin e => e ≤ k.val)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro k _
        exact Nat.not_le.mpr k.isLt
      rw [he, Finset.sum_empty]
      constructor <;> positivity
    · have hrr := hgeom.2 r (by omega) hre
      have hrN : (r : ℝ) ≤ N := by exact_mod_cast (show r ≤ (N : ℕ) by dsimp [N]; omega)
      have hp := Real.rpow_le_rpow (Nat.cast_nonneg r) hrN (by linarith : 0 ≤ min s 1 / 2 + ε)
      have hb := mul_le_mul_of_nonneg_left hp
        (by positivity : 0 ≤ 4 * (a + 1 : ℝ) ^ ε)
      have hR := (abs_le.mp hrr.1).2
      have hL := (abs_le.mp hrr.2).2
      push_cast at hR hL
      constructor <;> linarith
  have hh := hbound N (a + 1) hnn hsize x (fun j => (hx.1 j).le)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hmass) ?_ ?_ i r hr hmeet
  · simpa only [N, x, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hh
  · intro p hp
    have hpe : p ≤ e := by dsimp only [N, Nat.succPNat_coe] at hp; omega
    dsimp only [N, Nat.succPNat_coe, x]
    rw [(assembled_exterior_filters e a p hpe y.val u).1]
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using (hpieces p hpe).1
  · intro q hq
    have hqe : q ≤ e := by dsimp only [N, Nat.succPNat_coe] at hq; omega
    dsimp only [N, Nat.succPNat_coe, x]
    rw [(assembled_exterior_filters e a q hqe y.val u).2]
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using (hpieces q hqe).2

/-- Internal coefficient comparison in Subsection 6.1. The
physical interval stays in the first half-period, so both nearest images
are bounded below by its actual length. -/
theorem internal_coefficient_comparison_internal (p : Parameters) (N : ℕ+)
    {n r η : ℝ} (hn : 0 < n) (hr : 0 < r)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (hhalf : 2 * L.val ≤ N) (hlo : r * n ^ (-η) ≤ L.val)
    (hhi : L.val ≤ r * n ^ η) :
    p.val.2 * (p.val.2 + 1) * n ^ (-(p.val.2 + 2) * η) * r ^ (-p.val.2 - 2) ≤
      PhysicalEnergy.intervalCoefficient p N L ∧
    PhysicalEnergy.intervalCoefficient p N L ≤
      (p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])) *
          n ^ ((p.val.2 + 2) * η) * r ^ (-p.val.2 - 2) := by
  have hs : -p.val.2 - 2 ≤ 0 := by linarith [p.property.2.1]
  have hl := Real.rpow_le_rpow_of_nonpos L.property.1 hhi hs
  rw [Real.mul_rpow hr.le (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le] at hl
  have he : η * (-p.val.2 - 2) = -(p.val.2 + 2) * η := by ring
  rw [he] at hl
  have hl' := mul_le_mul_of_nonneg_left hl
    (by have := p.property.2.1; positivity : 0 ≤ p.val.2 * (p.val.2 + 1))
  constructor
  · apply le_trans _ (PhysicalEnergy.intervalCoefficient_lower p N L)
    convert hl' using 1; ring
  · have hh := PhysicalEnergy.intervalCoefficient_upper p N L L.property.1 le_rfl (by linarith)
    have hu := InterpolantLocalLaws.internal_cutoff_rpow hn hr hs hlo
    have hc : 0 ≤ p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1]) := by
      have := p.property.2.1
      have := PeriodicPower.bound_pos (p.val.2 + 2) (by linarith [p.property.2.1])
      positivity
    rw [show -η * (-p.val.2 - 2) = (p.val.2 + 2) * η by ring] at hu
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu hc)

/-- See Subsection 6.1 of the paper, all-size internal coefficient clause. This
uses the actual fixed-exterior assembly, the rigidity event, and
the literal physical image coefficient. Neither an exterior Hessian
bound nor an exceptional-set hypothesis is needed. -/
theorem physical_internal_coefficient_bounds (p : Parameters) (ε η : ℝ)
    (hγ : min p.val.2 1 / 2 + ε ≤ 1)
    (e a : ℕ) (hN : 4 * (a + 1) ≤ e + a + 1)
    (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
    (hgeom : InterpolantLocalLaws.exteriorGeometry p.val.2 ε e a y.val)
    (u : EuclideanSpace ℝ (Fin (a + 1)))
    (hu : u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k))
    (hgood : WithLp.ofLp u ∈ goodBlockEvent p.val.2 a.succPNat (e + a).succPNat η)
    (i r : ℕ) (hr : 0 < r) (hir : i + r ≤ a + 1) :
    let N := (e + a).succPNat
    let x := WithLp.ofLp (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y.val u)
    let ℓ := cyclicGapSum N ⟨i, by change i < e + a + 1; omega⟩ r x
    ∃ hℓ : 0 < ℓ ∧ ℓ < (N : ℝ),
      p.val.2 * (p.val.2 + 1) * (a + 1 : ℝ) ^ (-(p.val.2 + 2) * η) *
        (r : ℝ) ^ (-p.val.2 - 2) ≤ PhysicalEnergy.intervalCoefficient p N ⟨ℓ, hℓ⟩ ∧
      PhysicalEnergy.intervalCoefficient p N ⟨ℓ, hℓ⟩ ≤
        (p.val.2 * (p.val.2 + 1) *
          PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])) *
            (a + 1 : ℝ) ^ ((p.val.2 + 2) * η) * (r : ℝ) ^ (-p.val.2 - 2) := by
  intro N x ℓ
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hxs : x ∈ Riesz1.gapSimplex N := ⟨hx.1, by
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hx.2⟩
  have hℓ := PhysicalEnergy.gapSum_mem N ⟨i, by dsimp [N]; omega⟩ hr (by dsimp [N]; omega) x hxs
  have heq : ℓ = ∑ k : Fin r, u ⟨i + k.val, by have := k.isLt; omega⟩ :=
    InterpolantLocalLaws.cyclicGapSum_assembled_active e a i r (by omega) hir y.val u
  have hlo : (r : ℝ) * (a + 1 : ℝ) ^ (-η) ≤ ℓ := by
    rw [heq]
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using
      InterpolantLocalLaws.goodBlockEvent_interval_lower p.val.2 η a.succPNat
        (e + a).succPNat (WithLp.ofLp u) hgood i r hir
  have hhi : ℓ ≤ (r : ℝ) * (a + 1 : ℝ) ^ η := by
    have hg : ∀ k : Fin (a + 1), u k ≤ (a + 1 : ℝ) ^ η := by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using fun k => (hgood.2.1 k).2
    rw [heq]
    calc
      _ ≤ ∑ _k : Fin r, (a + 1 : ℝ) ^ η := Finset.sum_le_sum fun k _ =>
        hg ⟨i + k.val, by have := k.isLt; omega⟩
      _ = _ := by simp
  have hsub : ℓ ≤ ∑ k, u k := by
    let f : Fin r ↪ Fin (a + 1) :=
      ⟨fun k => ⟨i + k.val, by have := k.isLt; omega⟩,
        fun k l h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
    rw [heq]
    change (∑ k : Fin r, u (f k)) ≤ _
    rw [← Finset.sum_map]
    exact Finset.sum_le_univ_sum_of_nonneg fun k => (hu.1 k).le
  have hn1 : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hmass : (∑ k, u k) ≤ 2 * (a + 1 : ℝ) := by
    have hh := (abs_le.mp hgeom.1).2
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 hγ
    rw [Real.rpow_one] at hp
    rw [hu.2]
    push_cast at hh ⊢
    linarith
  have hhalf : 2 * ℓ ≤ (N : ℝ) := by
    have hN' : 4 * (a + 1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine ⟨hℓ, ?_⟩
  exact internal_coefficient_comparison_internal p N (by positivity)
    (by exact_mod_cast hr) ⟨ℓ, hℓ⟩ hhalf hlo hhi

/-- The actual exceptional weight dominates the square of an inverse-gap
curvature, in both exponent regimes of Subsection 6.1. -/
theorem curvature_power_sq_le_weight (s : ℝ) (hs : 0 < s) (a : ℕ)
    (u : Fin (a + 1) → ℝ) (hu : ∀ j, 0 < u j) (j : Fin (a + 1)) :
    (1 + u j ^ (-s - 2)) ^ 2 ≤
      4 * InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s u := by
  have hW := InterpolantLocalLaws.one_le_exceptionalWeight (n := a.succPNat) s u
    (fun j => (hu j).le)
  have hterm : u j ^ (-4 * s - 12) ≤ ∑ i : Fin (a + 1), u i ^ (-4 * s - 12) :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hu i).le _) (Finset.mem_univ j)
  have hsq : (u j ^ (-s - 2)) ^ 2 ≤
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s u := by
    change (u j ^ (-s - 2)) ^ 2 ≤ 1 + ∑ i : Fin (a + 1), u i ^ (-4 * s - 12)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hu j).le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-s - 2) * (2 : ℝ) = -2 * s - 4 by ring]
    by_cases hj1 : u j ≤ 1
    · have hp := Real.rpow_le_rpow_of_exponent_ge (hu j) hj1
        (by linarith : -4 * s - 12 ≤ -2 * s - 4)
      linarith
    · have hp := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hj1)
        (by linarith : -2 * s - 4 ≤ 0)
      have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
        Real.rpow_nonneg (hu i).le (-4 * s - 12))
      linarith
  nlinarith [sq_nonneg (u j ^ (-s - 2) - 1)]

/-- Internal whole-simplex coefficient estimate of Subsection 6.1.
One included active gap controls the principal singularity, while a unit
complementary distance excludes the opposite image singularity. -/
theorem coefficient_sq_le_weight_internal (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) (a : ℕ)
    (u : Fin (a + 1) → ℝ) (hu : ∀ j, 0 < u j) (j : Fin (a + 1))
    (hLj : u j ≤ L.val) (hcomp : 1 ≤ (N : ℝ) - L.val) :
    PhysicalEnergy.intervalCoefficient p N L ^ 2 ≤
      4 * (p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])) ^ 2 *
          InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) p.val.2 u := by
  let B := p.val.2 * (p.val.2 + 1) *
    PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])
  have hB : 0 < B := by
    have := p.property.2.1
    have := PeriodicPower.bound_pos (p.val.2 + 2) (by linarith [p.property.2.1])
    positivity
  have hδ : 0 < min (u j) 1 := lt_min (hu j) zero_lt_one
  have hh := PhysicalEnergy.intervalCoefficient_upper p N L hδ
    ((min_le_left _ _).trans hLj) ((min_le_right _ _).trans hcomp)
  have hpower : (min (u j) 1) ^ (-p.val.2 - 2) ≤ 1 + u j ^ (-p.val.2 - 2) := by
    by_cases hj : u j ≤ 1
    · rw [min_eq_left hj]
      linarith
    · rw [min_eq_right (le_of_not_ge hj), Real.one_rpow]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (hu j).le _)
  have hupper : PhysicalEnergy.intervalCoefficient p N L ≤ B * (1 + u j ^ (-p.val.2 - 2)) :=
    hh.trans (mul_le_mul_of_nonneg_left hpower hB.le)
  have hnonneg := (PhysicalEnergy.intervalCoefficient_pos p N L).le
  have hsq := mul_self_le_mul_self hnonneg hupper
  have hw := curvature_power_sq_le_weight p.val.2 p.property.2.1 a u hu j
  have hm := mul_le_mul_of_nonneg_left hw (sq_nonneg B)
  change _ ≤ 4 * B ^ 2 * _
  nlinarith only [hsq, hm]

/-- See Subsection 6.1 of the paper, whole-simplex bound for each physical
interval coefficient meeting a specified active coordinate. This is
uniform in both the exterior and the active point, with the actual
exceptional weight, above the temperature-independent threshold. -/
theorem physical_crossing_coefficient_sq (p : Parameters) (ε : ℝ)
    (hε : 0 ≤ ε) (hσε : min p.val.2 1 / 2 + 2 * ε < 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (e a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry p.val.2 ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      ∀ (i : Fin (e + a + 1)) (r : ℕ), 0 < r → 2 * r ≤ e + a + 1 →
      ∀ j : Fin (a + 1),
      j.castLE (show a + 1 ≤ e + a + 1 by omega) ∈ cyclicIndexInterval (e + a).succPNat i r →
      let N := (e + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      ∃ hℓ : 0 < cyclicGapSum N i r x ∧ cyclicGapSum N i r x < (N : ℝ),
        PhysicalEnergy.intervalCoefficient p N ⟨cyclicGapSum N i r x, hℓ⟩ ^ 2 ≤
          4 * (p.val.2 * (p.val.2 + 1) *
            PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])) ^ 2 *
              InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) p.val.2 (WithLp.ofLp u) := by
  obtain ⟨n₀, hn₀, hb⟩ := physical_crossing_complement_lower p.val.2 ε p.property.2.1.le hε hσε
  refine ⟨n₀, hn₀, ?_⟩
  intro e a hnn hsize y hgeom u hu i r hr hrN j hj N x
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hxs : x ∈ Riesz1.gapSimplex N := ⟨hx.1, by
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hx.2⟩
  have hℓ := PhysicalEnergy.gapSum_mem N i hr (by dsimp [N]; omega) x hxs
  have hc := hb e a hnn hsize y hgeom u hu i r hrN
    ⟨j.castLE (show a + 1 ≤ e + a + 1 by omega), hj, j.isLt⟩
  have hn : 2 ≤ a + 1 := hn₀.trans hnn
  have hN : (8 : ℝ) ≤ N := by exact_mod_cast (show 8 ≤ e + a + 1 by omega)
  have hcomp : 1 ≤ (N : ℝ) - cyclicGapSum N i r x := by
    have hc' : (N : ℝ) / 8 ≤ (N : ℝ) - cyclicGapSum N i r x := by
      simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hc
    linarith
  have hsingle := Finset.single_le_sum
    (s := cyclicIndexInterval N i r) (f := x) (fun k _ => (hxs.1 k).le) hj
  have hsingle' := hsingle.trans_eq
    (sum_cyclicIndexInterval_eq_cyclicGapSum N i (r := r) (by dsimp [N]; omega) x)
  have hLj : u j ≤ cyclicGapSum N i r x := by
    have he := InterpolatingDensities.assemble_exterior_active e a y.val u j (by omega)
    exact he ▸ hsingle'
  exact ⟨hℓ, coefficient_sq_le_weight_internal p N ⟨cyclicGapSum N i r x, hℓ⟩ a
    (WithLp.ofLp u) hu.1 j hLj hcomp⟩

end Riesz2.InterpolationCoefficients
