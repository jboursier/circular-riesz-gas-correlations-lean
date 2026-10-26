/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Variance.APrioriGoodGradientCount
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Cyclic distance: metric axioms, interval metric and shells

For labels `i j : Fin N`, the cyclic distance is `Riesz1.cyclicIndexDistance N i j`. A subset of
labels inherits this distance: restricted to the subset it is the same function, and it is not
replaced by the distance of a shorter cycle on the subset.

The lemmas below give the metric axioms, the interval metric on arcs of length at most half the
cycle, and the shells `cyclicShell N i k` of labels at distance `k` from `i`. A shell has at most
two labels (`card_cyclicShell_le_two`), exactly one label when `k = 0` or `2 k = N`, and exactly
two labels when `0 < 2 k < N`. The shells about `i` partition the labels (`sum_card_cyclicShell`).
-/

@[expose] public section

open Finset

namespace Riesz2

variable {N : ℕ+}

/-- The integer cast of the natural distance: `Nat.dist x y = |x - y|`. -/
theorem natCast_dist_eq_abs (x y : ℕ) : ((Nat.dist x y : ℕ) : ℤ) = |(x : ℤ) - y| := by
  unfold Nat.dist
  rcases le_total x y with h | h
  · rw [show x - y + (y - x) = y - x by omega, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (show (0 : ℤ) ≤ (y : ℤ) - x by omega)]
  · rw [show x - y + (y - x) = x - y by omega, Nat.cast_sub h,
      abs_of_nonneg (show (0 : ℤ) ≤ (x : ℤ) - y by omega)]

/-- The cyclic distance of a label to itself is zero. -/
theorem cyclicIndexDistance_self (i : Fin (N : ℕ)) : Riesz1.cyclicIndexDistance N i i = 0 := by
  simp [Riesz1.cyclicIndexDistance, Nat.dist_self]

/-- The cyclic distance vanishes exactly on the diagonal. -/
theorem cyclicIndexDistance_eq_zero_iff (i j : Fin (N : ℕ)) :
    Riesz1.cyclicIndexDistance N i j = 0 ↔ i = j := by
  have hi := i.isLt
  have hj := j.isLt
  constructor
  · intro h
    apply Fin.ext
    unfold Riesz1.cyclicIndexDistance Nat.dist at h
    omega
  · rintro rfl
    simp [Riesz1.cyclicIndexDistance, Nat.dist_self]

/-- The cyclic distance satisfies the triangle inequality. A shortest shift from `i` to `j`
followed by a shortest shift from `j` to `k` is a shift from `i` to `k`, and the cyclic distance
is at most the length of any such shift. -/
theorem cyclicIndexDistance_triangle (i j k : Fin (N : ℕ)) :
    Riesz1.cyclicIndexDistance N i k ≤
      Riesz1.cyclicIndexDistance N i j + Riesz1.cyclicIndexDistance N j k := by
  obtain ⟨m, hmj, hm⟩ := Riesz1.APG.exists_shift_of_cyclicIndexDistance (N := N) i j
  obtain ⟨n, hnk, hn⟩ := Riesz1.APG.exists_shift_of_cyclicIndexDistance (N := N) j k
  have hjm : Riesz1.labelOf N (((i : ℕ) : ℤ) + m) = Riesz1.labelOf N ((j : ℕ) : ℤ) := by
    rw [hmj, Riesz1.labelOf_natCast]
  have hdvd : ((N : ℕ) : ℤ) ∣ (((j : ℕ) : ℤ) + n) - (((i : ℕ) : ℤ) + m + n) := by
    rw [show (((j : ℕ) : ℤ) + n) - (((i : ℕ) : ℤ) + m + n) = ((j : ℕ) : ℤ) - (((i : ℕ) : ℤ) + m)
      by ring]
    exact Riesz1.dvd_of_labelOf_eq N hjm
  have hlab : Riesz1.labelOf N (((i : ℕ) : ℤ) + m + n) = k :=
    (Riesz1.labelOf_eq_of_dvd N hdvd).trans hnk
  have hle := Riesz1.APG.cyclicIndexDistance_le_abs_labelOf (N := N)
    ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + m + n)
  rw [Riesz1.labelOf_natCast, hlab] at hle
  have htri : |((i : ℕ) : ℤ) + m + n - ((i : ℕ) : ℤ)| ≤ |m| + |n| := by
    rw [show ((i : ℕ) : ℤ) + m + n - ((i : ℕ) : ℤ) = m + n by ring]
    exact abs_add_le m n
  have hm' : ((m.natAbs : ℕ) : ℤ) = (Riesz1.cyclicIndexDistance N i j : ℤ) := by rw [hm]
  have hn' : ((n.natAbs : ℕ) : ℤ) = (Riesz1.cyclicIndexDistance N j k : ℤ) := by rw [hn]
  have habs_m : |m| = ((m.natAbs : ℕ) : ℤ) := Int.abs_eq_natAbs m
  have habs_n : |n| = ((n.natAbs : ℕ) : ℤ) := Int.abs_eq_natAbs n
  have hfinal : ((Riesz1.cyclicIndexDistance N i k : ℕ) : ℤ) ≤
      ((Riesz1.cyclicIndexDistance N i j : ℕ) : ℤ) +
        ((Riesz1.cyclicIndexDistance N j k : ℕ) : ℤ) := by
    linarith
  exact_mod_cast hfinal

/-- On an arc of length at most half the cycle, the cyclic distance is the integer distance of the
endpoints: `d(a, b) = |b - a|` whenever `2 |b - a| ≤ N`. -/
theorem cyclicIndexDistance_labelOf_eq_abs {a b : ℤ} (h : 2 * |b - a| ≤ (N : ℤ)) :
    ((Riesz1.cyclicIndexDistance N (Riesz1.labelOf N a) (Riesz1.labelOf N b) : ℕ) : ℤ) =
      |b - a| := by
  refine le_antisymm (Riesz1.APG.cyclicIndexDistance_le_abs_labelOf (N := N) a b) ?_
  obtain ⟨k, hk, hkd⟩ := Riesz1.APG.exists_shift_of_cyclicIndexDistance (N := N)
    (Riesz1.labelOf N a) (Riesz1.labelOf N b)
  have hv := Riesz1.APG.val_labelOf_add (N := N) a
  have h1 : Riesz1.labelOf N (a + k) = Riesz1.labelOf N ((Riesz1.labelOf N a : ℕ) + k) :=
    Riesz1.labelOf_eq_of_dvd N ⟨-(a / ((N : ℕ) : ℤ)), by linarith⟩
  have hbk : Riesz1.labelOf N (a + k) = Riesz1.labelOf N b := h1.trans hk
  obtain ⟨q, hq⟩ := Riesz1.dvd_of_labelOf_eq N hbk
  have hkt : |b - a| ≤ |k| := by
    rcases eq_or_ne q 0 with hq0 | hq0
    · subst hq0
      rw [mul_zero] at hq
      have hba : b - a = k := by linarith
      rw [hba]
    · have hNq : ((N : ℕ) : ℤ) ≤ |((N : ℕ) : ℤ) * q| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
        have hq1 : (1 : ℤ) ≤ |q| := Int.one_le_abs hq0
        have hN0 : (0 : ℤ) ≤ ((N : ℕ) : ℤ) := Int.natCast_nonneg _
        nlinarith
      have hsplit : ((N : ℕ) : ℤ) * q = (b - a) - k := by linarith
      have htri2 : |((N : ℕ) : ℤ) * q| ≤ |b - a| + |k| := by
        rw [hsplit, sub_eq_add_neg]
        have := abs_add_le (b - a) (-k)
        rwa [abs_neg] at this
      linarith
  rw [← hkd, ← Int.abs_eq_natAbs]
  exact hkt

/-- The shell of radius `k` about the label `i`: the labels at cyclic distance exactly `k`. -/
def cyclicShell (N : ℕ+) (i : Fin (N : ℕ)) (k : ℕ) : Finset (Fin (N : ℕ)) :=
  univ.filter fun j => Riesz1.cyclicIndexDistance N i j = k

/-- A label of the shell of radius `k` about `i` is `i + k` or `i - k`, reduced modulo `N`. -/
theorem cyclicShell_subset_pair (i : Fin (N : ℕ)) (k : ℕ) :
    cyclicShell N i k ⊆
      {Riesz1.labelOf N (((i : ℕ) : ℤ) + k), Riesz1.labelOf N (((i : ℕ) : ℤ) - k)} := by
  intro j hj
  rw [cyclicShell, mem_filter] at hj
  obtain ⟨m, hm, hmk⟩ := Riesz1.APG.exists_shift_of_cyclicIndexDistance (N := N) i j
  have hmk' : m.natAbs = k := hmk.trans hj.2
  rw [mem_insert, mem_singleton]
  rcases Int.natAbs_eq m with h | h <;> rw [hmk'] at h
  · left
    rw [← hm, h]
  · right
    rw [← hm, h, sub_eq_add_neg]

/-- The shell of radius `k` has at most two labels. -/
theorem card_cyclicShell_le_two (i : Fin (N : ℕ)) (k : ℕ) : (cyclicShell N i k).card ≤ 2 :=
  (card_le_card (cyclicShell_subset_pair i k)).trans card_le_two

/-- The shell of radius zero is the label itself. -/
theorem cyclicShell_zero (i : Fin (N : ℕ)) : cyclicShell N i 0 = {i} := by
  ext j
  simp only [cyclicShell, mem_filter, mem_univ, true_and, mem_singleton,
    cyclicIndexDistance_eq_zero_iff]
  exact eq_comm

/-- The shell of radius zero has one label, for every size `N ≥ 1`. -/
theorem card_cyclicShell_zero (i : Fin (N : ℕ)) : (cyclicShell N i 0).card = 1 := by
  rw [cyclicShell_zero, card_singleton]

/-- The label `i + t` lies at distance `|t|` from `i` on an arc of length at most half the cycle,
so it belongs to the shell of radius `t.natAbs` about `i`. -/
theorem labelOf_mem_cyclicShell (i : Fin (N : ℕ)) {t : ℤ} (ht : 2 * |t| ≤ (N : ℤ)) :
    Riesz1.labelOf N (((i : ℕ) : ℤ) + t) ∈ cyclicShell N i t.natAbs := by
  rw [cyclicShell, mem_filter]
  refine ⟨mem_univ _, ?_⟩
  have h := cyclicIndexDistance_labelOf_eq_abs (N := N) (a := ((i : ℕ) : ℤ))
    (b := ((i : ℕ) : ℤ) + t) (by rwa [add_sub_cancel_left])
  rw [Riesz1.labelOf_natCast, add_sub_cancel_left, Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- For `2 k < N`, the shell of radius `k` is the pair of labels `i + k` and `i - k`. -/
theorem cyclicShell_eq_pair (i : Fin (N : ℕ)) {k : ℕ} (h2 : 2 * k < (N : ℕ)) :
    cyclicShell N i k =
      {Riesz1.labelOf N (((i : ℕ) : ℤ) + k), Riesz1.labelOf N (((i : ℕ) : ℤ) - k)} := by
  apply Subset.antisymm (cyclicShell_subset_pair i k)
  intro j hj
  rw [mem_insert, mem_singleton] at hj
  have hk2 : 2 * |(k : ℤ)| ≤ ((N : ℕ) : ℤ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg k)]
    omega
  have hplus := labelOf_mem_cyclicShell i (t := (k : ℤ)) hk2
  have hminus := labelOf_mem_cyclicShell i (t := -(k : ℤ)) (by rwa [abs_neg])
  have hplus' : Riesz1.labelOf N (((i : ℕ) : ℤ) + k) ∈ cyclicShell N i k := by
    simpa using hplus
  have hminus' : Riesz1.labelOf N (((i : ℕ) : ℤ) - k) ∈ cyclicShell N i k := by
    rw [← sub_eq_add_neg] at hminus
    simpa using hminus
  rcases hj with rfl | rfl
  · exact hplus'
  · exact hminus'

/-- For `0 < k` with `2 k < N`, the shell of radius `k` has exactly two labels. -/
theorem card_cyclicShell_of_two_mul_lt (i : Fin (N : ℕ)) {k : ℕ} (hk : 0 < k)
    (h2 : 2 * k < (N : ℕ)) : (cyclicShell N i k).card = 2 := by
  rw [cyclicShell_eq_pair i h2]
  refine card_pair_eq_two_iff.2 fun heq => ?_
  have hd := Riesz1.dvd_of_labelOf_eq N heq
  have h0 : ((N : ℕ) : ℤ) ∣ 2 * (k : ℤ) := by
    have h' : ((N : ℕ) : ℤ) ∣ -(2 * (k : ℤ)) := by
      rwa [show (((i : ℕ) : ℤ) - k) - (((i : ℕ) : ℤ) + k) = -(2 * (k : ℤ)) by ring] at hd
    exact dvd_neg.mp h'
  have habs : |2 * (k : ℤ)| < ((N : ℕ) : ℤ) := by
    rw [abs_of_nonneg (by positivity)]
    omega
  have := Int.eq_zero_of_abs_lt_dvd h0 habs
  omega

/-- For `2 k = N`, the labels `i + k` and `i - k` coincide, so the shell of radius `k` has exactly
one label. This is the half-cycle case. -/
theorem card_cyclicShell_of_two_mul_eq (i : Fin (N : ℕ)) {k : ℕ} (h2 : 2 * k = (N : ℕ)) :
    (cyclicShell N i k).card = 1 := by
  have hsub := cyclicShell_subset_pair i k
  have h2' : (2 : ℤ) * k = ((N : ℕ) : ℤ) := by exact_mod_cast h2
  have heq : Riesz1.labelOf N (((i : ℕ) : ℤ) + k) = Riesz1.labelOf N (((i : ℕ) : ℤ) - k) :=
    Riesz1.labelOf_eq_of_dvd N ⟨-1, by linarith⟩
  have hmem : Riesz1.labelOf N (((i : ℕ) : ℤ) + k) ∈ cyclicShell N i k := by
    have := labelOf_mem_cyclicShell i (t := (k : ℤ))
      (by rw [abs_of_nonneg (Int.natCast_nonneg k)]; omega)
    simpa using this
  rw [card_eq_one]
  refine ⟨Riesz1.labelOf N (((i : ℕ) : ℤ) + k),
    Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun j hj => ?_⟩⟩
  have hj' := hsub hj
  rw [mem_insert, mem_singleton, ← heq] at hj'
  rcases hj' with h | h <;> exact h

/-- For `N < 2 k`, the shell of radius `k` is empty, since every cyclic distance is at most
`N / 2`. -/
theorem card_cyclicShell_of_lt_two_mul (i : Fin (N : ℕ)) {k : ℕ} (h : (N : ℕ) < 2 * k) :
    (cyclicShell N i k).card = 0 := by
  rw [cyclicShell, card_eq_zero, filter_eq_empty_iff]
  intro j _ hj
  have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i j
  omega

/-- The shells about `i` partition the labels, so their cardinalities sum to `N`. -/
theorem sum_card_cyclicShell (i : Fin (N : ℕ)) :
    ∑ k ∈ range ((N : ℕ) + 1), (cyclicShell N i k).card = (N : ℕ) := by
  have hmap : ∀ j ∈ (univ : Finset (Fin (N : ℕ))),
      Riesz1.cyclicIndexDistance N i j ∈ range ((N : ℕ) + 1) := by
    intro j _
    have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i j
    rw [mem_range]
    omega
  have h := Finset.card_eq_sum_card_fiberwise hmap
  rw [card_univ, Fintype.card_fin] at h
  exact h.symm

end Riesz2

end
