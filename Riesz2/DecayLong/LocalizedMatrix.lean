/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundaryEntriesPart4
public import Riesz2.DecayLong.GlobalReferenceErrorPart2
public import Riesz2.ToMathlib.CyclicDistance

/-!
# Exact matrix identities for localization

The local window of Subsection 5.5 uses the original cyclic distance.
Internal and crossing interval matrices are the existing constructions in
`IntervalBoundary` and `BoundaryEntries`. No second interval encoding is used.
The inclusion--exclusion identities below are the algebraic part of the proof of Proposition 5.15.
-/

@[expose] public section
noncomputable section

open MeasureTheory Finset
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.LocalizedMatrix

/-- See Subsection 5.5 of the paper: the radius-`R/8` window in the parent component cycle.
The natural-number inequality is exactly the displayed real-radius inequality. -/
def window (m : ℕ+) (j i₀ : Fin (m : ℕ)) : Finset (Fin (m : ℕ)) :=
  univ.filter fun i => 8 * Riesz1.cyclicIndexDistance m i j ≤
    Riesz1.cyclicIndexDistance m j i₀

/-- See Subsection 5.5 of the paper: the center is retained, including at zero separation. -/
theorem center_mem_window (m : ℕ+) (j i₀ : Fin (m : ℕ)) : j ∈ window m j i₀ := by
  simp [window, cyclicIndexDistance_self]

/-- See Subsection 5.5 of the paper: exact agreement with the real-radius ball. -/
theorem mem_window_iff (m : ℕ+) (j i₀ i : Fin (m : ℕ)) :
    i ∈ window m j i₀ ↔ (Riesz1.cyclicIndexDistance m i j : ℝ) ≤
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 8 := by
  simp only [window, mem_filter, mem_univ, true_and]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  constructor
  · intro h
    have h' : (8 : ℝ) * Riesz1.cyclicIndexDistance m i j ≤
        Riesz1.cyclicIndexDistance m j i₀ := by exact_mod_cast h
    simpa only [mul_comm] using h'
  · intro h
    have h' : (8 : ℝ) * Riesz1.cyclicIndexDistance m i j ≤
        Riesz1.cyclicIndexDistance m j i₀ := by simpa only [mul_comm] using h
    exact_mod_cast h'

/-- The local window is nonempty, so its cardinal is a positive size on its
entire carrier (Subsection 5.5). -/
def windowSize (m : ℕ+) (j i₀ : Fin (m : ℕ)) : ℕ+ :=
  ⟨(window m j i₀).card, card_pos.mpr ⟨j, center_mem_window m j i₀⟩⟩

/-- See Subsection 5.5 of the paper: the new component period. The scalar space is
unchanged by this definition. -/
def windowPeriod (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) : ℕ+ :=
  ⟨min (m : ℕ) (max (2 * (windowSize m j i₀ : ℕ))
    ⌈(windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊),
    lt_min m.pos (lt_of_lt_of_le (by have := (windowSize m j i₀).pos; omega)
      (le_max_left _ _))⟩

/-- A separated source is outside the local window (the proof of Proposition 5.15). -/
theorem source_not_mem_window (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 0 < Riesz1.cyclicIndexDistance m j i₀) : i₀ ∉ window m j i₀ := by
  simp only [window, mem_filter, mem_univ, true_and]
  have hs : Riesz1.cyclicIndexDistance m i₀ j = Riesz1.cyclicIndexDistance m j i₀ := by
    simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
  rw [hs]
  omega

/-- Every local index is at least `7R/8` from the source. This is the
separation step of the proof of Proposition 5.15. -/
theorem window_separation (m : ℕ+) (j i₀ i : Fin (m : ℕ))
    (hi : i ∈ window m j i₀) :
    7 * Riesz1.cyclicIndexDistance m j i₀ ≤
      8 * Riesz1.cyclicIndexDistance m i i₀ := by
  have ht := cyclicIndexDistance_triangle j i i₀
  have hs : Riesz1.cyclicIndexDistance m j i = Riesz1.cyclicIndexDistance m i j := by
    simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
  simp only [window, mem_filter, mem_univ, true_and] at hi
  rw [hs] at ht
  omega

/-- The parent cap in Subsection 5.5 is literal. -/
theorem windowPeriod_le_parent (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) : (windowPeriod s m j i₀ : ℕ) ≤ m := min_le_left _ _

/-- See Subsection 5.5 of the paper: the exact number of labels in the window. In
particular the two labels at each positive distance are counted separately. -/
theorem window_card (m : ℕ+) (j i₀ : Fin (m : ℕ)) :
    (window m j i₀).card = 2 * (Riesz1.cyclicIndexDistance m j i₀ / 8) + 1 := by
  let R := Riesz1.cyclicIndexDistance m j i₀
  let k := R / 8
  have hR : 2 * R ≤ (m : ℕ) := by
    dsimp only [R, Riesz1.cyclicIndexDistance]
    have hd : Nat.dist j.val i₀.val < (m : ℕ) := by
      have hj := j.isLt
      have hi := i₀.isLt
      unfold Nat.dist
      omega
    omega
  have hsmall : 2 * k < (m : ℕ) := by have := m.pos; dsimp only [k]; omega
  have hcount : (window m j i₀).card =
      ∑ r ∈ range (k + 1), (cyclicShell m j r).card := by
    calc
      _ = ∑ i : Fin (m : ℕ), if Riesz1.cyclicIndexDistance m i j ≤ k then 1 else 0 := by
        simp only [window, card_filter, k, R]
        apply sum_congr rfl
        intro i _
        have hiff : 8 * Riesz1.cyclicIndexDistance m i j ≤ Riesz1.cyclicIndexDistance m j i₀ ↔
            Riesz1.cyclicIndexDistance m i j ≤ Riesz1.cyclicIndexDistance m j i₀ / 8 := by omega
        simp only [hiff]
      _ = ∑ i : Fin (m : ℕ), ∑ r ∈ range (k + 1),
          if Riesz1.cyclicIndexDistance m j i = r then 1 else 0 := by
        apply sum_congr rfl
        intro i _
        have hs : Riesz1.cyclicIndexDistance m i j = Riesz1.cyclicIndexDistance m j i := by
          simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
        simp only [hs, sum_ite_eq, mem_range, Nat.lt_succ_iff]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro r _
        simp only [cyclicShell, card_filter]
  rw [hcount, sum_range_succ']
  have htwo (r : ℕ) (hr : r ∈ range k) : (cyclicShell m j (r + 1)).card = 2 :=
    card_cyclicShell_of_two_mul_lt j (by omega)
      (by have := mem_range.mp hr; omega)
  rw [sum_congr rfl htwo, card_cyclicShell_zero]
  simp only [sum_const, card_range, smul_eq_mul]
  change k * 2 + 1 = 2 * k + 1
  omega

/-- See Subsection 5.5 of the paper: the stated window-size bounds, including the
smallest allowed separation `R = 16`. -/
theorem window_size_bounds (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀) :
    5 ≤ (windowSize m j i₀ : ℕ) ∧
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 8 ≤ (windowSize m j i₀ : ℝ) ∧
      (windowSize m j i₀ : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 2 ∧
      4 * (windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
  have hc : (windowSize m j i₀ : ℕ) =
      2 * (Riesz1.cyclicIndexDistance m j i₀ / 8) + 1 := window_card m j i₀
  have hl : Riesz1.cyclicIndexDistance m j i₀ ≤ 8 * (windowSize m j i₀ : ℕ) := by omega
  have hu : 2 * (windowSize m j i₀ : ℕ) ≤ Riesz1.cyclicIndexDistance m j i₀ := by omega
  have hd : 2 * Riesz1.cyclicIndexDistance m j i₀ ≤ (m : ℕ) := by
    dsimp only [Riesz1.cyclicIndexDistance]
    have hj := j.isLt
    have hi := i₀.isLt
    unfold Nat.dist
    omega
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8), mul_comm]
    exact_mod_cast hl
  · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm]
    exact_mod_cast hu

/-- See Subsection 5.5 of the paper: the new cycle contains the active block and a
second block of at least the same size. -/
theorem two_windowSize_le_period (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀) :
    2 * (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ) := by
  have hn := (window_size_bounds m j i₀ hR).2.2.2
  exact le_min (by omega) (le_max_left _ _)

/-- See Subsection 5.5 of the paper: when the new period is not capped at the parent
period, its defining power is bounded by the new component size. -/
theorem power_le_windowPeriod_of_lt (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) (hcap : (windowPeriod s m j i₀ : ℕ) < (m : ℕ)) :
    (windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (windowPeriod s m j i₀ : ℝ) := by
  have hc : ⌈(windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ ≤
      (windowPeriod s m j i₀ : ℕ) := by
    change min (m : ℕ) (max (2 * (windowSize m j i₀ : ℕ))
      ⌈(windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊) < (m : ℕ) at hcap
    change ⌈(windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ ≤
      min (m : ℕ) (max (2 * (windowSize m j i₀ : ℕ))
        ⌈(windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊)
    omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast hc)

section InclusionExclusion

open IntervalBoundary

/-- See the proof of Proposition 5.15 in the paper: a positive-length interval is internal when its
right endpoint stays in the active block. This uses the existing internality
predicate, including its requirement on every label. -/
theorem isInternal_iff (m : ℕ+) {n : ℕ} (hn : n < (m : ℕ))
    (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) :
    IsInternal m n t ↔ t.1.val + (t.2.val + 1) ≤ n := by
  have ha := t.1.isLt
  have hr := t.2.isLt
  constructor
  · intro h
    have hstart : t.1 ∈ cyclicIndexInterval m t.1 (t.2.val + 1) := by
      rw [mem_cyclicIndexInterval_iff m _ _ (by omega), sub_self]
      simp
    have han := h t.1 hstart
    have hnowrap : t.1.val + (t.2.val + 1) ≤ (m : ℕ) := by
      by_contra hwrap
      let last : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by omega⟩
      have hlast : last ∈ cyclicIndexInterval m t.1 (t.2.val + 1) := by
        apply mem_image.mpr
        refine ⟨(m : ℕ) - 1 - t.1.val, mem_range.mpr (by omega), ?_⟩
        apply Fin.ext
        change (t.1.val + ((m : ℕ) - 1 - t.1.val)) % (m : ℕ) = (m : ℕ) - 1
        rw [show t.1.val + ((m : ℕ) - 1 - t.1.val) = (m : ℕ) - 1 by omega,
          Nat.mod_eq_of_lt (by omega)]
      have := h last hlast
      dsimp only [last] at this
      omega
    let last : Fin (m : ℕ) := ⟨t.1.val + t.2.val, by omega⟩
    have hlast : last ∈ cyclicIndexInterval m t.1 (t.2.val + 1) := by
      apply mem_image.mpr
      refine ⟨t.2.val, mem_range.mpr (by omega), ?_⟩
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    have := h last hlast
    dsimp only [last] at this
    omega
  · intro h j hj
    obtain ⟨k, hk, he⟩ := mem_image.mp hj
    have hk := mem_range.mp hk
    have hjv := congrArg Fin.val he
    simp only [Nat.mod_eq_of_lt (show t.1.val + k < (m : ℕ) by omega)] at hjv
    omega

/-- See the proof of Proposition 5.15 in the paper: short intervals are order-convex on an arc below half
the cycle. This is the no-wrap argument used in inclusion--exclusion. -/
theorem interval_convex_on_half (m : ℕ+) {n r : ℕ}
    (hn : 2 * n ≤ (m : ℕ)) (hr : 2 * r ≤ (m : ℕ))
    (a p q w : Fin (m : ℕ)) (hp : p.val < n) (hw : w.val < n)
    (hpq : p.val ≤ q.val) (hqw : q.val ≤ w.val)
    (hpm : p ∈ cyclicIndexInterval m a r) (hwm : w ∈ cyclicIndexInterval m a r) :
    q ∈ cyclicIndexInterval m a r := by
  rw [BoundaryEntries.mem_interval_active m hn hr a p hp] at hpm
  rw [BoundaryEntries.mem_interval_active m hn hr a w hw] at hwm
  rw [BoundaryEntries.mem_interval_active m hn hr a q (by omega)]
  split_ifs at * <;> omega

/-- See the proof of Proposition 5.15 in the paper: the preceding label belongs to an interval
exactly when that interval reaches the cyclic seam. -/
theorem predecessor_mem_interval_iff (m : ℕ+) (a : Fin (m : ℕ)) {r : ℕ}
    (hr : r ≤ (m : ℕ)) :
    (⟨(m : ℕ) - 1, by have := m.pos; omega⟩ : Fin (m : ℕ)) ∈
      cyclicIndexInterval m a r ↔ (m : ℕ) ≤ a.val + r := by
  rw [mem_cyclicIndexInterval_iff m _ _ hr, Fin.val_sub]
  have ha := a.isLt
  rw [show (m : ℕ) - a.val + ((m : ℕ) - 1) =
    ((m : ℕ) - 1 - a.val) + (m : ℕ) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/-- See the proof of Proposition 5.15 in the paper: inclusion--exclusion for a
single signed interval term. Both neighboring labels are in the parent cycle.
The active indices have their parent cyclic order. -/
theorem interval_inclusion_exclusion (m : ℕ+) {n : ℕ}
    (hn : 2 * (n + 1) ≤ (m : ℕ))
    (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) (i l : Fin n) (hil : i.val ≤ l.val) :
    let hnM : n ≤ (m : ℕ) := by omega
    let left : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by omega⟩
    let right : Fin (m : ℕ) := ⟨n, by omega⟩
    let T := cyclicIndexInterval m t.1 (t.2.val + 1)
    (if IsInternal m n t then
      (if i.castLE hnM ∈ T ∧ l.castLE hnM ∈ T then (1 : ℝ) else 0) else 0) =
      (if i.castLE hnM ∈ T ∧ l.castLE hnM ∈ T then (1 : ℝ) else 0) -
      (if left ∈ T ∧ l.castLE hnM ∈ T then (1 : ℝ) else 0) -
      (if i.castLE hnM ∈ T ∧ right ∈ T then (1 : ℝ) else 0) +
      (if left ∈ T ∧ right ∈ T then (1 : ℝ) else 0) := by
  dsimp only
  have ha := t.1.isLt
  have hr := t.2.isLt
  have hi := i.isLt
  have hl := l.isLt
  simp_rw [isInternal_iff m (n := n) (by omega) t,
    predecessor_mem_interval_iff m t.1 (r := t.2.val + 1) (by omega)]
  simp_rw [BoundaryEntries.mem_interval_active m (r := t.2.val + 1) hn (by omega) t.1 (i.castLE (by omega))
    (by simp only [Fin.val_castLE]; omega)]
  simp_rw [BoundaryEntries.mem_interval_active m (r := t.2.val + 1) hn (by omega) t.1 (l.castLE (by omega))
    (by simp only [Fin.val_castLE]; omega)]
  simp_rw [BoundaryEntries.mem_interval_active m (r := t.2.val + 1) hn (by omega) t.1
    (⟨n, by omega⟩ : Fin (m : ℕ)) (Nat.lt_succ_self n)]
  simp only [Fin.val_castLE]
  split_ifs <;> (first | omega | ring)

/-- See the proof of Proposition 5.15 in the paper: the exact internal matrix
entry from four parent entries. Coefficients may have either sign, so this
applies directly to the parent reference error. -/
theorem internalMatrix_inclusion_exclusion (m : ℕ+) {n : ℕ}
    (hn : 2 * (n + 1) ≤ (m : ℕ))
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (i l : Fin n) (hil : i.val ≤ l.val) :
    let hnM : n ≤ (m : ℕ) := by omega
    let E := intervalMatrix m m le_rfl A
    let left : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by omega⟩
    let right : Fin (m : ℕ) := ⟨n, by omega⟩
    internalMatrix m n hnM A i l =
      E (i.castLE hnM) (l.castLE hnM) - E left (l.castLE hnM) -
        E (i.castLE hnM) right + E left right := by
  dsimp only
  simp only [internalMatrix, intervalMatrix, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  have h := interval_inclusion_exclusion m hn t i l hil
  dsimp only at h
  have hrank (p q : Fin (m : ℕ)) :
      rankOne (trace m m le_rfl t.1 (t.2.val + 1)) p q =
        if p ∈ cyclicIndexInterval m t.1 (t.2.val + 1) ∧
          q ∈ cyclicIndexInterval m t.1 (t.2.val + 1) then (1 : ℝ) else 0 := by
    simp only [rankOne, trace, mem_filter, mem_univ, true_and, Fin.castLE_refl]
  have hrank' : rankOne (trace m n (by omega) t.1 (t.2.val + 1)) i l =
      if i.castLE (by omega) ∈ cyclicIndexInterval m t.1 (t.2.val + 1) ∧
        l.castLE (by omega) ∈ cyclicIndexInterval m t.1 (t.2.val + 1)
          then (1 : ℝ) else 0 := by
    simp only [rankOne, trace, mem_filter, mem_univ, true_and]
  simp_rw [hrank, hrank']
  rw [show (if IsInternal m n t then A t *
      (if i.castLE (by omega) ∈ cyclicIndexInterval m t.1 (t.2.val + 1) ∧
        l.castLE (by omega) ∈ cyclicIndexInterval m t.1 (t.2.val + 1) then 1 else 0) else 0) =
      A t * (if IsInternal m n t then
        (if i.castLE (by omega) ∈ cyclicIndexInterval m t.1 (t.2.val + 1) ∧
          l.castLE (by omega) ∈ cyclicIndexInterval m t.1 (t.2.val + 1) then 1 else 0)
        else 0) by split_ifs <;> ring, h]
  ring

/-- The crossing part of a signed interval matrix is exactly the three
endpoint terms. This is the boundary-row identity in the proof of Proposition 5.15, before the change of reference period. -/
theorem boundaryMatrix_inclusion_exclusion (m : ℕ+) {n : ℕ}
    (hn : 2 * (n + 1) ≤ (m : ℕ))
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (i l : Fin n) (hil : i.val ≤ l.val) :
    let hnM : n ≤ (m : ℕ) := by omega
    let E := intervalMatrix m m le_rfl A
    let left : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by omega⟩
    let right : Fin (m : ℕ) := ⟨n, by omega⟩
    boundaryMatrix m n hnM A i l =
      E left (l.castLE hnM) + E (i.castLE hnM) right - E left right := by
  dsimp only
  have h := internalMatrix_inclusion_exclusion m hn A i l hil
  dsimp only at h
  have hp := congrFun (congrFun (internal_add_boundary m n (by omega) A) i) l
  have he : intervalMatrix m n (by omega) A i l =
      intervalMatrix m m le_rfl A (i.castLE (by omega)) (l.castLE (by omega)) := by
    simp only [intervalMatrix, rankOne, trace, mem_filter, mem_univ, true_and,
      Fin.castLE_refl]
  simp only [Matrix.add_apply] at hp
  rw [he] at hp
  linarith only [hp, h]

/-- Every distance in the four-entry identity is at least the distance of the
two ordered active indices (the proof of Proposition 5.15). -/
theorem endpoint_distances (m : ℕ+) {n : ℕ} (hn : 4 * n ≤ (m : ℕ))
    (i l : Fin n) (hil : i.val ≤ l.val) :
    let hnM : n ≤ (m : ℕ) := by omega
    let left : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by have := m.pos; omega⟩
    let right : Fin (m : ℕ) := ⟨n, by have := l.isLt; omega⟩
    l.val - i.val ≤ Riesz1.cyclicIndexDistance m (i.castLE hnM) (l.castLE hnM) ∧
      l.val - i.val ≤ Riesz1.cyclicIndexDistance m left (l.castLE hnM) ∧
      l.val - i.val ≤ Riesz1.cyclicIndexDistance m (i.castLE hnM) right ∧
      l.val - i.val ≤ Riesz1.cyclicIndexDistance m left right := by
  have hi := i.isLt
  have hl := l.isLt
  dsimp only [Riesz1.cyclicIndexDistance, Nat.dist, Fin.val_castLE]
  omega

/-- See the proof of Proposition 5.15 in the paper, internal entry comparison
at the parent period. The signed matrix and its bound are explicit internal
inputs. -/
theorem internalMatrix_entry_bound_internal (m : ℕ+) {n : ℕ}
    (hn : 4 * n ≤ (m : ℕ)) (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hE : ∀ p w, |intervalMatrix m m le_rfl A p w| ≤
      C * (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-q))
    (i l : Fin n) (hil : i.val ≤ l.val) :
    |internalMatrix m n (by omega) A i l| ≤
      4 * C * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-q) := by
  have hi := i.isLt
  have hl := l.isLt
  let E := intervalMatrix m m le_rfl A
  let left : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by omega⟩
  let right : Fin (m : ℕ) := ⟨n, by omega⟩
  have hb (p w : Fin (m : ℕ))
      (hd : l.val - i.val ≤ Riesz1.cyclicIndexDistance m p w) :
      |E p w| ≤ C * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-q) := by
    apply (hE p w).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact_mod_cast (Nat.add_le_add_left hd 1)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := endpoint_distances m hn i l hil
  have he := internalMatrix_inclusion_exclusion m (n := n) (by omega) A i l hil
  dsimp only at he
  rw [he]
  have ha := abs_add_le (E (i.castLE (by omega)) (l.castLE (by omega)) -
    E left (l.castLE (by omega)) - E (i.castLE (by omega)) right) (E left right)
  have hs := abs_sub (E (i.castLE (by omega)) (l.castLE (by omega)) -
    E left (l.castLE (by omega))) (E (i.castLE (by omega)) right)
  have ht := abs_sub (E (i.castLE (by omega)) (l.castLE (by omega)))
    (E left (l.castLE (by omega)))
  have hb₁ := hb _ _ h₁
  have hb₂ := hb _ _ h₂
  have hb₃ := hb _ _ h₃
  have hb₄ := hb _ _ h₄
  dsimp only [E, left, right] at *
  linarith only [ha, hs, ht, hb₁, hb₂, hb₃, hb₄]

end InclusionExclusion

section Construction

open IntervalBoundary BoundaryEntries

variable {Ω : Type*}

/-- The existing reference coefficient family assembles to the reference Hessian. This is the coefficient representation used in the proof of Proposition 5.15. -/
theorem intervalMatrix_referenceWeight (s : Riesz1.RieszExponent) (m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) :
    intervalMatrix m m le_rfl (referenceWeight s m hm K) =
      (2 : ℝ) • referenceIntervalMatrix s m hm K := by
  ext i l
  rw [Matrix.smul_apply, smul_eq_mul, GlobalReferenceErrorInternal.reference_fin_lengths]
  simp only [intervalMatrix, Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro r _
  simp only [referenceWeight, rankOne, trace, mem_filter, mem_univ, true_and,
    Fin.castLE_refl]
  have hcast : (⟨(r.val + 1) % (m : ℕ), Nat.mod_lt _ m.pos⟩ : Fin (m : ℕ)) =
      (↑(r.val + 1) : Fin (m : ℕ)) := Fin.ext rfl
  rw [hcast]
  split_ifs <;> simp_all

/-- See the proof of Proposition 5.15 in the paper: restriction changes only the component labels. Its
coefficients and its parent cycle are unchanged. -/
theorem intervalMatrix_restrict (m : ℕ+) (n : ℕ) (hn : n ≤ (m : ℕ))
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (i l : Fin n) :
    intervalMatrix m n hn A i l =
      intervalMatrix m m le_rfl A (i.castLE hn) (l.castLE hn) := by
  simp only [intervalMatrix, rankOne, trace, mem_filter, mem_univ, true_and,
    Fin.castLE_refl]

/-- See the proof of Proposition 5.15 in the paper: retained reference coefficients are exactly
the existing reference internal block, including its cutoff and normalization. -/
theorem internalMatrix_referenceWeight (s : Riesz1.RieszExponent) (m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (m : ℕ)) :
    internalMatrix m n hn (referenceWeight s m hm K) = referenceInternal s m hm K n hn := by
  ext i l
  have hsplit := congrFun (congrFun (internal_add_boundary m n hn
    (referenceWeight s m hm K)) i) l
  rw [← referenceCrossing_eq_boundaryMatrix s m hm K n hn] at hsplit
  rw [intervalMatrix_restrict, intervalMatrix_referenceWeight] at hsplit
  have href := referenceInternal_add_crossing s m hm K n hn i l
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hsplit
  linarith only [hsplit, href]

/-- See the proof of Proposition 5.15 in the paper: internal retention is linear for signed errors. -/
theorem internalMatrix_sub (m : ℕ+) (n : ℕ) (hn : n ≤ (m : ℕ))
    (A B : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) :
    internalMatrix m n hn (A - B) = internalMatrix m n hn A - internalMatrix m n hn B := by
  ext i l
  simp only [internalMatrix, Matrix.sub_apply, ← sum_sub_distrib, Pi.sub_apply]
  apply sum_congr rfl
  intro t _
  split_ifs <;> ring

/-- See the proof of Proposition 5.15 in the paper: the interval matrix is linear in signed coefficients. -/
theorem intervalMatrix_sub (m : ℕ+) (n : ℕ) (hn : n ≤ (m : ℕ))
    (A B : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) :
    intervalMatrix m n hn (A - B) = intervalMatrix m n hn A - intervalMatrix m n hn B := by
  ext i l
  simp only [intervalMatrix, Matrix.sub_apply, Pi.sub_apply, sub_mul, sum_sub_distrib]

/-- See the proof of Proposition 5.15 in the paper: the interval API in the product-of-indicators convention
used by the periodized matrix bounds. -/
theorem intervalMatrix_entries (m : ℕ+)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (i l : Fin (m : ℕ)) :
    intervalMatrix m m le_rfl A i l = ∑ a, ∑ r,
      A (a, r) * (if i ∈ cyclicIndexInterval m a (r.val + 1) then 1 else 0) *
        (if l ∈ cyclicIndexInterval m a (r.val + 1) then 1 else 0) := by
  simp only [intervalMatrix, Fintype.sum_prod_type, rankOne, trace,
    mem_filter, mem_univ, true_and, Fin.castLE_refl]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp_all

/-- See the proof of Proposition 5.15 in the paper, parent-period part of the
internal entry comparison, derived from the assumptions.
The same measurable nonnegative coefficient witness works for every initial
subinterval. -/
theorem parent_internal_comparison [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ) (hC : 1 ≤ C)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧ ∀ᵐ x ∂ν,
      (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x ∧
      ∀ (n₀ : ℕ+) (hn₀ : 4 * (n₀ : ℕ) ≤ (m : ℕ)) (i l : Fin (n₀ : ℕ)), i.val ≤ l.val →
        |internalMatrix m n₀ (by omega) (fun t => A t x) i l -
          referenceInternal s m hm K n₀ (by omega) i l| ≤
        4 * (C * (n : ℝ) ^ (κ * ε)) *
          (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
  obtain ⟨a, ha, hrep⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  refine ⟨fun t => a t.1 t.2, fun t => ha t.1 t.2, ?_⟩
  filter_upwards [hrep, periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε
    (by linarith : 0 ≤ C) M hM]
    with x hx he
  let A := fun t : Fin (m : ℕ) × Fin ((m : ℕ) / 2) => a t.1 t.2 x
  have hmatrix : intervalMatrix m m le_rfl A = M x := by
    ext i l
    rw [intervalMatrix_entries]
    exact (hx.2 i l).symm
  refine ⟨fun t => (hx.1 t.1 t.2).1, hmatrix, fun n₀ hn₀ i l hil => ?_⟩
  let B := A - referenceWeight s m hm K
  have hb (p w : Fin (m : ℕ)) : |intervalMatrix m m le_rfl B p w| ≤
      (C * (n : ℝ) ^ (κ * ε)) * (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-(1 + s.val / 2)) := by
    rw [show intervalMatrix m m le_rfl B = M x - (2 : ℝ) • referenceIntervalMatrix s m hm K by
      rw [show B = A - referenceWeight s m hm K from rfl,
        intervalMatrix_sub, hmatrix, intervalMatrix_referenceWeight], Matrix.sub_apply]
    simpa only [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using he p w
  have h := internalMatrix_entry_bound_internal m hn₀ B (C * (n : ℝ) ^ (κ * ε))
    (1 + s.val / 2) (mul_nonneg (by linarith) (by positivity))
    (by linarith [s.property.1]) hb i l hil
  rw [show B = A - referenceWeight s m hm K from rfl,
    internalMatrix_sub, internalMatrix_referenceWeight, Matrix.sub_apply] at h
  simpa only [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using h

/-- See Subsection 5.5 of the paper: the localized matrix in coordinates where the
retained parent interval is the first `n₀` labels. The coefficient family
is explicit. Its internal matrix is the existing `IntervalBoundary.internalMatrix`.
The exterior entries are the reference at the new period. -/
def matrix (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ) :
    Ω → Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ :=
  fun x i l => if hi : i.val < (n₀ : ℕ) then
    if hl : l.val < (n₀ : ℕ) then
      internalMatrix m n₀ hn (fun t => A t x) ⟨i.val, hi⟩ ⟨l.val, hl⟩ +
        referenceCrossing s m₀ hm₀ K n₀ hn₀ ⟨i.val, hi⟩ ⟨l.val, hl⟩
    else 2 * referenceIntervalMatrix s m₀ hm₀ K i l
  else 2 * referenceIntervalMatrix s m₀ hm₀ K i l

/-- See Subsection 5.5 of the paper: the exact boundary remainder for a relabelled
parent principal matrix. -/
def remainder (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (P : Ω → Matrix (Fin (n₀ : ℕ)) (Fin (n₀ : ℕ)) ℝ) :
    Ω → Matrix (Fin (n₀ : ℕ)) (Fin (n₀ : ℕ)) ℝ :=
  fun x => P x - internalMatrix m n₀ hn (fun t => A t x) -
    referenceCrossing s m₀ hm₀ K n₀ hn₀

/-- The exterior blocks in Subsection 5.5 agree exactly with the reference. -/
theorem matrix_exterior (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (x : Ω) (i l : Fin (m₀ : ℕ)) (h : (n₀ : ℕ) ≤ i.val ∨ (n₀ : ℕ) ≤ l.val) :
    matrix s m m₀ n₀ hm₀ hn hn₀ K A x i l =
      ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) i l := by
  simp only [matrix, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> first | rfl | omega

/-- The internal and crossing parts are the actual principal block of the
localized matrix (Subsection 5.5). -/
theorem matrix_active (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (x : Ω) (i l : Fin (n₀ : ℕ)) :
    matrix s m m₀ n₀ hm₀ hn hn₀ K A x (i.castLE hn₀) (l.castLE hn₀) =
      internalMatrix m n₀ hn (fun t => A t x) i l +
        referenceCrossing s m₀ hm₀ K n₀ hn₀ i l := by
  simp only [matrix, Fin.val_castLE, i.isLt, l.isLt, dite_true]

/-- The principal reference error is exactly the difference of the two
internal matrices (the proof of Proposition 5.15). This keeps the new
reference period explicit. -/
theorem matrix_reference_error (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (x : Ω) (i l : Fin (n₀ : ℕ)) :
    matrix s m m₀ n₀ hm₀ hn hn₀ K A x (i.castLE hn₀) (l.castLE hn₀) -
      ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) (i.castLE hn₀) (l.castLE hn₀) =
      internalMatrix m n₀ hn (fun t => A t x) i l -
        referenceInternal s m₀ hm₀ K n₀ hn₀ i l := by
  rw [matrix_active]
  have he := referenceInternal_add_crossing s m₀ hm₀ K n₀ hn₀ i l
  simp only [Matrix.smul_apply, smul_eq_mul]
  linarith only [he]

/-- Adding the remainder restores the parent principal operator, with the
positive sign required by the proof of Proposition 5.15. -/
theorem matrix_add_remainder (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (P : Ω → Matrix (Fin (n₀ : ℕ)) (Fin (n₀ : ℕ)) ℝ)
    (x : Ω) (i l : Fin (n₀ : ℕ)) :
    matrix s m m₀ n₀ hm₀ hn hn₀ K A x (i.castLE hn₀) (l.castLE hn₀) +
      remainder s m m₀ n₀ hm₀ hn hn₀ K A P x i l = P x i l := by
  rw [matrix_active]
  simp only [remainder, Matrix.sub_apply]
  ring

end Construction

end Riesz2.LocalizedMatrix

end
