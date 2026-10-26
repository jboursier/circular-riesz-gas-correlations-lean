/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicIntervalPairCount

/-!
# Boundary traces of short cyclic intervals

For a block of at most half a cycle, a noninternal cyclic interval of at most
half a cycle has an empty, prefix, suffix or full trace. Finite rank-one sums
therefore group into the three boundary families. The algebra works over any
semiring, including extended nonnegative coefficients before finiteness is known.
This is the combinatorial argument of Subsection 4.4.
-/

@[expose] public section
noncomputable section
open Finset
namespace Riesz2.IntervalBoundary

/-- The first `k` labels of a block of size `n`. -/
def initialSegment (n k : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < k)
/-- Labels of the block starting at the zero-based label `k`. -/
def terminalSegment (n k : ℕ) : Finset (Fin n) := univ.filter (fun i => k ≤ i.val)
/-- Restriction of the literal cyclic interval to the active block. -/
def trace (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (a : Fin (N : ℕ)) (r : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => Fin.castLE hn i ∈ cyclicIndexInterval N a r)

/-- Membership in the trace in terms of its forward residue. -/
theorem mem_trace (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (a : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ)) (i : Fin n) :
    i ∈ trace N n hn a r ↔ (i.val + (N : ℕ) - a.val) % (N : ℕ) < r := by
  simp only [trace, mem_filter, mem_univ, true_and,
    mem_cyclicIndexInterval_iff N _ _ hr, Fin.val_sub, Fin.val_castLE]
  rw [show (N : ℕ) - a.val + i.val = i.val + (N : ℕ) - a.val by omega]

/-- See Subsection 4.4 of the paper: the four possible boundary traces, including
the empty trace and the singleton active block. -/
theorem boundary_trace_cases (N : ℕ+) {n r : ℕ} (hn : 1 ≤ n)
    (hnN : 2 * n ≤ (N : ℕ)) (hr : 1 ≤ r) (hrN : 2 * r ≤ (N : ℕ))
    (a : Fin (N : ℕ))
    (hb : ¬ ∀ j ∈ cyclicIndexInterval N a r, j.val < n) :
    trace N n (by omega) a r = ∅ ∨
      (∃ k ∈ Ico 1 n, trace N n (by omega) a r = initialSegment n k) ∨
      (∃ k ∈ Ico 1 n, trace N n (by omega) a r = terminalSegment n k) ∨
      trace N n (by omega) a r = univ := by
  have ha := a.isLt
  have hm (i : Fin n) : i ∈ trace N n (by omega) a r ↔
      (if a.val ≤ i.val then i.val - a.val else i.val + (N : ℕ) - a.val) < r := by
    rw [mem_trace N n (by omega) a r (by omega)]
    have hi := i.isLt
    by_cases hai : a.val ≤ i.val
    · rw [ite_eq_left hai, show i.val + (N : ℕ) - a.val = (i.val - a.val) + (N : ℕ) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right hai, Nat.mod_eq_of_lt (by omega)]
  by_cases hw : (N : ℕ) < a.val + r
  · have han : n ≤ a.val := by omega
    have he : trace N n (by omega) a r = initialSegment n (min n (a.val + r - (N : ℕ))) := by
      ext i
      rw [hm]
      have hi := i.isLt
      simp only [initialSegment, mem_filter, mem_univ, true_and, lt_min_iff]
      rw [ite_eq_right (by omega)]
      omega
    by_cases hk : a.val + r - (N : ℕ) < n
    · right; left
      refine ⟨a.val + r - (N : ℕ), mem_Ico.mpr ⟨by omega, hk⟩, ?_⟩
      simpa only [min_eq_right hk.le] using he
    · right; right; right
      rw [he, min_eq_left (by omega)]
      ext i
      simp [initialSegment]
  · have hw' : a.val + r ≤ (N : ℕ) := by omega
    by_cases han : n ≤ a.val
    · left
      ext i
      rw [hm]
      have hi := i.isLt
      simp only [Finset.notMem_empty, iff_false]
      rw [ite_eq_right (by omega)]
      omega
    · have har : n < a.val + r := by
        by_contra h
        apply hb
        intro j hj
        rw [mem_cyclicIndexInterval_iff N _ _ (by omega)] at hj
        rw [Fin.val_sub] at hj
        have hjN := j.isLt
        by_cases haj : a.val ≤ j.val
        · rw [show (N : ℕ) - a.val + j.val = (j.val - a.val) + (N : ℕ) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at hj
          omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hj
          omega
      have he : trace N n (by omega) a r = terminalSegment n a.val := by
        ext i
        rw [hm]
        have hi := i.isLt
        simp only [terminalSegment, mem_filter, mem_univ, true_and]
        split_ifs <;> omega
      by_cases ha0 : a.val = 0
      · right; right; right
        rw [he, ha0]
        ext i
        simp [terminalSegment]
      · right; right; left
        exact ⟨a.val, mem_Ico.mpr ⟨by omega, by omega⟩, he⟩

private theorem initialSegment_inj {n k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    initialSegment n k = initialSegment n l ↔ k = l := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hm : (⟨k, by omega⟩ : Fin n) ∈ initialSegment n l := by
      simp [initialSegment, hlt]
    rw [← h] at hm
    simp [initialSegment] at hm
  · have hm : (⟨l, by omega⟩ : Fin n) ∈ initialSegment n k := by
      simp [initialSegment, hlt]
    rw [h] at hm
    simp [initialSegment] at hm

private theorem terminalSegment_inj {n k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    terminalSegment n k = terminalSegment n l ↔ k = l := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hm : (⟨k, by omega⟩ : Fin n) ∈ terminalSegment n k := by
      simp [terminalSegment]
    rw [h] at hm
    simp only [terminalSegment, mem_filter, mem_univ, true_and] at hm
    omega
  · have hm : (⟨l, by omega⟩ : Fin n) ∈ terminalSegment n l := by
      simp [terminalSegment]
    rw [← h] at hm
    simp only [terminalSegment, mem_filter, mem_univ, true_and] at hm
    omega

private theorem initialSegment_ne_terminalSegment {n k l : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hl : 1 ≤ l) : initialSegment n k ≠ terminalSegment n l := by
  intro h
  have hm : (⟨0, by omega⟩ : Fin n) ∈ initialSegment n k := by
    simp [initialSegment]; omega
  rw [h] at hm
  simp only [terminalSegment, mem_filter, mem_univ, true_and] at hm
  omega

private theorem initialSegment_ne_univ {n k : ℕ} (hk : k < n) : initialSegment n k ≠ univ := by
  intro h
  have hm : (⟨k, hk⟩ : Fin n) ∈ initialSegment n k := h ▸ mem_univ _
  simp [initialSegment] at hm

private theorem terminalSegment_ne_univ {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    terminalSegment n k ≠ univ := by
  intro h
  have hm : (⟨0, by omega⟩ : Fin n) ∈ terminalSegment n k := h ▸ mem_univ _
  simp only [terminalSegment, mem_filter, mem_univ, true_and] at hm
  omega

variable {R : Type*} [Semiring R]

/-- A rank-one interval term over a semiring. -/
def rankOne {n : ℕ} (K : Finset (Fin n)) (i j : Fin n) : R :=
  if i ∈ K ∧ j ∈ K then 1 else 0

/-- The contribution of a boundary trace is the sum of its unique prefix,
suffix, or full-block group. Empty traces contribute zero. -/
theorem rankOne_boundary_groups {n : ℕ} (hn : 1 ≤ n) (K : Finset (Fin n))
    (hK : K = ∅ ∨ (∃ k ∈ Ico 1 n, K = initialSegment n k) ∨
      (∃ k ∈ Ico 1 n, K = terminalSegment n k) ∨ K = univ)
    (i j : Fin n) :
    rankOne (R := R) K i j =
      (∑ k ∈ Ico 1 n, if K = initialSegment n k then rankOne (initialSegment n k) i j else 0) +
      (∑ k ∈ Ico 1 n, if K = terminalSegment n k then rankOne (terminalSegment n k) i j else 0) +
      (if K = univ then 1 else 0) := by
  classical
  rcases hK with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | rfl
  · have hp (k) (hk : k ∈ Ico 1 n) : (∅ : Finset (Fin n)) ≠ initialSegment n k := by
      intro h
      have hkn := mem_Ico.mp hk
      have hm : (⟨0, by omega⟩ : Fin n) ∈ initialSegment n k := by
        simp only [initialSegment, mem_filter, mem_univ, true_and]; omega
      rw [← h] at hm
      exact notMem_empty _ hm
    have hs (k) (hk : k ∈ Ico 1 n) : (∅ : Finset (Fin n)) ≠ terminalSegment n k := by
      intro h
      have hm : (⟨k, (mem_Ico.mp hk).2⟩ : Fin n) ∈ terminalSegment n k := by
        simp [terminalSegment]
      rw [← h] at hm
      exact notMem_empty _ hm
    have hu : (∅ : Finset (Fin n)) ≠ univ := by
      intro h
      have hm : (⟨0, by omega⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := h ▸ mem_univ _
      exact notMem_empty _ hm
    simp only [rankOne, notMem_empty, and_self, ↓reduceIte, hu]
    rw [sum_eq_zero (fun k hk => ite_eq_right (hp k hk)),
      sum_eq_zero (fun k hk => ite_eq_right (hs k hk))]
    simp
  · have hkn := mem_Ico.mp hk
    have hp (l) (hl : l ∈ Ico 1 n) :
        initialSegment n k = initialSegment n l ↔ k = l :=
      initialSegment_inj (by omega) (by have := mem_Ico.mp hl; omega)
    have hs (l) (hl : l ∈ Ico 1 n) :
        initialSegment n k ≠ terminalSegment n l :=
      initialSegment_ne_terminalSegment hkn.1 hkn.2.le (mem_Ico.mp hl).1
    rw [sum_congr rfl (fun l hl => if_congr (hp l hl) rfl rfl),
      sum_eq_zero (fun l hl => ite_eq_right (hs l hl)), ite_eq_right (initialSegment_ne_univ hkn.2)]
    simp [hk]
  · have hkn := mem_Ico.mp hk
    have hs (l) (hl : l ∈ Ico 1 n) :
        terminalSegment n k = terminalSegment n l ↔ k = l :=
      terminalSegment_inj (by omega) (by have := mem_Ico.mp hl; omega)
    have hp (l) (hl : l ∈ Ico 1 n) :
        terminalSegment n k ≠ initialSegment n l :=
      (initialSegment_ne_terminalSegment (mem_Ico.mp hl).1 (by have := mem_Ico.mp hl; omega)
        hkn.1).symm
    rw [sum_eq_zero (fun l hl => ite_eq_right (hp l hl)),
      sum_congr rfl (fun l hl => if_congr (hs l hl) rfl rfl),
      ite_eq_right (terminalSegment_ne_univ hn hkn.1)]
    simp [hk]
  · have hp (k) (hk : k ∈ Ico 1 n) : (univ : Finset (Fin n)) ≠ initialSegment n k :=
      (initialSegment_ne_univ (mem_Ico.mp hk).2).symm
    have hs (k) (hk : k ∈ Ico 1 n) : (univ : Finset (Fin n)) ≠ terminalSegment n k :=
      (terminalSegment_ne_univ hn (mem_Ico.mp hk).1).symm
    rw [sum_eq_zero (fun k hk => ite_eq_right (hp k hk)),
      sum_eq_zero (fun k hk => ite_eq_right (hs k hk))]
    simp [rankOne]

/-- Internal finite grouping identity, for arbitrary semiring weights. -/
theorem weighted_boundary_groups {ι : Type*} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (A : ι → R) (K : ι → Finset (Fin n)) (B : ι → Prop) [DecidablePred B]
    (hK : ∀ t, ¬ B t → K t = ∅ ∨ (∃ k ∈ Ico 1 n, K t = initialSegment n k) ∨
      (∃ k ∈ Ico 1 n, K t = terminalSegment n k) ∨ K t = univ)
    (i j : Fin n) :
    (∑ t, if B t then 0 else A t * rankOne (K t) i j) =
      (∑ k ∈ Ico 1 n,
        (∑ t, if B t then 0 else if K t = initialSegment n k then A t else 0) *
          rankOne (initialSegment n k) i j) +
      (∑ k ∈ Ico 1 n,
        (∑ t, if B t then 0 else if K t = terminalSegment n k then A t else 0) *
          rankOne (terminalSegment n k) i j) +
      (∑ t, if B t then 0 else if K t = univ then A t else 0) := by
  classical
  simp_rw [sum_mul]
  rw [sum_comm (s := Ico 1 n) (t := univ), sum_comm (s := Ico 1 n) (t := univ),
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases ht : B t
  · simp only [ht, ↓reduceIte, zero_mul, sum_const_zero, add_zero]
  · simp only [ht, ↓reduceIte]
    have h := congrArg (fun z : R => A t * z) (rankOne_boundary_groups hn (K t) (hK t ht) i j)
    simpa only [mul_add, mul_sum, mul_ite, mul_zero, mul_one, ite_mul, zero_mul] using h

/-- A short interval is internal when every one of its labels is active. -/
def IsInternal (N : ℕ+) (n : ℕ) (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) : Prop :=
  ∀ j ∈ cyclicIndexInterval N t.1 (t.2.val + 1), j.val < n

/-- The active interval matrix for an arbitrary coefficient family. -/
def intervalMatrix (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ∑ t, A t * rankOne (trace N n hn t.1 (t.2.val + 1)) i j

/-- The internal terms in the active interval matrix. -/
def internalMatrix (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) : Matrix (Fin n) (Fin n) R := by
  classical
  exact fun i j => ∑ t, if IsInternal N n t then
    A t * rankOne (trace N n hn t.1 (t.2.val + 1)) i j else 0

/-- The boundary terms in the active interval matrix. -/
def boundaryMatrix (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) : Matrix (Fin n) (Fin n) R := by
  classical
  exact fun i j => ∑ t, if IsInternal N n t then 0 else
    A t * rankOne (trace N n hn t.1 (t.2.val + 1)) i j

/-- The coefficient of a proper prefix of length `k`. -/
def prefixCoefficient (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) (k : ℕ) : R := by
  classical
  exact ∑ t, if IsInternal N n t then 0 else
    if trace N n hn t.1 (t.2.val + 1) = initialSegment n k then A t else 0

/-- The coefficient of a proper suffix starting at the zero-based label `k`. -/
def suffixCoefficient (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) (k : ℕ) : R := by
  classical
  exact ∑ t, if IsInternal N n t then 0 else
    if trace N n hn t.1 (t.2.val + 1) = terminalSegment n k then A t else 0

/-- The coefficient of the full active block. -/
def fullCoefficient (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) : R := by
  classical
  exact ∑ t, if IsInternal N n t then 0 else
    if trace N n hn t.1 (t.2.val + 1) = univ then A t else 0

/-- See Subsection 4.4 of the paper: exact boundary grouping, for any coefficient family.
The two sums index proper prefix lengths and zero-based proper suffix starts.
In particular both sums are empty when the active block is a singleton. -/
theorem boundary_representation (N : ℕ+) {n : ℕ} (hn : 1 ≤ n)
    (hhalf : 2 * n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) (i j : Fin n) :
    boundaryMatrix N n (by omega) A i j =
      (∑ k ∈ Ico 1 n, prefixCoefficient N n (by omega) A k *
        rankOne (initialSegment n k) i j) +
      (∑ k ∈ Ico 1 n, suffixCoefficient N n (by omega) A k *
        rankOne (terminalSegment n k) i j) + fullCoefficient N n (by omega) A := by
  classical
  apply weighted_boundary_groups hn A
    (fun t => trace N n (by omega) t.1 (t.2.val + 1)) (IsInternal N n) _ i j
  intro t ht
  exact boundary_trace_cases N hn hhalf (by omega) (by have := t.2.isLt; omega) t.1 ht

/-- Internal and boundary terms partition the full active matrix. -/
theorem internal_add_boundary (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → R) :
    internalMatrix N n hn A + boundaryMatrix N n hn A = intervalMatrix N n hn A := by
  classical
  ext i j
  simp only [Matrix.add_apply, internalMatrix, boundaryMatrix, intervalMatrix]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  split_ifs <;> simp

end Riesz2.IntervalBoundary
