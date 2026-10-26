/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart3

/-!
# Internal interval transport for the physical core

The internal intervals in a half-window have the same ordinary endpoints
at the physical and reference periods. This supplies the finite-family
assembly required by the proof of Lemma 5.4.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore.Internal

/-- Internal short intervals in a half-window are exactly the nonwrapping
intervals whose right endpoint lies in that window. -/
theorem internal_iff_end_le (N : ℕ+) (n : ℕ) (hn : 2 * n ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
    IntervalBoundary.IsInternal N n (i, r) ↔ i.val + r.val + 1 ≤ n := by
  have hr : 2 * (r.val + 1) ≤ (N : ℕ) := by have := r.isLt; omega
  constructor
  · intro hi
    exact (internal_endpoints N n hn i (r.val + 1) (by omega) hr hi).2
  · intro hi j hj
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hj
    have ha' := Finset.mem_range.mp ha
    change a < r.val + 1 at ha'
    have he' := congrArg Fin.val he
    change (i.val + a) % (N : ℕ) = j.val at he'
    simp only [Nat.mod_eq_of_lt (show i.val + a < (N : ℕ) by omega)] at he'
    omega

/-- An internal interval has the same active-coordinate membership at every
period containing the half-window. -/
theorem internal_mem_iff (N : ℕ+) (n : ℕ) (hn : 2 * n ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2))
    (hi : IntervalBoundary.IsInternal N n (i, r)) (a : Fin n) :
    a.castLE (by omega : n ≤ (N : ℕ)) ∈ cyclicIndexInterval N i (r.val + 1) ↔
      i.val ≤ a.val ∧ a.val < i.val + r.val + 1 := by
  have he := (internal_iff_end_le N n hn i r).mp hi
  have h := BoundaryEntries.mem_interval_active N hn
    (by have := r.isLt; omega : 2 * (r.val + 1) ≤ (N : ℕ))
    i (a.castLE (by omega)) (by exact a.isLt)
  simpa only [Fin.val_castLE, ite_eq_left (show i.val < n by omega), Nat.add_assoc] using h

/-- Relabel the complete internal family by its two ordinary active indices.
The result includes the interval of length `n` when the window is exactly
half a cycle. No antipodal term is discarded. -/
theorem internal_sum_reindex {R : Type*} [AddCommMonoid R]
    (N : ℕ+) (n : ℕ) (hn : 2 * n ≤ (N : ℕ))
    (f : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → R) :
    (∑ i, ∑ r, if IntervalBoundary.IsInternal N n (i, r) then f i r else 0) =
      ∑ i : Fin n, ∑ r : Fin n, if _h : i.val + r.val + 1 ≤ n then
        f ⟨i.val, by omega⟩ ⟨r.val, by omega⟩ else 0 := by
  let S := Finset.univ.filter (fun t : Fin (N : ℕ) × Fin ((N : ℕ) / 2) =>
    IntervalBoundary.IsInternal N n t)
  let T := Finset.univ.filter (fun t : Fin n × Fin n => t.1.val + t.2.val + 1 ≤ n)
  have hS (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) :
      t ∈ S ↔ t.1.val + t.2.val + 1 ≤ n := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using
      internal_iff_end_le N n hn t.1 t.2
  have hT (t : Fin n × Fin n) : t ∈ T ↔ t.1.val + t.2.val + 1 ≤ n := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  let g := fun t : Fin n × Fin n => if h : t.1.val + t.2.val + 1 ≤ n then
    f ⟨t.1.val, by omega⟩ ⟨t.2.val, by omega⟩ else 0
  have he := Finset.sum_bij (s := S) (t := T) (f := fun t => f t.1 t.2) (g := g)
    (fun t ht => (⟨t.1.val, by have := (hS t).mp ht; omega⟩,
      ⟨t.2.val, by have := (hS t).mp ht; omega⟩))
    (fun t ht => (hT _).mpr ((hS t).mp ht))
    (fun a _ b _ h => by
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg (fun t : Fin n × Fin n => t.1.val) h
      · exact congrArg (fun t : Fin n × Fin n => t.2.val) h)
    (fun t ht => by
      have hh := (hT t).mp ht
      refine ⟨(⟨t.1.val, by omega⟩, ⟨t.2.val, by omega⟩), (hS _).mpr hh, ?_⟩
      exact Prod.ext (Fin.ext rfl) (Fin.ext rfl))
    (fun t ht => by
      dsimp only [g]
      rw [dite_eq_left ((hS t).mp ht)])
  simp only [S, T, Finset.sum_filter, Fintype.sum_prod_type] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [g]
  split_ifs <;> rfl

end Riesz2.PhysicalCore.Internal


namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (finite-family assembly): the actual
physical internal block is a sum over the complete reference-period
internal family. Only the index labels change. In particular the physical
antipodal multiplier stays in the original conditional coefficient. -/
theorem physicalInternal_reference_intervals (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    BoundaryEntries.physicalInternal β s n m x a b =
      ∑ i : Fin (M : ℕ), ∑ r : Fin ((M : ℕ) / 2),
        if hi : IntervalBoundary.IsInternal M n (i, r) then
          if a.castLE (by omega) ∈ cyclicIndexInterval M i (r.val + 1) ∧
            b.castLE (by omega) ∈ cyclicIndexInterval M i (r.val + 1) then
            BoundaryEntries.conditionalIntervalWeight β s n m
              ⟨r.val, by
                have := (Internal.internal_iff_end_le M n hnM i r).mp hi
                omega⟩
              ⟨i.val, by
                have := (Internal.internal_iff_end_le M n hnM i r).mp hi
                omega⟩ x
          else 0
        else 0 := by
  let N := ((n : ℕ) + m).succPNat
  have hnN : 2 * (n : ℕ) ≤ (N : ℕ) := hn
  have hph : BoundaryEntries.physicalInternal β s n m x a b =
      ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
        if IntervalBoundary.IsInternal N n (i, r) then
          (if a.castLE (by omega) ∈ cyclicIndexInterval N i (r.val + 1) ∧
            b.castLE (by omega) ∈ cyclicIndexInterval N i (r.val + 1)
          then BoundaryEntries.conditionalIntervalWeight β s n m r i x else 0)
        else 0 := by
    rw [BoundaryEntries.physicalInternal, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    have hsub : cyclicIndexInterval N i (r.val + 1) ⊆ BoundaryEntries.activeIndices N n ↔
        IntervalBoundary.IsInternal N n (i, r) := by
      simp only [IntervalBoundary.IsInternal, Finset.subset_iff,
        BoundaryEntries.activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    have ha : (a.castAdd m).castSucc = a.castLE (by omega : (n : ℕ) ≤ (N : ℕ)) := Fin.ext rfl
    have hb : (b.castAdd m).castSucc = b.castLE (by omega : (n : ℕ) ≤ (N : ℕ)) := Fin.ext rfl
    dsimp only [N] at hsub ha hb ⊢
    simp only [hsub, ha, hb, ite_and]
  rw [hph, Internal.internal_sum_reindex N n hnN]
  let f : Fin (M : ℕ) → Fin ((M : ℕ) / 2) → ℝ := fun i r =>
    if hi : IntervalBoundary.IsInternal M n (i,r) then
      if a.castLE (by omega) ∈ cyclicIndexInterval M i (r.val + 1) ∧
        b.castLE (by omega) ∈ cyclicIndexInterval M i (r.val + 1) then
        BoundaryEntries.conditionalIntervalWeight β s n m
          ⟨r.val, by have := (Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
          ⟨i.val, by have := (Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩ x
      else 0
    else 0
  change _ = ∑ i, ∑ r, f i r
  have hf : (∑ i, ∑ r, f i r) = ∑ i, ∑ r,
      if IntervalBoundary.IsInternal M n (i,r) then f i r else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [f]
    split_ifs <;> rfl
  rw [hf, Internal.internal_sum_reindex M n hnM]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : i.val + r.val + 1 ≤ (n : ℕ)
  · simp only [h, ↓reduceDIte]
    have hiN : IntervalBoundary.IsInternal N n
        (⟨i.val, by omega⟩, ⟨r.val, by omega⟩) :=
      (Internal.internal_iff_end_le N n hnN _ _).mpr h
    have hiM : IntervalBoundary.IsInternal M n
        (⟨i.val, by omega⟩, ⟨r.val, by omega⟩) :=
      (Internal.internal_iff_end_le M n hnM _ _).mpr h
    dsimp only [f]
    rw [dite_eq_left hiM]
    simp only [Internal.internal_mem_iff N n hnN _ _ hiN a,
      Internal.internal_mem_iff N n hnN _ _ hiN b,
      Internal.internal_mem_iff M n hnM _ _ hiM a,
      Internal.internal_mem_iff M n hnM _ _ hiM b]
  · simp only [h, ↓reduceDIte]

end Riesz2.PhysicalCore





namespace Riesz2.PhysicalCore

/-- The actual whole-period interval coefficient of the proper core
(Subsection 5.1). Internal physical coefficients keep their physical-period
antipodal multiplier. Forcing contributes at the singleton intervals.
All other intervals have exactly their original reference coefficient. -/
def properIntervalWeight (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  if x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ then
    if hi : IntervalBoundary.IsInternal M n (i,r) then
      BoundaryEntries.conditionalIntervalWeight β s n m
        ⟨r.val, by have := (Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
        ⟨i.val, by have := (Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩ x +
      if r.val = 0 then forcingHessian n θ ε x.val
        ⟨i.val, by have := (Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
        ⟨i.val, by have := (Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩ else 0
    else BoundaryEntries.referenceWeight s M hM K (i,r)
  else BoundaryEntries.referenceWeight s M hM K (i,r)

/-- Every whole-period coefficient is a Borel function of the actual active
configuration. -/
theorem measurable_properIntervalWeight (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)) :
    Measurable (properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r) := by
  unfold properIntervalWeight
  apply Measurable.ite (GoodBlocks.measurableSet_properGoodEvent β s n m ε κ₀)
  · split_ifs
    · exact (BoundaryEntries.measurable_conditionalIntervalWeight β s n m _ _).add
        ((measurable_forcingHessian n θ ε _ _).comp measurable_subtype_coe)
    · exact (BoundaryEntries.measurable_conditionalIntervalWeight β s n m _ _).add measurable_const
    · exact measurable_const
  · exact measurable_const

/-- The physical, forcing, and reference contributions to each whole-period
coefficient are nonnegative, including the physical antipodal endpoint. -/
theorem properIntervalWeight_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    0 ≤ properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x := by
  obtain ⟨C, hC, hF⟩ := forcingHessian_bound n m θ ε
  unfold properIntervalWeight
  split_ifs
  · exact add_nonneg (BoundaryEntries.conditionalIntervalWeight_nonneg β s n m _ _ x) (hF x _ _).1
  · exact add_nonneg (BoundaryEntries.conditionalIntervalWeight_nonneg β s n m _ _ x) le_rfl
  all_goals exact BoundaryEntries.referenceWeight_nonneg s M hM K (i,r)

namespace Internal

/-- Rewrite any reference interval subfamily on the exact finite length
carrier used in the matrix-bounds predicate. -/
theorem referenceIntervalBlock_sum (s : Riesz1.RieszExponent)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+)
    (hnM : (n : ℕ) ≤ (M : ℕ)) (family : Finset (Fin (M : ℕ)) → Prop)
    (a b : Fin (n : ℕ)) :
    BoundaryEntries.referenceIntervalBlock s M hM K n hnM family a b =
      ∑ i : Fin (M : ℕ), ∑ r : Fin ((M : ℕ) / 2),
        if family (cyclicIndexInterval M i (r.val + 1)) then
          BoundaryEntries.referenceWeight s M hM K (i,r) *
            (if a.castLE hnM ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0) *
            (if b.castLE hnM ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0)
        else 0 := by
  simp only [BoundaryEntries.referenceIntervalBlock, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range_succ']
  simp only [show ¬(1 ≤ (0 : ℕ) ∧ K ≤ 0) by omega, ite_false, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  simp only [BoundaryEntries.referenceWeight]
  split_ifs <;> simp_all

/-- The complete reference matrix on the whole-period length carrier. -/
theorem referenceMatrix_sum (s : Riesz1.RieszExponent)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (a b : Fin (M : ℕ)) :
    2 * referenceIntervalMatrix s M hM K a b =
      ∑ i : Fin (M : ℕ), ∑ r : Fin ((M : ℕ) / 2),
        BoundaryEntries.referenceWeight s M hM K (i,r) *
          (if a ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0) *
          (if b ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0) := by
  have he := BoundaryEntries.referenceInternal_add_crossing s M hM K M le_rfl a b
  rw [BoundaryEntries.referenceInternal, BoundaryEntries.referenceCrossing,
    referenceIntervalBlock_sum, referenceIntervalBlock_sum] at he
  simp only [Fin.castLE_refl, ← Finset.sum_add_distrib] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp_all

end Internal
end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore.Internal

/-- Singleton intervals carry precisely the diagonal forcing contribution.
This is an equality of the actual Hessian entries, including `n=1`. -/
theorem forcing_singleton_sum (n : ℕ+) (m : ℕ) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    forcingHessian n θ ε x.val a b =
      ∑ i : Fin (M : ℕ), ∑ r : Fin ((M : ℕ) / 2),
        if hi : IntervalBoundary.IsInternal M n (i,r) then
          (if r.val = 0 then forcingHessian n θ ε x.val
            ⟨i.val, by have := (internal_iff_end_le M n hnM i r).mp hi; omega⟩
            ⟨i.val, by have := (internal_iff_end_le M n hnM i r).mp hi; omega⟩ else 0) *
          (if a.castLE (by omega) ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0) *
          (if b.castLE (by omega) ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0)
        else 0 := by
  let r₀ : Fin ((M : ℕ) / 2) := ⟨0, by omega⟩
  let i₀ := a.castLE (by omega : (n : ℕ) ≤ (M : ℕ))
  have hsing (i : Fin (M : ℕ)) : cyclicIndexInterval M i 1 = {i} := by
    simp only [cyclicIndexInterval, Finset.range_one, Finset.image_singleton,
      add_zero, Nat.mod_eq_of_lt i.isLt]
  have hzero (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)) (hr : r ≠ r₀) : r.val ≠ 0 := by
    intro h
    exact hr (Fin.ext h)
  symm
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single r₀]
    · have hi : IntervalBoundary.IsInternal M n (i₀, r₀) :=
        (internal_iff_end_le M n hnM i₀ r₀).mpr (by dsimp only [i₀, r₀]; exact a.isLt)
      rw [dite_eq_left hi]
      have hba : b.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = i₀ ↔ b = a := by
        constructor
        · intro h
          apply Fin.ext
          exact congrArg (fun z : Fin (M : ℕ) => z.val) h
        · intro h; subst b; rfl
      simp only [r₀, ite_true, zero_add, hsing, Finset.mem_singleton,
        show a.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = i₀ from rfl, hba,
        mul_one]
      by_cases hab : a = b
      · subst b
        simp only [ite_true, mul_one]
        rfl
      · simp only [Ne.symm hab, ite_false, mul_zero, forcingHessian_apply n m θ ε x a b, hab]
    · intro r _ hr
      by_cases hi : IntervalBoundary.IsInternal M n (i₀,r)
      · simp only [dite_eq_left hi, ite_eq_right (hzero i₀ r hr), zero_mul]
      · exact dite_eq_right hi
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r = r₀
    · subst r
      have ha : a.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) ∉ cyclicIndexInterval M i 1 := by
        rw [hsing, Finset.mem_singleton]
        exact Ne.symm hi
      by_cases h : IntervalBoundary.IsInternal M n (i,r₀)
      · simp only [dite_eq_left h, r₀, zero_add, ha, ite_false, mul_zero, zero_mul]
      · exact dite_eq_right h
    · by_cases h : IntervalBoundary.IsInternal M n (i,r)
      · simp only [dite_eq_left h, ite_eq_right (hzero i r hr), zero_mul]
      · exact dite_eq_right h
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (whole-period assembly): every entry of the
existing proper core has its nonnegative cyclic-interval representation
using `properIntervalWeight`. All physical and reference antipodal factors
are kept, and the forcing is included in the same coefficient family. -/
theorem properMatrix_interval_entries (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (M : ℕ)) :
    properMatrix β s n m M hM (by omega) K θ ε κ₀ x a b =
      ∑ i : Fin (M : ℕ), ∑ r : Fin ((M : ℕ) / 2),
        properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x *
          (if a ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0) *
          (if b ∈ cyclicIndexInterval M i (r.val + 1) then 1 else 0) := by
  by_cases hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀
  · by_cases ha : a.val < (n : ℕ)
    · by_cases hb : b.val < (n : ℕ)
      · let a' : Fin (n : ℕ) := ⟨a.val, ha⟩
        let b' : Fin (n : ℕ) := ⟨b.val, hb⟩
        have hea : a'.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = a := Fin.ext rfl
        have heb : b'.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = b := Fin.ext rfl
        rw [show properMatrix β s n m M hM (by omega) K θ ε κ₀ x a b =
          properActive β s n m M hM (by omega) K θ ε κ₀ x a' b' by
            simpa only [hea, heb] using
              properMatrix_active β s n m M hM (by omega) K θ ε κ₀ x a' b']
        simp only [properActive, ite_eq_left hx, Matrix.add_apply]
        rw [Internal.forcing_singleton_sum n m M hM hnM θ ε x a' b',
          physicalInternal_reference_intervals β s n m hn M hnM x a' b',
          BoundaryEntries.referenceCrossing, Internal.referenceIntervalBlock_sum]
        simp only [hea, heb, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro r _
        have hs : cyclicIndexInterval M i (r.val + 1) ⊆ BoundaryEntries.activeIndices M n ↔
            IntervalBoundary.IsInternal M n (i,r) := by
          simp only [IntervalBoundary.IsInternal, Finset.subset_iff,
            BoundaryEntries.activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [properIntervalWeight, ite_eq_left hx, hs]
        by_cases hi : IntervalBoundary.IsInternal M n (i,r)
        · simp only [hi, ↓reduceDIte, not_true_eq_false, ite_false]
          by_cases hai : a ∈ cyclicIndexInterval M i (r.val + 1) <;>
            by_cases hbi : b ∈ cyclicIndexInterval M i (r.val + 1) <;>
              simp [hai, hbi]
          ring
        · simp only [hi, ↓reduceDIte, not_false_eq_true, ite_true, zero_add]
      · rw [properMatrix_exterior β s n m M hM (by omega) K θ ε κ₀ x a b (Or.inr (by omega))]
        change 2 * referenceIntervalMatrix s M hM K a b = _
        rw [Internal.referenceMatrix_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro r _
        by_cases hi : IntervalBoundary.IsInternal M n (i,r)
        · have hbi : b ∉ cyclicIndexInterval M i (r.val + 1) := fun h => hb (hi b h)
          simp only [properIntervalWeight, ite_eq_left hx, dite_eq_left hi, hbi,
            ite_false, mul_zero]
        · simp only [properIntervalWeight, ite_eq_left hx, dite_eq_right hi]
    · rw [properMatrix_exterior β s n m M hM (by omega) K θ ε κ₀ x a b (Or.inl (by omega))]
      change 2 * referenceIntervalMatrix s M hM K a b = _
      rw [Internal.referenceMatrix_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      by_cases hi : IntervalBoundary.IsInternal M n (i,r)
      · have hai : a ∉ cyclicIndexInterval M i (r.val + 1) := fun h => ha (hi a h)
        simp only [properIntervalWeight, ite_eq_left hx, dite_eq_left hi, hai,
          ite_false, mul_zero, zero_mul]
      · simp only [properIntervalWeight, ite_eq_left hx, dite_eq_right hi]
  · rw [properMatrix_of_not_mem β s n m M hM (by omega) K θ ε κ₀ x hx]
    change 2 * referenceIntervalMatrix s M hM K a b = _
    rw [Internal.referenceMatrix_sum]
    simp only [properIntervalWeight, ite_eq_right hx]

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (interval representation): the whole core
has exactly the quadratic representation required by the periodized
matrix predicate. This includes the forcing singletons and every retained
reference boundary interval. -/
theorem properMatrix_interval_quadratic (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (M : ℕ) → ℝ) :
    (∑ a, ∑ b, z a * properMatrix β s n m M hM (by omega) K θ ε κ₀ x a b * z b) =
      ∑ i, ∑ r, properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x *
        (cyclicGapSum M i (r.val + 1) z) ^ 2 := by
  have h := sum_quadratic_rankOne (κ := Fin (M : ℕ) × Fin ((M : ℕ) / 2))
    Finset.univ
    (fun t => properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ t.1 t.2 x)
    (fun t a => if a ∈ cyclicIndexInterval M t.1 (t.2.val + 1) then (1 : ℝ) else 0) z
  simp only [Fintype.sum_prod_type] at h
  have hs (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)) :
      (∑ a : Fin (M : ℕ), (if a ∈ cyclicIndexInterval M i (r.val + 1) then (1 : ℝ) else 0) * z a) =
        cyclicGapSum M i (r.val + 1) z := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    exact sum_cyclicIndexInterval_eq_cyclicGapSum M i
      (by have := r.isLt; omega) z
  simp only [hs] at h
  simp only [properMatrix_interval_entries β s n m hn M hM hnM K θ ε κ₀ x]
  exact h

/-- Nonnegativity of the actual whole physical core follows from its exact
nonnegative interval coefficients, before any asymptotic matrix estimates. -/
theorem properMatrix_posSemidef (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (properMatrix β s n m M hM (by omega) K θ ε κ₀ x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun z => ?_⟩
  · ext a b
    exact properMatrix_symmetric β s n m M hM (by omega) K θ ε κ₀ x b a
  · have h : 0 ≤ ∑ i, ∑ r, properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x *
        (cyclicGapSum M i (r.val + 1) z) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun r _ =>
        mul_nonneg (properIntervalWeight_nonneg β s n m hn M hM hnM K θ ε κ₀ i r x) (sq_nonneg _)
    rw [← properMatrix_interval_quadratic β s n m hn M hM hnM K θ ε κ₀ x z] at h
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using h

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (lower coefficients): on the actual good
event, every internal physical coefficient has the principal-image lower
bound with a power loss depending only on `s`. No long-interval threshold
is required for this lower bound. -/
theorem internal_coefficient_good_lower (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i,r)) :
    s.val * (s.val + 1) * (n : ℝ) ^ (-(s.val + 2) * ε) *
        ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤
      BoundaryEntries.conditionalIntervalWeight β s n m r i x := by
  let N := ((n : ℕ) + m).succPNat
  let L := cyclicGapSum N i (r.val + 1)
    (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
  have hL : 0 < L := (internal_gapSum_mem β s n m x r i hi).1
  have hupper : L ≤ ((r.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ ε := by
    dsimp only [L]
    rw [Internal.internal_gapSum_active n m hn x.val r i hi]
    unfold cyclicGapSum
    calc
      _ ≤ ∑ _a ∈ Finset.range (r.val + 1), (n : ℝ) ^ ε :=
        Finset.sum_le_sum fun a _ => (hx.1.1 _).2
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp := Real.rpow_le_rpow_of_nonpos hL hupper
    (show -s.val - 2 ≤ 0 by linarith [s.property.1])
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ ((r.val + 1 : ℕ) : ℝ))
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) ε),
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)] at hp
  have he : ε * (-s.val - 2) = -(s.val + 2) * ε := by ring
  rw [he] at hp
  have h := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ s.val * (s.val + 1) by have := s.property.1; positivity)
  have hl := internal_coefficient_lower β s n m x r i hi
  have h' : s.val * (s.val + 1) * (n : ℝ) ^ (-(s.val + 2) * ε) *
      ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤ s.val * (s.val + 1) * L ^ (-s.val - 2) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  exact h'.trans hl

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (coefficient comparison from below): every
whole-period coefficient dominates the literal reference coefficient by
`c(s) n^(-(s+2)ε)`, on both freezing branches. The comparison is valid for
every cutoff. It does not require the upper or entry-error bounds. -/
theorem properIntervalWeight_reference_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)),
        c * (n : ℝ) ^ (-(s.val + 2) * ε) * BoundaryEntries.referenceWeight s M hM K (i,r) ≤
          properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x := by
  obtain ⟨C, hC, hb⟩ := BoundaryEntries.referenceWeight_bound s
  let c := min 1 (s.val * (s.val + 1) / C)
  have hsp : 0 < s.val * (s.val + 1) := mul_pos s.property.1 (by linarith [s.property.1])
  have hc : 0 < c := lt_min zero_lt_one (div_pos hsp hC)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcC : c * C ≤ s.val * (s.val + 1) :=
    (le_div_iff₀ hC).mp (min_le_right _ _)
  refine ⟨c, hc, hc1, fun β n m hn M hM hnM K θ ε κ₀ hε x i r => ?_⟩
  let v := (n : ℝ) ^ (-(s.val + 2) * ε)
  have hv : 0 ≤ v := Real.rpow_nonneg (by positivity) _
  have hv1 : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast n.pos : (1 : ℝ) ≤ n) (by nlinarith [s.property.1])
  have hq : c * v ≤ 1 := calc
    c * v ≤ 1 * v := mul_le_mul_of_nonneg_right hc1 hv
    _ ≤ 1 := by simpa only [one_mul] using hv1
  have hq0 : 0 ≤ c * v := mul_nonneg hc.le hv
  have href0 := BoundaryEntries.referenceWeight_nonneg s M hM K (i,r)
  by_cases hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀
  · by_cases hi : IntervalBoundary.IsInternal M n (i,r)
    · have hend := (Internal.internal_iff_end_le M n hnM i r).mp hi
      let r' : Fin (((n : ℕ) + m + 1) / 2) := ⟨r.val, by omega⟩
      let i' : Fin ((n : ℕ) + m + 1) := ⟨i.val, by omega⟩
      have hip : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i',r') :=
        (Internal.internal_iff_end_le ((n : ℕ) + m).succPNat n hn i' r').mpr hend
      have hl := internal_coefficient_good_lower β s n m hn ε κ₀ x hx r' i' hip
      have hh : c * v * BoundaryEntries.referenceWeight s M hM K (i,r) ≤
          BoundaryEntries.conditionalIntervalWeight β s n m r' i' x := by
        calc
          _ ≤ c * v * (C * (r.val + 1 : ℝ) ^ (-s.val - 2)) :=
            mul_le_mul_of_nonneg_left (hb M hM K (i,r)) hq0
          _ = (c * C) * v * (r.val + 1 : ℝ) ^ (-s.val - 2) := by ring
          _ ≤ (s.val * (s.val + 1)) * v * (r.val + 1 : ℝ) ^ (-s.val - 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hv)
              (Real.rpow_nonneg (by positivity) _)
          _ ≤ _ := by simpa only [r', Nat.cast_add, Nat.cast_one] using hl
      have hf : 0 ≤ if r.val = 0 then forcingHessian n θ ε x.val
          ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ else 0 := by
        obtain ⟨B, _, hB⟩ := forcingHessian_bound n m θ ε
        split_ifs
        · exact (hB x _ _).1
        · exact le_rfl
      exact hh.trans (by
        simpa only [properIntervalWeight, ite_eq_left hx, dite_eq_left hi, r', i'] using
          le_add_of_nonneg_right hf)
    · simpa only [properIntervalWeight, ite_eq_left hx, dite_eq_right hi] using
        mul_le_of_le_one_left href0 hq
  · simpa only [properIntervalWeight, ite_eq_right hx] using mul_le_of_le_one_left href0 hq

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (matrix comparison from below): the actual
proper core dominates a temperature-independent power multiple of the whole
reference matrix, including the original exterior and coupling blocks. -/
theorem properMatrix_reference_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        (c * (n : ℝ) ^ (-(s.val + 2) * ε)) •
            ((2 : ℝ) • referenceIntervalMatrix s M hM K) ≤
          properMatrix β s n m M hM (by omega) K θ ε κ₀ x := by
  obtain ⟨c, hc, hc1, hb⟩ := properIntervalWeight_reference_lower s
  refine ⟨c, hc, hc1, fun β n m hn M hM hnM K θ ε κ₀ hε x => ?_⟩
  let q := c * (n : ℝ) ^ (-(s.val + 2) * ε)
  let v := fun (t : Fin (M : ℕ) × Fin ((M : ℕ) / 2)) (a : Fin (M : ℕ)) =>
    if a ∈ cyclicIndexInterval M t.1 (t.2.val + 1) then (1 : ℝ) else 0
  let w := fun t : Fin (M : ℕ) × Fin ((M : ℕ) / 2) =>
    properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ t.1 t.2 x -
      q * BoundaryEntries.referenceWeight s M hM K t
  have he : properMatrix β s n m M hM (by omega) K θ ε κ₀ x -
      q • ((2 : ℝ) • referenceIntervalMatrix s M hM K) =
      ∑ t, w t • Matrix.vecMulVec (v t) (v t) := by
    ext a b
    change properMatrix β s n m M hM (by omega) K θ ε κ₀ x a b -
      q * (2 * referenceIntervalMatrix s M hM K a b) = _
    rw [properMatrix_interval_entries β s n m hn M hM hnM K θ ε κ₀ x,
      Internal.referenceMatrix_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [w, v]
    ring
  apply Matrix.le_iff.mpr
  rw [he]
  exact FiniteMatrixOrder.posSemidef_rankOneSum Finset.univ w v
    (fun t _ => sub_nonneg.mpr (hb β n m hn M hM hnM K θ ε κ₀ hε x t.1 t.2))

/-- See the proof of Lemma 5.4 in the paper (coercivity): truncation coercivity transfers
to the actual proper core with a prefactor depending only on `s`. The
configuration, temperature, physical period, and reference period are all
quantified after that prefactor. -/
theorem properMatrix_truncated_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
      (K : ℕ), 1 ≤ K → K ≤ (M : ℕ) / 4 →
      ∀ (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        (c * (n : ℝ) ^ (-(s.val + 2) * ε) * (K : ℝ) ^ (-1 - s.val)) •
            (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤
          properMatrix β s n m M hM (by omega) K θ ε κ₀ x := by
  obtain ⟨c, hc, _, hb⟩ := properMatrix_reference_lower s
  obtain ⟨a, ha, href⟩ := referenceIntervalMatrix_truncated_coercivity s
  refine ⟨c * 2 * a, by positivity, fun β n m hn M hM hnM K hK hKM θ ε κ₀ hε x => ?_⟩
  let q := c * (n : ℝ) ^ (-(s.val + 2) * ε)
  have hq : 0 ≤ q := mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
  have hr := smul_le_smul_of_nonneg_left (href M hM K hK hKM).2.2
    (mul_nonneg hq (by norm_num : (0 : ℝ) ≤ 2))
  have hcompare := hb β n m hn M hM hnM K θ ε κ₀ hε x
  have he : (c * 2 * a) * (n : ℝ) ^ (-(s.val + 2) * ε) * (K : ℝ) ^ (-1 - s.val) =
      (q * 2) * (a * (K : ℝ) ^ (-1 - s.val)) := by dsimp only [q]; ring
  rw [he]
  have hr' : ((q * 2) * (a * (K : ℝ) ^ (-1 - s.val))) •
      (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤
      q • ((2 : ℝ) • referenceIntervalMatrix s M hM K) := by
    simpa only [smul_smul] using hr
  exact hr'.trans hcompare

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (prescribed-cutoff coercivity): the actual
cutoff `floor(n^ε)^M₀` gives the structural exponent
`s+2+M₀(1+s)`. The positive prefactor precedes `M₀`, temperature, epsilon,
and both periods, so no exponent or constant depends on total volume. -/
theorem properMatrix_cutoff_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M₀ : ℕ) (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
      (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      K ≤ (M : ℕ) / 4 →
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        (c * (n : ℝ) ^ (-((s.val + 2) + (M₀ : ℝ) * (1 + s.val)) * ε)) •
            (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤
          properMatrix β s n m M hM (by omega) K θ ε κ₀ x := by
  obtain ⟨c, hc, hb⟩ := properMatrix_truncated_coercivity s
  refine ⟨c, hc, ?_⟩
  intro M₀ β n m hn M hM hnM θ ε κ₀ hε K hKM x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hfloor : 1 ≤ ⌊(n : ℝ) ^ ε⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hε)
  have hK : 1 ≤ K := one_le_pow₀ hfloor
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hupper : (K : ℝ) ≤ (n : ℝ) ^ ((M₀ : ℝ) * ε) := by
    calc
      _ = (⌊(n : ℝ) ^ ε⌋₊ : ℝ) ^ M₀ := by rw [Nat.cast_pow]
      _ ≤ ((n : ℝ) ^ ε) ^ M₀ :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hn0.le _)) M₀
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        ring
  have hpow := Real.rpow_le_rpow_of_nonpos hK0 hupper
    (show -1 - s.val ≤ 0 by linarith [s.property.1])
  have he : (n : ℝ) ^ (-((s.val + 2) + (M₀ : ℝ) * (1 + s.val)) * ε) =
      (n : ℝ) ^ (-(s.val + 2) * ε) *
        ((n : ℝ) ^ ((M₀ : ℝ) * ε)) ^ (-1 - s.val) := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    ring
  have hscalar : c * (n : ℝ) ^ (-((s.val + 2) + (M₀ : ℝ) * (1 + s.val)) * ε) ≤
      c * (n : ℝ) ^ (-(s.val + 2) * ε) * (K : ℝ) ^ (-1 - s.val) := by
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have horder := smul_le_smul_of_nonneg_right hscalar
    (show (0 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤ 1 by exact zero_le_one)
  exact horder.trans (hb β n m hn M hM hnM K hK hKM θ ε κ₀ hε x)

end Riesz2.PhysicalCore
