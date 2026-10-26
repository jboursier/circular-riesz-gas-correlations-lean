/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundaryEntriesPart3
public import Riesz2.Preliminaries.InverseIntervalKernelPart2
public import Riesz2.ToMathlib.CyclicIntervalBoundary

/-!
# Reference endpoints and boundary remainders

The reference weights retain the cutoff and antipodal half-weight of the
interval matrix. The grouping uses `IntervalBoundary`. These estimates
complete the boundary remainder bounds of Lemma 5.6.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.BoundaryEntries

/-- The literal reference Hessian coefficient, specialized to the existing
interval-label carrier (Subsection 2.5, Subsection 5.1). -/
def referenceWeight (s : Riesz1.RieszExponent) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (K : ℕ) (t : Fin (M : ℕ) × Fin ((M : ℕ) / 2)) : ℝ :=
  if K ≤ t.2.val + 1 then
    2 * ((1 - if 2 * (t.2.val + 1) = (M : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s M hM
        ⟨(t.2.val + 1) % (M : ℕ), Nat.mod_lt _ M.pos⟩)
  else 0

/-- See Subsection 5.1 of the paper: reference coefficients are nonnegative with the
actual cutoff, including at the antipodal length. -/
theorem referenceWeight_nonneg (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (t : Fin (M : ℕ) × Fin ((M : ℕ) / 2)) :
    0 ≤ referenceWeight s M hM K t := by
  have hr : t.2.val + 1 < (M : ℕ) := by have := t.2.isLt; omega
  have hk : (⟨(t.2.val + 1) % (M : ℕ), Nat.mod_lt _ M.pos⟩ : Fin (M : ℕ)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Nat.mod_eq_of_lt hr] at this
    omega
  have hp := (sampledSecondDifference_pos s M hM hk).le
  unfold referenceWeight
  split_ifs <;> positivity

/-- A finite power tail, in the length convention used by the interval API. -/
theorem finite_length_tail_internal {t R : ℝ} (ht : 1 < t) (hR : 1 ≤ R)
    (L : ℕ) :
    (∑ k : Fin L, if R ≤ (k.val + 1 : ℝ) then (k.val + 1 : ℝ) ^ (-t) else 0) ≤
      (1 + 1 / (t - 1)) * R ^ (1 - t) := by
  let g : ℕ → ℝ := fun k => if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0
  have hg : Summable g := (summable_one_add_rpow_neg ht).of_nonneg_of_le
    (fun k => by dsimp [g]; split_ifs <;> positivity)
    (fun k => by dsimp [g]; split_ifs <;> first | exact le_rfl | positivity)
  have hs := hg.sum_le_tsum (Finset.range L)
    (fun k _ => by dsimp [g]; split_ifs <;> positivity)
  change (∑ k : Fin L, (fun k : ℕ => if R ≤ (k + 1 : ℝ) then (k + 1 : ℝ) ^ (-t) else 0) k.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if R ≤ (k + 1 : ℝ) then (k + 1 : ℝ) ^ (-t) else 0) L]
  have he : (fun k : ℕ => if R ≤ (k + 1 : ℝ) then (k + 1 : ℝ) ^ (-t) else 0) = g := by
    funext k
    dsimp [g]
    rw [add_comm (k : ℝ) 1]
  simpa only [he] using hs.trans (tsum_tail_indicator_le ht hR)

private theorem trace_prefix (M : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (i : Fin (M : ℕ)) (r j : ℕ) (hj : j ≤ (n : ℕ)) :
    IntervalBoundary.trace M n hn i r = IntervalBoundary.initialSegment n j ↔
      cyclicIndexInterval M i r ∩ activeIndices M n = activeIndices M j := by
  constructor
  · intro h
    ext a
    by_cases ha : a.val < (n : ℕ)
    · have hh := Finset.ext_iff.mp h (⟨a.val, ha⟩ : Fin (n : ℕ))
      have he : (⟨a.val, ha⟩ : Fin (n : ℕ)).castLE hn = a := Fin.ext rfl
      simpa only [IntervalBoundary.trace, IntervalBoundary.initialSegment,
        activeIndices, Finset.mem_filter, Finset.mem_univ, true_and, he,
        Finset.mem_inter, ha, and_true] using hh
    · simp only [Finset.mem_inter, activeIndices, Finset.mem_filter,
        Finset.mem_univ, true_and, ha, and_false, false_iff]
      omega
  · intro h
    ext a
    have hh := Finset.ext_iff.mp h (a.castLE hn)
    simpa only [IntervalBoundary.trace, IntervalBoundary.initialSegment,
      activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, Fin.val_castLE, a.isLt, and_true] using hh

private theorem trace_suffix (M : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (i : Fin (M : ℕ)) (r j : ℕ) :
    IntervalBoundary.trace M n hn i r = IntervalBoundary.terminalSegment n j ↔
      cyclicIndexInterval M i r ∩ activeIndices M n =
        (activeIndices M n).filter (fun a => j ≤ a.val) := by
  constructor
  · intro h
    ext a
    by_cases ha : a.val < (n : ℕ)
    · have hh := Finset.ext_iff.mp h (⟨a.val, ha⟩ : Fin (n : ℕ))
      have he : (⟨a.val, ha⟩ : Fin (n : ℕ)).castLE hn = a := Fin.ext rfl
      simpa only [IntervalBoundary.trace, IntervalBoundary.terminalSegment,
        activeIndices, Finset.mem_filter, Finset.mem_univ, true_and, he,
        Finset.mem_inter, ha, and_true, true_and] using hh
    · simp [activeIndices, ha]
  · intro h
    ext a
    have hh := Finset.ext_iff.mp h (a.castLE hn)
    simpa only [IntervalBoundary.trace, IntervalBoundary.terminalSegment,
      activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, Fin.val_castLE, a.isLt, and_true, true_and] using hh

private theorem internal_iff (M : ℕ+) (n : ℕ) (t : Fin (M : ℕ) × Fin ((M : ℕ) / 2)) :
    IntervalBoundary.IsInternal M n t ↔
      cyclicIndexInterval M t.1 (t.2.val + 1) ⊆ activeIndices M n := by
  simp only [IntervalBoundary.IsInternal, Finset.subset_iff, activeIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- See Subsection 5.1 of the paper: the generic interval boundary matrix is exactly
the reference crossing block, with its normalization. -/
theorem referenceCrossing_eq_boundaryMatrix (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ)) :
    referenceCrossing s M hM K n hn =
      IntervalBoundary.boundaryMatrix M n hn (referenceWeight s M hM K) := by
  ext a b
  simp only [referenceCrossing, referenceIntervalBlock, IntervalBoundary.boundaryMatrix,
    Fintype.sum_prod_type, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_range_succ']
  simp only [show ¬(1 ≤ (0 : ℕ) ∧ K ≤ 0) by omega, ite_false, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  have he := internal_iff M n (i, r)
  simp only [IntervalBoundary.rankOne, IntervalBoundary.trace, Finset.mem_filter,
    Finset.mem_univ, true_and, referenceWeight, he]
  split_ifs <;> simp_all

/-- The existing semiring boundary representation in the cut-index convention
of Subsection 5.1. This is an internal algebraic bridge for arbitrary weights. -/
theorem boundaryMatrix_grouped_internal (M : ℕ+) (n : ℕ+)
    (hn : (n : ℕ) ≤ (M : ℕ)) (hhalf : 2 * (n : ℕ) ≤ (M : ℕ))
    (A : Fin (M : ℕ) × Fin ((M : ℕ) / 2) → ℝ) :
    IntervalBoundary.boundaryMatrix M n hn A = groupedBoundaryMatrix n
      (fun b => IntervalBoundary.prefixCoefficient M n hn A (b.val + 1))
      (fun b => IntervalBoundary.suffixCoefficient M n hn A (b.val + 1))
      (IntervalBoundary.fullCoefficient M n hn A) := by
  ext i j
  rw [groupedBoundaryMatrix_apply]
  have h := IntervalBoundary.boundary_representation M n.pos hhalf A i j
  simp only [Finset.sum_Ico_eq_sum_range] at h
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  simp only [IntervalBoundary.rankOne, IntervalBoundary.initialSegment,
    IntervalBoundary.terminalSegment, Finset.mem_filter, Finset.mem_univ,
    true_and, mul_ite, mul_one, mul_zero] at h
  have hp (b : Fin ((n : ℕ) - 1)) :
      (i.val < b.val + 1 ∧ j.val < b.val + 1) ↔ (i.val ≤ b.val ∧ j.val ≤ b.val) := by omega
  have hs (b : Fin ((n : ℕ) - 1)) :
      (b.val + 1 ≤ i.val ∧ b.val + 1 ≤ j.val) ↔ (b.val < i.val ∧ b.val < j.val) := by omega
  simp only [Nat.add_comm 1] at h
  simp only [hp, hs] at h
  linarith

/-- See Subsection 5.1 of the paper: exact grouping of the actual reference block,
using the already defined general prefix, suffix and full coefficients. -/
theorem referenceCrossing_grouped (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (hhalf : 2 * (n : ℕ) ≤ (M : ℕ)) :
    referenceCrossing s M hM K n hn = groupedBoundaryMatrix n
      (fun b => IntervalBoundary.prefixCoefficient M n hn (referenceWeight s M hM K) (b.val + 1))
      (fun b => IntervalBoundary.suffixCoefficient M n hn (referenceWeight s M hM K) (b.val + 1))
      (IntervalBoundary.fullCoefficient M n hn (referenceWeight s M hM K)) := by
  rw [referenceCrossing_eq_boundaryMatrix]
  exact boundaryMatrix_grouped_internal M n hn hhalf _

/-- See Subsection 5.1 of the paper: positivity of all three reference coefficient families. -/
theorem referenceCoefficients_nonneg (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ)) (j : ℕ) :
    0 ≤ IntervalBoundary.prefixCoefficient M n hn (referenceWeight s M hM K) j ∧
    0 ≤ IntervalBoundary.suffixCoefficient M n hn (referenceWeight s M hM K) j ∧
    0 ≤ IntervalBoundary.fullCoefficient M n hn (referenceWeight s M hM K) := by
  have hp := referenceWeight_nonneg s M hM K
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> first | exact hp t | exact le_rfl

/-- See the proof of Lemma 5.6 in the paper: a uniform curvature
majorant for the actual retained reference coefficients. -/
theorem referenceWeight_bound (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ)
      (t : Fin (M : ℕ) × Fin ((M : ℕ) / 2)),
      referenceWeight s M hM K t ≤ C * (t.2.val + 1 : ℝ) ^ (-s.val - 2) := by
  obtain ⟨c, C, hc, hC, hb⟩ := sampledSecondDifference_bounds s
  refine ⟨2 * C, by positivity, ?_⟩
  intro M hM K t
  have hr := t.2.isLt
  have hrM : t.2.val + 1 < (M : ℕ) := by omega
  let k : Fin (M : ℕ) := ⟨(t.2.val + 1) % (M : ℕ), Nat.mod_lt _ M.pos⟩
  have hkv : k.val = t.2.val + 1 := Nat.mod_eq_of_lt hrM
  have hk : k ≠ 0 := by intro he; have := congrArg Fin.val he; simp only [hkv, Fin.val_zero] at this; omega
  have hd : Riesz1.cyclicIndexDistance M k 0 = t.2.val + 1 := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right, hkv]
    omega
  have hu := (hb M hM k hk).2
  rw [hd] at hu
  have hp := (sampledSecondDifference_pos s M hM hk).le
  unfold referenceWeight
  split_ifs <;> dsimp only [k] at hp hu <;> push_cast at hu <;> nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ t.2.val + 1) (-s.val - 2)]

/-- See Subsection 5.1 of the paper: exact fixed-length prefix grouping, with the
reference cutoff and half-weight contained in `referenceWeight`. -/
theorem reference_prefix_sum (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (hhalf : 2 * (n : ℕ) ≤ (M : ℕ)) (j : Fin ((n : ℕ) - 1)) :
    IntervalBoundary.prefixCoefficient M n hn (referenceWeight s M hM K) (j.val + 1) =
      ∑ r : Fin ((M : ℕ) / 2), ∑ i : Fin (M : ℕ),
        if (n : ℕ) ≤ i.val ∧ i.val + (r.val + 1) = (M : ℕ) + (j.val + 1)
        then referenceWeight s M hM K (i, r) else 0 := by
  unfold IntervalBoundary.prefixCoefficient
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  have hh := prefix_crossing_iff M (r := r.val + 1) hhalf (by omega : 0 < j.val + 1)
    (by have := j.isLt; omega) (by have := r.isLt; omega) i
  rw [← trace_prefix M n hn i (r.val + 1) (j.val + 1) (by have := j.isLt; omega),
    ← internal_iff M n (i, r)] at hh
  have hf : (if IntervalBoundary.IsInternal M n (i, r) then 0 else
      if IntervalBoundary.trace M n hn i (r.val + 1) = IntervalBoundary.initialSegment n (j.val + 1)
      then referenceWeight s M hM K (i, r) else 0) =
      (if ¬IntervalBoundary.IsInternal M n (i, r) ∧
        IntervalBoundary.trace M n hn i (r.val + 1) = IntervalBoundary.initialSegment n (j.val + 1)
      then referenceWeight s M hM K (i, r) else 0) := by split_ifs <;> simp_all
  change (if IntervalBoundary.IsInternal M n (i, r) then 0 else
      if IntervalBoundary.trace M n hn i (r.val + 1) = IntervalBoundary.initialSegment n (j.val + 1)
      then referenceWeight s M hM K (i, r) else 0) = _
  rw [hf]
  exact if_congr hh rfl rfl

/-- See Subsection 5.1 of the paper: exact fixed-length suffix grouping. -/
theorem reference_suffix_sum (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (hhalf : 2 * (n : ℕ) ≤ (M : ℕ)) (j : Fin ((n : ℕ) - 1)) :
    IntervalBoundary.suffixCoefficient M n hn (referenceWeight s M hM K) (j.val + 1) =
      ∑ r : Fin ((M : ℕ) / 2), ∑ i : Fin (M : ℕ),
        if i.val = j.val + 1 ∧ (n : ℕ) < i.val + (r.val + 1)
        then referenceWeight s M hM K (i, r) else 0 := by
  unfold IntervalBoundary.suffixCoefficient
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  have hh := suffix_crossing_iff M (r := r.val + 1) hhalf (by omega : 0 < j.val + 1)
    (by have := j.isLt; omega) (by have := r.isLt; omega) i
  rw [← trace_suffix M n hn i (r.val + 1) (j.val + 1),
    ← internal_iff M n (i, r)] at hh
  have hf : (if IntervalBoundary.IsInternal M n (i, r) then 0 else
      if IntervalBoundary.trace M n hn i (r.val + 1) = IntervalBoundary.terminalSegment n (j.val + 1)
      then referenceWeight s M hM K (i, r) else 0) =
      (if ¬IntervalBoundary.IsInternal M n (i, r) ∧
        IntervalBoundary.trace M n hn i (r.val + 1) = IntervalBoundary.terminalSegment n (j.val + 1)
      then referenceWeight s M hM K (i, r) else 0) := by split_ifs <;> simp_all
  change (if IntervalBoundary.IsInternal M n (i, r) then 0 else
      if IntervalBoundary.trace M n hn i (r.val + 1) = IntervalBoundary.terminalSegment n (j.val + 1)
      then referenceWeight s M hM K (i, r) else 0) = _
  rw [hf]
  exact if_congr hh rfl rfl

private theorem single_start_sum {L : ℕ} (P : Fin L → Prop) (w : ℝ) (hw : 0 ≤ w)
    (hP : ∀ i, P i → ∀ j, P j → i = j) :
    (∑ i : Fin L, if P i then w else 0) ≤ w := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter P).card ≤ 1 := Finset.card_le_one.mpr
    (fun i hi j hj => hP i (Finset.mem_filter.mp hi).2 j (Finset.mem_filter.mp hj).2)
  have hcR : ((Finset.univ.filter P).card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcR hw

/-- Internal endpoint-tail comparison. Its coefficient hypothesis is discharged
by `referenceWeight_bound` in the final reference estimates. -/
theorem reference_endpoint_tails_internal (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (hhalf : 2 * (n : ℕ) ≤ (M : ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ t, referenceWeight s M hM K t ≤ C * (t.2.val + 1 : ℝ) ^ (-s.val - 2))
    (j : Fin ((n : ℕ) - 1)) :
    IntervalBoundary.prefixCoefficient M n hn (referenceWeight s M hM K) (j.val + 1) ≤
      C * (1 + 1 / (s.val + 1)) * (j.val + 1 : ℝ) ^ (-s.val - 1) ∧
    IntervalBoundary.suffixCoefficient M n hn (referenceWeight s M hM K) (j.val + 1) ≤
      C * (1 + 1 / (s.val + 1)) * ((n : ℝ) - j.val - 1) ^ (-s.val - 1) := by
  have ht : 1 < s.val + 2 := by linarith [s.property.1]
  have htail (R : ℝ) (hR : 1 ≤ R) := finite_length_tail_internal ht hR ((M : ℕ) / 2)
  have hp (r : Fin ((M : ℕ) / 2)) :
      (∑ i : Fin (M : ℕ), if (n : ℕ) ≤ i.val ∧ i.val + (r.val + 1) = (M : ℕ) + (j.val + 1)
        then referenceWeight s M hM K (i, r) else 0) ≤
      C * (if (j.val + 1 : ℝ) ≤ r.val + 1 then (r.val + 1 : ℝ) ^ (-(s.val + 2)) else 0) := by
    by_cases hr : j.val + 1 ≤ r.val + 1
    · have hu := single_start_sum (fun i : Fin (M : ℕ) =>
          (n : ℕ) ≤ i.val ∧ i.val + (r.val + 1) = (M : ℕ) + (j.val + 1))
        (referenceWeight s M hM K (0, r)) (referenceWeight_nonneg s M hM K _)
        (by intro i hi k hk; apply Fin.ext; omega)
      have hrR : (j.val + 1 : ℝ) ≤ r.val + 1 := by exact_mod_cast hr
      simp only [hrR, ite_true]
      rw [show -(s.val + 2) = -s.val - 2 by ring]
      simpa only [referenceWeight] using hu.trans (hW (0, r))
    · have hnone (i : Fin (M : ℕ)) : ¬((n : ℕ) ≤ i.val ∧
          i.val + (r.val + 1) = (M : ℕ) + (j.val + 1)) := by have := i.isLt; omega
      have hrR : ¬(j.val + 1 : ℝ) ≤ r.val + 1 := by exact_mod_cast hr
      simp [hnone, hrR]
  have hs (r : Fin ((M : ℕ) / 2)) :
      (∑ i : Fin (M : ℕ), if i.val = j.val + 1 ∧ (n : ℕ) < i.val + (r.val + 1)
        then referenceWeight s M hM K (i, r) else 0) ≤
      C * (if (n : ℝ) - j.val - 1 ≤ r.val + 1 then (r.val + 1 : ℝ) ^ (-(s.val + 2)) else 0) := by
    by_cases hr : (n : ℕ) - (j.val + 1) ≤ r.val + 1
    · have hu := single_start_sum (fun i : Fin (M : ℕ) =>
          i.val = j.val + 1 ∧ (n : ℕ) < i.val + (r.val + 1))
        (referenceWeight s M hM K (0, r)) (referenceWeight_nonneg s M hM K _)
        (by intro i hi k hk; apply Fin.ext; omega)
      have hrR : (n : ℝ) - j.val - 1 ≤ r.val + 1 := by
        have := j.isLt
        have hh : (n : ℕ) ≤ r.val + 1 + (j.val + 1) := by omega
        have hhR : (n : ℝ) ≤ r.val + 1 + (j.val + 1) := by exact_mod_cast hh
        linarith
      simp only [hrR, ite_true]
      rw [show -(s.val + 2) = -s.val - 2 by ring]
      simpa only [referenceWeight] using hu.trans (hW (0, r))
    · have hnone (i : Fin (M : ℕ)) : ¬(i.val = j.val + 1 ∧
          (n : ℕ) < i.val + (r.val + 1)) := by omega
      have hrR : ¬(n : ℝ) - j.val - 1 ≤ r.val + 1 := by
        have hh : r.val + 1 + (j.val + 1) < (n : ℕ) := by omega
        have hhR : (r.val + 1 + (j.val + 1) : ℝ) < n := by exact_mod_cast hh
        linarith
      simp [hnone, hrR]
  have hpR : (1 : ℝ) ≤ j.val + 1 := by linarith [show (0 : ℝ) ≤ (j.val : ℝ) from Nat.cast_nonneg _]
  have hsR : (1 : ℝ) ≤ (n : ℝ) - j.val - 1 := by
    have hh : j.val + 2 ≤ (n : ℕ) := by have := j.isLt; omega
    have hhR : (j.val + 2 : ℝ) ≤ n := by exact_mod_cast hh
    linarith
  constructor
  · rw [reference_prefix_sum s M hM K n hn hhalf j]
    apply (Finset.sum_le_sum (fun r _ => hp r)).trans
    rw [← Finset.mul_sum]
    simpa only [show s.val + 2 - 1 = s.val + 1 by ring,
      show 1 - (s.val + 2) = -s.val - 1 by ring, mul_assoc] using
      mul_le_mul_of_nonneg_left (htail _ hpR) hC
  · rw [reference_suffix_sum s M hM K n hn hhalf j]
    apply (Finset.sum_le_sum (fun r _ => hs r)).trans
    rw [← Finset.mul_sum]
    simpa only [show s.val + 2 - 1 = s.val + 1 by ring,
      show 1 - (s.val + 2) = -s.val - 1 by ring, mul_assoc] using
      mul_le_mul_of_nonneg_left (htail _ hsR) hC

private theorem full_trace_length (M : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (hhalf : 2 * (n : ℕ) ≤ (M : ℕ)) (i : Fin (M : ℕ)) (r : ℕ)
    (hr : 2 * r ≤ (M : ℕ))
    (h : IntervalBoundary.trace M n hn i r = Finset.univ) : (n : ℕ) ≤ r := by
  have hm (a : Fin (n : ℕ)) : a.castLE hn ∈ cyclicIndexInterval M i r := by
    have hh := h.symm ▸ Finset.mem_univ a
    exact (Finset.mem_filter.mp hh).2
  have h0 := hm ⟨0, n.pos⟩
  have h1 := hm ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  rw [mem_interval_active M hhalf hr _ _ (by exact n.pos)] at h0
  rw [mem_interval_active M hhalf hr _ _ (by change (n : ℕ) - 1 < (n : ℕ); have := n.pos; omega)] at h1
  dsimp only [Fin.val_castLE] at h0 h1
  split_ifs at h0 h1 <;> have := i.isLt <;> have := n.pos <;> omega

/-- Internal full-trace bound. Pair counting bounds the number of full-trace
starts by the length, including the singleton active window. -/
theorem reference_full_tail_internal (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (hhalf : 2 * (n : ℕ) ≤ (M : ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ t, referenceWeight s M hM K t ≤ C * (t.2.val + 1 : ℝ) ^ (-s.val - 2)) :
    IntervalBoundary.fullCoefficient M n hn (referenceWeight s M hM K) ≤
      C * (1 + 1 / s.val) * (n : ℝ) ^ (-s.val) := by
  unfold IntervalBoundary.fullCoefficient
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hterm (r : Fin ((M : ℕ) / 2)) :
      (∑ i : Fin (M : ℕ), if IntervalBoundary.IsInternal M n (i, r) then 0 else
        if IntervalBoundary.trace M n hn i (r.val + 1) = Finset.univ
        then referenceWeight s M hM K (i, r) else 0) ≤
      C * (if (n : ℝ) ≤ r.val + 1 then (r.val + 1 : ℝ) ^ (-(s.val + 1)) else 0) := by
    have hr : 2 * (r.val + 1) ≤ (M : ℕ) := by have := r.isLt; omega
    by_cases hnR : (n : ℕ) ≤ r.val + 1
    · have hnR' : (n : ℝ) ≤ r.val + 1 := by exact_mod_cast hnR
      rw [ite_eq_left hnR']
      have hsum : (∑ i : Fin (M : ℕ), if IntervalBoundary.IsInternal M n (i, r) then 0 else
          if IntervalBoundary.trace M n hn i (r.val + 1) = Finset.univ
          then referenceWeight s M hM K (i, r) else 0) ≤
          referenceWeight s M hM K (0, r) * (r.val + 1 : ℝ) := by
        have hp := referenceWeight_nonneg s M hM K (0, r)
        calc
          _ ≤ ∑ i : Fin (M : ℕ), referenceWeight s M hM K (0, r) *
              ((if (0 : Fin (M : ℕ)) ∈ cyclicIndexInterval M i (r.val + 1) then (1 : ℝ) else 0) *
               (if (0 : Fin (M : ℕ)) ∈ cyclicIndexInterval M i (r.val + 1) then (1 : ℝ) else 0)) := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hi : IntervalBoundary.IsInternal M n (i, r)
            · simp only [hi, ite_true]
              positivity
            · by_cases ht : IntervalBoundary.trace M n hn i (r.val + 1) = Finset.univ
              · have hm : (0 : Fin (M : ℕ)) ∈ cyclicIndexInterval M i (r.val + 1) := by
                  have hh := ht.symm ▸ Finset.mem_univ (⟨0, n.pos⟩ : Fin (n : ℕ))
                  simpa only [IntervalBoundary.trace, Finset.mem_filter, Finset.mem_univ,
                    true_and, Fin.castLE_mk, show (⟨0, by omega⟩ : Fin (M : ℕ)) = 0 from Fin.ext rfl] using hh
                simp only [hi, ht, hm, ite_false, ite_true, mul_one]
                rfl
              · simp only [hi, ht, ite_false]
                positivity
          _ = _ := by
            rw [← Finset.mul_sum, cyclicIndexInterval_pair_count M hr 0 0]
            simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_self, Nat.sub_zero,
              Nat.zero_min, Nat.cast_add, Nat.cast_one]
      apply hsum.trans
      calc
        _ ≤ C * (r.val + 1 : ℝ) ^ (-s.val - 2) * (r.val + 1 : ℝ) :=
          mul_le_mul_of_nonneg_right (hW (0, r)) (by positivity)
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_add_one (by positivity : (r.val + 1 : ℝ) ≠ 0)]
          congr 2
          ring
    · have hnR' : ¬(n : ℝ) ≤ r.val + 1 := by exact_mod_cast hnR
      have ht (i : Fin (M : ℕ)) : IntervalBoundary.trace M n hn i (r.val + 1) ≠ Finset.univ :=
        fun hh => hnR (full_trace_length M n hn hhalf i _ hr hh)
      simp [ht, hnR']
  apply (Finset.sum_le_sum (fun r _ => hterm r)).trans
  rw [← Finset.mul_sum]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  simpa only [show s.val + 1 - 1 = s.val by ring,
    show 1 - (s.val + 1) = -s.val by ring, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (finite_length_tail_internal (by linarith [s.property.1] : 1 < s.val + 1) hn1 ((M : ℕ) / 2)) hC

/-- See the proof of Lemma 5.6 in the paper, all reference clauses.
This stronger version has no size loss, is uniform in the reference period
and the cutoff, and includes the one-gap diagonal. -/
theorem reference_endpoint_bounds (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ)
      (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ)), 2 * (n : ℕ) ≤ (M : ℕ) →
      (∀ b : Fin ((n : ℕ) - 1),
        IntervalBoundary.prefixCoefficient M n hn (referenceWeight s M hM K) (b.val + 1) ≤
          C * (b.val + 1 : ℝ) ^ (-s.val) *
            ((min (b.val + 1) ((n : ℕ) - b.val) : ℕ) : ℝ)⁻¹ ∧
        IntervalBoundary.suffixCoefficient M n hn (referenceWeight s M hM K) (b.val + 1) ≤
          C * ((n : ℝ) - b.val - 1) ^ (-s.val) *
            ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ)⁻¹) ∧
      IntervalBoundary.fullCoefficient M n hn (referenceWeight s M hM K) ≤
        C * (n : ℝ) ^ (-s.val) ∧
      ∀ i : Fin (n : ℕ), referenceCrossing s M hM K n hn i i ≤
        C * (5 / Real.log 2 + 4) * Real.log (2 * (n : ℝ)) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by
  obtain ⟨W, hW, hb⟩ := referenceWeight_bound s
  let C := W * (1 + 1 / s.val)
  have hC : 0 < C := by have := s.property.1; dsimp [C]; positivity
  have hfac : W * (1 + 1 / (s.val + 1)) ≤ C := by
    have hdiv : 1 / (s.val + 1) ≤ 1 / s.val :=
      one_div_le_one_div_of_le s.property.1 (by linarith)
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro M hM K n hn hhalf
  have hends (b : Fin ((n : ℕ) - 1)) :=
    reference_endpoint_tails_internal s M hM K n hn hhalf W hW.le (hb M hM K) b
  have hconv {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (hda : d ≤ a) :
      a ^ (-s.val - 1) ≤ a ^ (-s.val) * d⁻¹ := by
    rw [Real.rpow_sub ha, Real.rpow_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using one_div_le_one_div_of_le hd hda) (by positivity)
  have he (b : Fin ((n : ℕ) - 1)) :
      IntervalBoundary.prefixCoefficient M n hn (referenceWeight s M hM K) (b.val + 1) ≤
        C * (b.val + 1 : ℝ) ^ (-s.val) *
          ((min (b.val + 1) ((n : ℕ) - b.val) : ℕ) : ℝ)⁻¹ ∧
      IntervalBoundary.suffixCoefficient M n hn (referenceWeight s M hM K) (b.val + 1) ≤
        C * ((n : ℝ) - b.val - 1) ^ (-s.val) *
          ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ)⁻¹ := by
    have hbn := b.isLt
    have hd0 : (0 : ℝ) < (min (b.val + 1) ((n : ℕ) - b.val) : ℕ) := by exact_mod_cast (show 0 < min (b.val + 1) ((n : ℕ) - b.val) by omega)
    have hd1 : (0 : ℝ) < (min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) := by exact_mod_cast (show 0 < min (b.val + 2) ((n : ℕ) - (b.val + 1)) by omega)
    have hspos : 0 < (n : ℝ) - b.val - 1 := by
      have hh : (b.val + 1 : ℝ) < n := by exact_mod_cast (show b.val + 1 < (n : ℕ) by omega)
      linarith
    have hsle : ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ) ≤ (n : ℝ) - b.val - 1 := by
      have hh : min (b.val + 2) ((n : ℕ) - (b.val + 1)) + (b.val + 1) ≤ (n : ℕ) := by omega
      have hhR : ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ) + (b.val + 1) ≤ n := by exact_mod_cast hh
      linarith
    constructor
    · apply (hends b).1.trans
      calc
        _ ≤ C * (b.val + 1 : ℝ) ^ (-s.val - 1) := mul_le_mul_of_nonneg_right hfac (by positivity)
        _ ≤ _ := by
          have h := hconv (a := (b.val + 1 : ℝ)) (by positivity) hd0
            (by exact_mod_cast min_le_left (b.val + 1) ((n : ℕ) - b.val))
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hC.le
    · apply (hends b).2.trans
      calc
        _ ≤ C * ((n : ℝ) - b.val - 1) ^ (-s.val - 1) := mul_le_mul_of_nonneg_right hfac (by positivity)
        _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hconv hspos hd1 hsle) hC.le
  have hf := reference_full_tail_internal s M hM K n hn hhalf W hW.le (hb M hM K)
  refine ⟨he, hf, ?_⟩
  intro i
  have hg := grouped_diagonal_bound_internal s n _ _ _ C hC.le
    (fun b => (he b).1) (fun b => (he b).2) hf i
  rw [← referenceCrossing_grouped s M hM K n hn hhalf] at hg
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hl : 5 + 4 * Real.log (n : ℝ) ≤ (5 / Real.log 2 + 4) * Real.log (2 * (n : ℝ)) := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hln := Real.log_nonneg hn1
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    have hh := div_mul_cancel₀ (5 : ℝ) h2.ne'
    nlinarith [mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 5) h2.le) hln]
  apply hg.trans
  calc
    _ ≤ C * ((5 / Real.log 2 + 4) * Real.log (2 * (n : ℝ))) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hC.le) (by positivity)
    _ = _ := by ring

private theorem suffix_length_nonneg (n : ℕ+) (b : Fin ((n : ℕ) - 1)) :
    (0 : ℝ) ≤ (n : ℝ) - b.val - 1 := by
  have hh : (b.val + 1 : ℝ) ≤ n := by
    exact_mod_cast (show b.val + 1 ≤ (n : ℕ) by have := b.isLt; omega)
  linarith

/-- The four estimates of the proof of Lemma 5.6 for
one crossing block. Indices are zero-based. Here `b+1` is the paper's cut `j`.
All depth and length bases are positive on the stated finite carriers. -/
def EndpointBounds (s : Riesz1.RieszExponent) (n : ℕ+) (E : ℝ)
    (S : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (u v : Fin ((n : ℕ) - 1) → ℝ) (d : ℝ) : Prop :=
  (∀ b, u b ≤ E * (b.val + 1 : ℝ) ^ (-s.val) *
      ((min (b.val + 1) ((n : ℕ) - b.val) : ℕ) : ℝ)⁻¹ ∧
    v b ≤ E * ((n : ℝ) - b.val - 1) ^ (-s.val) *
      ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ)⁻¹) ∧
  d ≤ E * (n : ℝ) ^ (-s.val) ∧
  ∀ i, S i i ≤ E * Real.log (2 * (n : ℝ)) *
    ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val)

/-- Internal enlargement of the common prefactor of the four endpoint bounds. -/
theorem endpointBounds_mono_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    {E F : ℝ} (hEF : E ≤ F) (S : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (u v : Fin ((n : ℕ) - 1) → ℝ) (d : ℝ) (h : EndpointBounds s n E S u v d) :
    EndpointBounds s n F S u v d := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  refine ⟨fun b => ⟨(h.1 b).1.trans ?_, (h.1 b).2.trans ?_⟩,
    h.2.1.trans ?_, fun i => (h.2.2 i).trans ?_⟩
  all_goals gcongr
  all_goals exact Real.rpow_nonneg (suffix_length_nonneg n _) _

/-- See the proof of Lemma 5.6 in the paper, complete: one common
prefactor works for both actual crossing blocks and all four clauses. The
loss is quantified before ε and β. The reference period and cutoff remain
arbitrary, so this includes the prescribed construction. -/
theorem boundary_intervals_endpoints (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ β : InverseTemperature,
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
        2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
        ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
        2 * (n : ℕ) ≤ (M : ℕ) →
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ →
        EndpointBounds s n (C * (n : ℝ) ^ (κ * ε))
          (physicalCrossing β s n m x) (physicalPrefix β s n m x)
          (physicalSuffix β s n m x) (physicalFull β s n m x) ∧
        EndpointBounds s n (C * (n : ℝ) ^ (κ * ε))
          (referenceCrossing s M hM K n hnM)
          (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
          (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
          (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)) := by
  obtain ⟨R, hR, href⟩ := reference_endpoint_bounds s
  let B := 5 / Real.log 2 + 4
  have hB : 1 ≤ B := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [B]
    have : 0 ≤ 5 / Real.log 2 := by positivity
    linarith
  let κ := max κ₀ 0 + 6
  have hκ : 0 < κ := by dsimp [κ]; have := le_max_right κ₀ 0; linarith
  refine ⟨κ, hκ, ?_⟩
  intro ε hε β
  let C := (128 + R) * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n m hn M hM hnM K hhalf x hx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hpow : (n : ℝ) ^ ((κ₀ + 6) * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith [le_max_left κ₀ 0])
  have hp1 : 1 ≤ (n : ℝ) ^ (κ * ε) := Real.one_le_rpow hn1 (mul_nonneg hκ.le hε.le)
  have hphys : 128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε) ≤ C * (n : ℝ) ^ (κ * ε) := by
    have hc : 128 * B ≤ C := by dsimp [C]; nlinarith
    exact mul_le_mul hc hpow (by positivity) (by positivity)
  have hrefC : R * B ≤ C * (n : ℝ) ^ (κ * ε) := by
    have hc : R * B ≤ C := by dsimp [C]; nlinarith
    exact hc.trans (le_mul_of_one_le_right hC.le hp1)
  have hP : EndpointBounds s n (128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε))
      (physicalCrossing β s n m x) (physicalPrefix β s n m x)
      (physicalSuffix β s n m x) (physicalFull β s n m x) := by
    have hc : 128 * (n : ℝ) ^ ((κ₀ + 6) * ε) ≤
        128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε) := by gcongr; nlinarith
    refine ⟨fun b => ⟨(physical_prefix_bound β s ε κ₀ hε.le n m hn x hx b).trans ?_,
      (physical_suffix_bound β s ε κ₀ hε.le n m hn x hx b).trans ?_⟩, ?_, ?_⟩
    · gcongr
    · gcongr
      exact Real.rpow_nonneg (suffix_length_nonneg n _) _
    · apply (physical_full_bound β s n m hn ε κ₀ x hx).trans
      have hp := Real.rpow_le_rpow_of_exponent_le hn1
        (show κ₀ * ε ≤ (κ₀ + 6) * ε by nlinarith)
      have hc1 : (n : ℝ) ^ (κ₀ * ε) ≤ 128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε) :=
        hp.trans (le_mul_of_one_le_left (by positivity) (by nlinarith))
      exact mul_le_mul_of_nonneg_right hc1 (by positivity)
    · exact physical_diagonal_bound β s ε κ₀ hε.le n m hn x hx
  have hr := href M hM K n hnM hhalf
  have hQ : EndpointBounds s n (R * B) (referenceCrossing s M hM K n hnM)
      (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)) := by
    have hc : R ≤ R * B := le_mul_of_one_le_right hR.le hB
    refine ⟨fun b => ⟨(hr.1 b).1.trans ?_, (hr.1 b).2.trans ?_⟩, hr.2.1.trans ?_, hr.2.2⟩
    all_goals gcongr
    all_goals exact Real.rpow_nonneg (suffix_length_nonneg n _) _
  exact ⟨endpointBounds_mono_internal s n hphys _ _ _ _ hP,
    endpointBounds_mono_internal s n hrefC _ _ _ _ hQ⟩

private theorem depth_pos (n : ℕ+) (i : Fin (n : ℕ)) :
    (0 : ℝ) < ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) := by
  exact_mod_cast (show 0 < min (i.val + 1) ((n : ℕ) - i.val) by have := i.isLt; omega)

/-- Internal interpolation of a length power against two positive depths.
It is the power comparison in the increment proof of Lemma 5.6. -/
theorem endpoint_power_internal (s : Riesz1.RieszExponent) {a d p q : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q)
    (hpa : p ≤ a) (hqa : q ≤ a) (hqd : q ≤ d) :
    a ^ (-s.val) * d⁻¹ ≤ p ^ (-s.val / 2) * q ^ (-1 - s.val / 2) := by
  have hs : -s.val / 2 ≤ 0 := by linarith [s.property.1]
  have h1 := Real.rpow_le_rpow_of_nonpos hp hpa hs
  have h2 := Real.rpow_le_rpow_of_nonpos hq hqa hs
  have h3 : d⁻¹ ≤ q⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hq hqd
  calc
    _ = (a ^ (-s.val / 2) * a ^ (-s.val / 2)) * d⁻¹ := by
      rw [← Real.rpow_add ha]
      congr 2
      ring
    _ ≤ (p ^ (-s.val / 2) * q ^ (-s.val / 2)) * q⁻¹ :=
      mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hq]
      congr 2
      ring

/-- Internal positive-block entry estimate from the actual diagonal bounds. -/
theorem grouped_entry_bound_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (E : ℝ) (hE : 0 ≤ E) (u v : Fin ((n : ℕ) - 1) → ℝ) (d : ℝ)
    (hu : ∀ b, 0 ≤ u b) (hv : ∀ b, 0 ≤ v b) (hd : 0 ≤ d)
    (h : EndpointBounds s n E (groupedBoundaryMatrix n u v d) u v d)
    (i j : Fin (n : ℕ)) :
    |groupedBoundaryMatrix n u v d i j| ≤ E * Real.log (2 * (n : ℝ)) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) := by
  let S := groupedBoundaryMatrix n u v d
  have hS := groupedBoundaryMatrix_posSemidef n u v d hu hv hd
  have hsq := groupedBoundaryMatrix_entry_sq n u v d hu hv hd i j
  have hhalf (a : Fin (n : ℕ)) :
      (((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ) ^ (-s.val / 2)) ^ 2 =
        ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ) ^ (-s.val) := by
    rw [pow_two, ← Real.rpow_add (depth_pos n a)]
    congr 1
    ring
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hprod := mul_le_mul (h.2.2 i) (h.2.2 j)
    (show 0 ≤ groupedBoundaryMatrix n u v d j j from hS.diag_nonneg) (by have := depth_pos n i; have := n.pos; positivity)
  apply abs_le_of_sq_le_sq _ (by have := depth_pos n i; have := depth_pos n j; have := n.pos; positivity)
  apply hsq.trans
  apply hprod.trans_eq
  rw [mul_pow, mul_pow, hhalf i, hhalf j]
  ring

/-- Telescoping estimate from coefficient bounds. -/
theorem grouped_increment_bound_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (E : ℝ) (hE : 0 ≤ E) (u v : Fin ((n : ℕ) - 1) → ℝ) (d : ℝ)
    (hu : ∀ b, 0 ≤ u b) (hv : ∀ b, 0 ≤ v b)
    (h : EndpointBounds s n E (groupedBoundaryMatrix n u v d) u v d)
    (i j l : Fin (n : ℕ)) :
    |groupedBoundaryMatrix n u v d i j - groupedBoundaryMatrix n u v d i l| ≤
      E * (Nat.dist j.val l.val : ℝ) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
        (min (((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ))
          (((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2) := by
  let D (a : Fin (n : ℕ)) : ℝ := ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
  have hp (a : Fin (n : ℕ)) : 0 < D a := depth_pos n a
  have hord (j l : Fin (n : ℕ)) (hjl : j.val ≤ l.val) :
      |groupedBoundaryMatrix n u v d i j - groupedBoundaryMatrix n u v d i l| ≤
        E * (Nat.dist j.val l.val : ℝ) * (D i) ^ (-s.val / 2) *
          (min (D j) (D l)) ^ (-1 - s.val / 2) := by
    let q := min (D j) (D l)
    have hq : 0 < q := lt_min (hp j) (hp l)
    have hdepth (k : ℕ) (hk : j.val ≤ k) (hkl : k ≤ l.val) :
        q ≤ ((min (k + 1) ((n : ℕ) - k) : ℕ) : ℝ) := by
      dsimp [q, D]
      rw [← Nat.cast_min]
      exact_mod_cast (show min (min (j.val + 1) ((n : ℕ) - j.val))
        (min (l.val + 1) ((n : ℕ) - l.val)) ≤ min (k + 1) ((n : ℕ) - k) by
          have := j.isLt; have := l.isLt; omega)
    let f : ℕ → ℝ := fun k => groupedBoundaryMatrix n u v d i
      ⟨k % (n : ℕ), Nat.mod_lt _ n.pos⟩
    have hf (a : Fin (n : ℕ)) : f a.val = groupedBoundaryMatrix n u v d i a := by
      dsimp [f]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
    have hstep (k : ℕ) (hk : k ∈ Finset.Ico j.val l.val) :
        |f (k + 1) - f k| ≤ E * (D i) ^ (-s.val / 2) * q ^ (-1 - s.val / 2) := by
      have hks := Finset.mem_Ico.mp hk
      have hkn : k + 1 < (n : ℕ) := by have := l.isLt; omega
      let b : Fin ((n : ℕ) - 1) := ⟨k, by omega⟩
      have he : f (k + 1) - f k = if i.val ≤ k then -u b else v b := by
        have hinc := groupedBoundaryMatrix_increment n u v d i b
        simpa only [f, b, Nat.mod_eq_of_lt hkn, Nat.mod_eq_of_lt (show k < (n : ℕ) by omega)] using hinc
      rw [he]
      by_cases hik : i.val ≤ k
      · rw [ite_eq_left hik, abs_neg, abs_of_nonneg (hu b)]
        apply (h.1 b).1.trans
        have hpa : D i ≤ (k + 1 : ℝ) := by dsimp [D]; exact_mod_cast (show min (i.val + 1) ((n : ℕ) - i.val) ≤ k + 1 by omega)
        have hqa : q ≤ (k + 1 : ℝ) := (hdepth k hks.1 hks.2.le).trans (by exact_mod_cast min_le_left (k + 1) ((n : ℕ) - k))
        have hb := endpoint_power_internal s (by positivity) (hp ⟨k, by omega⟩) (hp i) hq
          hpa hqa (hdepth k hks.1 hks.2.le)
        simpa only [b, mul_assoc] using mul_le_mul_of_nonneg_left hb hE
      · rw [ite_eq_right hik, abs_of_nonneg (hv b)]
        apply (h.1 b).2.trans
        have hapos : 0 < (n : ℝ) - k - 1 := by
          have hh : (k + 1 : ℝ) < n := by exact_mod_cast hkn
          linarith
        have hpa : D i ≤ (n : ℝ) - k - 1 := by
          have hh : min (i.val + 1) ((n : ℕ) - i.val) + k + 1 ≤ (n : ℕ) := by have := i.isLt; omega
          have hhR : D i + k + 1 ≤ (n : ℝ) := by dsimp [D]; exact_mod_cast hh
          linarith
        have hqa : q ≤ (n : ℝ) - k - 1 := by
          have hmin : ((min (k + 2) ((n : ℕ) - (k + 1)) : ℕ) : ℝ) ≤
              (((n : ℕ) - (k + 1) : ℕ) : ℝ) := by exact_mod_cast min_le_right (k + 2) ((n : ℕ) - (k + 1))
          have hh := (hdepth (k + 1) (by omega) (by omega)).trans hmin
          rw [Nat.cast_sub (by omega : k + 1 ≤ (n : ℕ))] at hh
          push_cast at hh
          linarith
        have hb := endpoint_power_internal s hapos (hp ⟨k + 1, hkn⟩) (hp i) hq
          hpa hqa (hdepth (k + 1) (by omega) (by omega))
        simpa only [b, D, mul_assoc] using mul_le_mul_of_nonneg_left hb hE
    rw [← hf j, ← hf l, abs_sub_comm, ← Finset.sum_Ico_sub f hjl]
    calc
      _ ≤ ∑ k ∈ Finset.Ico j.val l.val, |f (k + 1) - f k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico j.val l.val, E * (D i) ^ (-s.val / 2) * q ^ (-1 - s.val / 2) :=
        Finset.sum_le_sum hstep
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, Nat.dist_eq_sub_of_le hjl]
        dsimp [q]
        ring
  rcases le_total j.val l.val with hjl | hlj
  · exact hord j l hjl
  · simpa only [abs_sub_comm, Nat.dist_comm l.val j.val, min_comm (D l) (D j)] using hord l j hlj

/-- See Lemma 5.6 of the paper, complete: entries and all ordinary
column increments of the actual boundary remainder. The loss precedes ε and β,
all prefactors precede the system sizes, and singleton windows are included. -/
theorem boundary_intervals (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ β : InverseTemperature,
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
        2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
        ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
        2 * (n : ℕ) ≤ (M : ℕ) →
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ i j l : Fin (n : ℕ),
        |boundaryRemainder β s n m M hM hnM K x i j| ≤
          C * (n : ℝ) ^ (κ * ε) *
            ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
            ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) ∧
        |boundaryRemainder β s n m M hM hnM K x i j -
          boundaryRemainder β s n m M hM hnM K x i l| ≤
          C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
            (min (((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ))
              (((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2) := by
  obtain ⟨κ, hκ, hb⟩ := boundary_intervals_endpoints s κ₀
  refine ⟨κ + 1, by linarith, ?_⟩
  intro ε hε β
  obtain ⟨C, hC, hbound⟩ := hb ε hε β
  let A := Real.log 2 + 1 / ε + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 1 ≤ A := by dsimp [A]; have := one_div_pos.mpr hε; linarith
  refine ⟨2 * C * A, by positivity, ?_⟩
  intro n m hn M hM hnM K hhalf x hx i j l
  let E := C * (n : ℝ) ^ (κ * ε)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp := physicalCrossing_grouped β s n m hn x
  have hr := referenceCrossing_grouped s M hM K n hnM hhalf
  obtain ⟨hP, hR⟩ := hbound n m hn M hM hnM K hhalf x hx
  have hPG : EndpointBounds s n E
      (groupedBoundaryMatrix n (physicalPrefix β s n m x) (physicalSuffix β s n m x)
        (physicalFull β s n m x))
      (physicalPrefix β s n m x) (physicalSuffix β s n m x) (physicalFull β s n m x) := by
    simpa only [← hp] using hP
  have hRG : EndpointBounds s n E
      (groupedBoundaryMatrix n
        (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
        (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
        (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)))
      (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)) := by
    simpa only [← hr] using hR
  have hpu (b) : 0 ≤ physicalPrefix β s n m x b := physicalGroup_nonneg β s n m x _
  have hpv (b) : 0 ≤ physicalSuffix β s n m x b := physicalGroup_nonneg β s n m x _
  have hpd : 0 ≤ physicalFull β s n m x := physicalGroup_nonneg β s n m x _
  have hru (b : Fin ((n : ℕ) - 1)) :=
    (referenceCoefficients_nonneg s M hM K n hnM (b.val + 1)).1
  have hrv (b : Fin ((n : ℕ) - 1)) :=
    (referenceCoefficients_nonneg s M hM K n hnM (b.val + 1)).2.1
  have hrd := (referenceCoefficients_nonneg s M hM K n hnM 0).2.2
  have hpe := grouped_entry_bound_internal s n E hE _ _ _ hpu hpv hpd hPG i j
  have hre := grouped_entry_bound_internal s n E hE _ _ _ hru hrv hrd hRG i j
  have hpi := grouped_increment_bound_internal s n E hE _ _ _ hpu hpv hPG i j l
  have hri := grouped_increment_bound_internal s n E hE _ _ _ hru hrv hRG i j l
  rw [← hp] at hpe hpi
  rw [← hr] at hre hri
  have hlog : Real.log (2 * (n : ℝ)) ≤ A * (n : ℝ) ^ ε := by
    have hnε : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
    have hl := Real.log_le_rpow_div hn0.le hε
    rw [div_eq_mul_inv] at hl
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    dsimp [A]
    rw [one_div]
    nlinarith [mul_le_mul_of_nonneg_left hnε hlog2.le]
  have hpow : (n : ℝ) ^ (κ * ε) * (n : ℝ) ^ ε = (n : ℝ) ^ ((κ + 1) * ε) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hfac : 2 * E * Real.log (2 * (n : ℝ)) ≤ 2 * C * A * (n : ℝ) ^ ((κ + 1) * ε) := by
    calc
      _ ≤ 2 * E * (A * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by dsimp [E]; rw [← hpow]; ring
  have hfac' : 2 * E ≤ 2 * C * A * (n : ℝ) ^ ((κ + 1) * ε) := by
    have hpε : (n : ℝ) ^ (κ * ε) ≤ (n : ℝ) ^ ((κ + 1) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
    calc
      _ ≤ 2 * C * (n : ℝ) ^ ((κ + 1) * ε) := by dsimp [E]; nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (Real.rpow_nonneg hn0.le ((κ + 1) * ε))]
  constructor
  · change |physicalCrossing β s n m x i j - referenceCrossing s M hM K n hnM i j| ≤ _
    apply (abs_sub _ _).trans
    apply (add_le_add hpe hre).trans
    calc
      _ = (2 * E * Real.log (2 * (n : ℝ))) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) := by ring
      _ ≤ _ := by gcongr
  · change |(physicalCrossing β s n m x i j - referenceCrossing s M hM K n hnM i j) -
      (physicalCrossing β s n m x i l - referenceCrossing s M hM K n hnM i l)| ≤ _
    have heq : (physicalCrossing β s n m x i j - referenceCrossing s M hM K n hnM i j) -
        (physicalCrossing β s n m x i l - referenceCrossing s M hM K n hnM i l) =
        (physicalCrossing β s n m x i j - physicalCrossing β s n m x i l) -
        (referenceCrossing s M hM K n hnM i j - referenceCrossing s M hM K n hnM i l) := by ring
    rw [heq]
    apply (abs_sub _ _).trans
    apply (add_le_add hpi hri).trans
    calc
      _ = (2 * E) * (Nat.dist j.val l.val : ℝ) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          (min (((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ))
            (((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2) := by ring
      _ ≤ _ := by gcongr

end Riesz2.BoundaryEntries
