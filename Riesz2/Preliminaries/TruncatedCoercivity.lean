/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.InverseIntervalKernelPart2
public import Riesz2.ToMathlib.FiniteMatrixOrder

/-!
# Coercivity of the truncated interval matrix

Consecutive interval sums recover each coordinate. Averaging this identity over
lengths from `K` to `2K` gives a lower bound uniform in the cycle size.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast MatrixOrder
open Matrix Finset

namespace Riesz2

/-- Sum over the interval equals the consecutive-coordinate sum
when the interval has no repeated labels. -/
theorem sum_cyclicIndexInterval_eq_cyclicGapSum (N : ℕ+) (i : Fin (N : ℕ))
    {r : ℕ} (hr : r ≤ (N : ℕ)) (u : Fin (N : ℕ) → ℝ) :
    (∑ j ∈ cyclicIndexInterval N i r, u j) = cyclicGapSum N i r u := by
  unfold cyclicIndexInterval cyclicGapSum
  apply Finset.sum_image
  have hcard := card_cyclicIndexInterval N i hr
  unfold cyclicIndexInterval at hcard
  apply Finset.card_image_iff.mp
  simpa only [Finset.card_range] using hcard

private theorem cyclicGapSum_eq_fin_add (N : ℕ+) (i : Fin (N : ℕ))
    (r : ℕ) (u : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i r u = ∑ a ∈ Finset.range r, u (i + (↑a : Fin (N : ℕ))) := by
  unfold cyclicGapSum
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

/-- Consecutive interval sums recover the initial coordinate, including wraparound. -/
theorem cyclicGapSum_succ_sub (N : ℕ+) (i : Fin (N : ℕ))
    (r : ℕ) (u : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i (r + 1) u - cyclicGapSum N (i + 1) r u = u i := by
  simp only [cyclicGapSum_eq_fin_add]
  rw [Finset.sum_range_succ']
  have hshift : (∑ a ∈ Finset.range r, u (i + (↑(a + 1) : Fin (N : ℕ)))) =
      ∑ a ∈ Finset.range r, u (i + 1 + (↑a : Fin (N : ℕ))) := by
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    push_cast
    abel
  rw [hshift]
  simp

/-- The unweighted interval estimate in Subsection 2.5. The endpoint
length `2K` is included. -/
theorem cyclicGapSum_block_coercivity (N : ℕ+) (K : ℕ) (u : Fin (N : ℕ) → ℝ) :
    (K : ℝ) * (∑ i, u i ^ 2) ≤
      4 * ∑ r ∈ Finset.Icc K (2 * K), ∑ i, cyclicGapSum N i r u ^ 2 := by
  let A := fun r => ∑ i, cyclicGapSum N i r u ^ 2
  have hA (r : ℕ) : 0 ≤ A r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hstep (r : ℕ) : (∑ i, u i ^ 2) ≤ 2 * (A r + A (r + 1)) := by
    have h (i : Fin (N : ℕ)) : u i ^ 2 ≤
        2 * (cyclicGapSum N i (r + 1) u ^ 2 + cyclicGapSum N (i + 1) r u ^ 2) := by
      rw [← cyclicGapSum_succ_sub N i r u]
      nlinarith [sq_nonneg (cyclicGapSum N i (r + 1) u + cyclicGapSum N (i + 1) r u)]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    have hp : (∑ i : Fin (N : ℕ), cyclicGapSum N (i + 1) r u ^ 2) = A r := by
      exact Equiv.sum_comp (Equiv.addRight (1 : Fin (N : ℕ)))
        (fun i : Fin (N : ℕ) => cyclicGapSum N i r u ^ 2)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
    rw [hp] at hsum
    dsimp [A] at *
    linarith
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.Ico K (2 * K)) => hstep r)
  have hfirst : (∑ r ∈ Finset.Ico K (2 * K), A r) ≤ ∑ r ∈ Finset.Icc K (2 * K), A r :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro r hr; simp only [Finset.mem_Ico, Finset.mem_Icc] at hr ⊢; omega)
      (fun r _ _ => hA r)
  have hsecond : (∑ r ∈ Finset.Ico K (2 * K), A (r + 1)) ≤
      ∑ r ∈ Finset.Icc K (2 * K), A r := by
    rw [Finset.sum_Ico_add' A K (2 * K) 1]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hr ⊢
      omega
    · intro r _ _
      exact hA r
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    show 2 * K - K = K by omega, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  dsimp [A] at *
  linarith

/-- The quadratic form of the literal truncated matrix. -/
theorem referenceIntervalMatrix_dotProduct (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (u : Fin (N : ℕ) → ℝ) :
    u ⬝ᵥ (referenceIntervalMatrix s N hN K *ᵥ u) =
      ∑ i : Fin (N : ℕ),
        ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r),
          (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
            (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2 := by
  convert referenceIntervalMatrix_quadratic s N hN K u using 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Symmetry of the literal truncated matrix, for every cutoff. -/
theorem referenceIntervalMatrix_isHermitian (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) :
    (referenceIntervalMatrix s N hN K).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, star_trivial, referenceIntervalMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem interval_coefficient_nonneg (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ (N : ℕ) / 2) :
    0 ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) := by
  have hne : (↑r : Fin (N : ℕ)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega : r < (N : ℕ))] at hv
    omega
  apply mul_nonneg _ (sampledSecondDifference_pos s N hN hne).le
  split_ifs <;> norm_num

/-- Removing positive interval terms preserves the Loewner order. This proves
the first two inequalities of Subsection 2.5 for every cutoff. -/
theorem referenceIntervalMatrix_nonneg_le_full (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) :
    0 ≤ referenceIntervalMatrix s N hN K ∧
      referenceIntervalMatrix s N hN K ≤
        Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)) := by
  have hterm (i : Fin (N : ℕ)) (r : ℕ)
      (hr : r ∈ Finset.range ((N : ℕ) / 2 + 1)) (hr1 : 1 ≤ r)
      (u : Fin (N : ℕ) → ℝ) :
      0 ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
        (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2 :=
    mul_nonneg (interval_coefficient_nonneg s N hN hr1 (by simp only [Finset.mem_range] at hr; omega))
      (sq_nonneg _)
  have hpos : (referenceIntervalMatrix s N hN K).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨referenceIntervalMatrix_isHermitian s N hN K, ?_⟩
    intro u
    simp only [star_trivial]
    rw [referenceIntervalMatrix_dotProduct]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun r hr =>
      hterm i r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2.1 u
  refine ⟨Matrix.nonneg_iff_posSemidef.mpr hpos, ?_⟩
  have hfull : referenceIntervalMatrix s N hN 1 =
      Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)) := by
    ext a b
    exact referenceIntervalMatrix_full s N hN a b
  rw [← hfull]
  apply (FiniteMatrixOrder.le_iff_forall_dotProduct_mulVec_le
    (referenceIntervalMatrix_isHermitian s N hN K)
    (referenceIntervalMatrix_isHermitian s N hN 1)).mpr
  intro u
  simp only [referenceIntervalMatrix_dotProduct]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.1⟩
  · intro r hr _
    exact hterm i r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2.1 u

/-- See Subsection 2.5 of the paper: the truncation is nonnegative, bounded by the
full sampled matrix, and uniformly coercive with scale `K^(-1-s)`. -/
theorem referenceIntervalMatrix_truncated_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 →
      0 ≤ referenceIntervalMatrix s N hN K ∧
      referenceIntervalMatrix s N hN K ≤
        Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)) ∧
      (c * (K : ℝ) ^ (-1 - s.val)) • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤
        referenceIntervalMatrix s N hN K := by
  obtain ⟨c, _, hc, _, hcurv⟩ := sampledSecondDifference_bounds s
  refine ⟨c / 8 * (2 : ℝ) ^ (-s.val - 2), by positivity, ?_⟩
  intro N hN K hK hKN
  obtain ⟨hpos, hupper⟩ := referenceIntervalMatrix_nonneg_le_full s N hN K
  refine ⟨hpos, hupper, ?_⟩
  apply (FiniteMatrixOrder.smul_one_le_iff
    (referenceIntervalMatrix_isHermitian s N hN K) _).mpr
  intro u
  let Q := fun r => ∑ i, cyclicGapSum N i r u ^ 2
  let L := (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r)
  let w := fun r => (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
    sampledSecondDifference s N hN (↑r : Fin (N : ℕ))
  let a := c / 2 * (2 * (K : ℝ)) ^ (-s.val - 2)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ (r : ℕ) : 0 ≤ Q r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw (r : ℕ) (hr : r ∈ L) : 0 ≤ w r := by
    have hr' := Finset.mem_filter.mp hr
    exact interval_coefficient_nonneg s N hN hr'.2.1
      (by have := Finset.mem_range.mp hr'.1; omega)
  have hquad : u ⬝ᵥ (referenceIntervalMatrix s N hN K *ᵥ u) = ∑ r ∈ L, w r * Q r := by
    rw [referenceIntervalMatrix_dotProduct, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    have hrN : r ≤ (N : ℕ) := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      omega
    simp_rw [sum_cyclicIndexInterval_eq_cyclicGapSum N _ hrN]
    exact (Finset.mul_sum _ _ _).symm
  have hsub : Finset.Icc K (2 * K) ⊆ L := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    simp only [L, Finset.mem_filter, Finset.mem_range]
    omega
  have hcoeff (r : ℕ) (hr : r ∈ Finset.Icc K (2 * K)) : a ≤ w r := by
    have hr' := Finset.mem_Icc.mp hr
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hrhalf : r ≤ (N : ℕ) / 2 := by omega
    have hrlt : r < (N : ℕ) := by omega
    have hne : (↑r : Fin (N : ℕ)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hrlt] at hv
      omega
    have hd : Riesz1.cyclicIndexDistance N (↑r : Fin (N : ℕ)) 0 = r := by
      simp only [Riesz1.cyclicIndexDistance, Fin.val_natCast, Fin.val_zero,
        Nat.mod_eq_of_lt hrlt, Nat.dist_zero_right]
      omega
    have hlow := (hcurv N hN (↑r : Fin (N : ℕ)) hne).1
    rw [hd] at hlow
    have hweight : (1 / 2 : ℝ) ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have hpow : (2 * (K : ℝ)) ^ (-s.val - 2) ≤ (r : ℝ) ^ (-s.val - 2) :=
      Real.rpow_le_rpow_of_nonpos hrpos
        (by exact_mod_cast hr'.2) (by linarith [s.property.1])
    calc a = (1 / 2 : ℝ) * (c * (2 * (K : ℝ)) ^ (-s.val - 2)) := by dsimp [a]; ring
      _ ≤ (1 / 2 : ℝ) * (c * (r : ℝ) ^ (-s.val - 2)) := by gcongr
      _ ≤ w r := mul_le_mul hweight hlow (by positivity) (by linarith)
  have henergy : a * (∑ r ∈ Finset.Icc K (2 * K), Q r) ≤
      u ⬝ᵥ (referenceIntervalMatrix s N hN K *ᵥ u) := by
    rw [hquad, Finset.mul_sum]
    calc (∑ r ∈ Finset.Icc K (2 * K), a * Q r)
        ≤ ∑ r ∈ Finset.Icc K (2 * K), w r * Q r :=
          Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_right (hcoeff r hr) (hQ r)
      _ ≤ ∑ r ∈ L, w r * Q r := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun r hr _ => mul_nonneg (hw r hr) (hQ r))
  have hblock := cyclicGapSum_block_coercivity N K u
  have hscale : a * (K : ℝ) / 4 =
      (c / 8 * (2 : ℝ) ^ (-s.val - 2)) * (K : ℝ) ^ (-1 - s.val) := by
    dsimp [a]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hKpos.le]
    have hpow : (K : ℝ) ^ (-s.val - 2) * (K : ℝ) = (K : ℝ) ^ (-1 - s.val) := by
      rw [← Real.rpow_add_one hKpos.ne']
      congr 1
      ring
    calc c / 2 * ((2 : ℝ) ^ (-s.val - 2) * (K : ℝ) ^ (-s.val - 2)) * (K : ℝ) / 4 =
        c / 8 * (2 : ℝ) ^ (-s.val - 2) * ((K : ℝ) ^ (-s.val - 2) * (K : ℝ)) := by ring
      _ = _ := by rw [hpow]
  have hbound : a * (K : ℝ) / 4 * (∑ i, u i ^ 2) ≤
      a * (∑ r ∈ Finset.Icc K (2 * K), Q r) := by
    have h := mul_le_mul_of_nonneg_left hblock ha.le
    dsimp [Q]
    nlinarith
  rw [hscale] at hbound
  simpa only [dotProduct, sq] using hbound.trans henergy

end Riesz2
