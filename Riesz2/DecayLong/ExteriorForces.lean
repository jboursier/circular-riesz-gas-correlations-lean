/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.TruncatedCoercivity
public import Riesz2.Preliminaries.InverseRieszMatrix
public import Riesz2.ToMathlib.SubcriticalPowerSum
public import Riesz2.ToMathlib.RpowPartialSums
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Exterior covariance forms of the truncated reference matrix

The reference Hessian is twice the interval matrix. Principal
submatrices below are restrictions of this Hessian, including the empty block.
The covariance comparisons are deterministic quadratic-form statements used in
the proof of Lemma 5.5.
-/

@[expose] public section

noncomputable section

open scoped BigOperators MatrixOrder Fin.NatCast
open Matrix

namespace Riesz2.ExteriorForces

private theorem symmetric_pair {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (u v : ι → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  have ht : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [dotProduct_mulVec, ← vecMul_transpose A u, ht, dotProduct_comm]

private theorem inverse_solves {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : ι → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)), one_mulVec]

private theorem variational_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v u : ι → ℝ) :
    2 * (v ⬝ᵥ u) - u ⬝ᵥ (A *ᵥ u) ≤ v ⬝ᵥ (A⁻¹ *ᵥ v) := by
  have h := hA.posSemidef.dotProduct_mulVec_nonneg (u - A⁻¹ *ᵥ v)
  simp only [star_trivial, mulVec_sub, dotProduct_sub, sub_dotProduct,
    inverse_solves hA] at h
  rw [symmetric_pair hA.isHermitian (A⁻¹ *ᵥ v) u, inverse_solves hA,
    dotProduct_comm u v, dotProduct_comm (A⁻¹ *ᵥ v) v] at h
  linarith

private theorem variational_attained {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : ι → ℝ) :
    2 * (v ⬝ᵥ (A⁻¹ *ᵥ v)) -
      (A⁻¹ *ᵥ v) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ v)) = v ⬝ᵥ (A⁻¹ *ᵥ v) := by
  rw [inverse_solves hA, dotProduct_comm (A⁻¹ *ᵥ v) v]
  ring

private theorem interval_squares_sum_le (N : ℕ+) {r : ℕ} (hr : r ≤ (N : ℕ))
    (u : Fin (N : ℕ) → ℝ) :
    (∑ i, (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2) ≤
      (r : ℝ) ^ 2 * ∑ j, u j ^ 2 := by
  have hcs (i : Fin (N : ℕ)) : (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2 ≤
      (r : ℝ) * ∑ j ∈ cyclicIndexInterval N i r, u j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (cyclicIndexInterval N i r)
      (fun _ => (1 : ℝ)) u
    simpa only [one_mul, one_pow, Finset.sum_const,
      card_cyclicIndexInterval N i hr, nsmul_eq_mul, mul_one] using h
  have hshift (a : ℕ) :
      (∑ i : Fin (N : ℕ), u ⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩ ^ 2) =
      ∑ i, u i ^ 2 := by
    have hfun (i : Fin (N : ℕ)) :
        (⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)) =
          i + (a : Fin (N : ℕ)) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
    simp_rw [hfun]
    exact Equiv.sum_comp (Equiv.addRight (a : Fin (N : ℕ))) (fun i => u i ^ 2)
  have hsum : (∑ i : Fin (N : ℕ), ∑ j ∈ cyclicIndexInterval N i r, u j ^ 2) =
      (r : ℝ) * ∑ j, u j ^ 2 := by
    simp_rw [sum_cyclicIndexInterval_eq_cyclicGapSum N _ hr, cyclicGapSum]
    rw [Finset.sum_comm]
    simp_rw [hshift]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (∑ i, (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2)
      ≤ ∑ i, (r : ℝ) * ∑ j ∈ cyclicIndexInterval N i r, u j ^ 2 :=
        Finset.sum_le_sum fun i _ => hcs i
    _ = (r : ℝ) ^ 2 * ∑ j, u j ^ 2 := by rw [← Finset.mul_sum, hsum]; ring

/-- The deleted short intervals have operator size at most `C K^(1-s)`.
This is the first quantitative comparison in the proof of Lemma 5.5. -/
theorem deleted_intervals_bound (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 →
      Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)) -
        referenceIntervalMatrix s N hN K ≤
          (C * (K : ℝ) ^ (1 - s.val)) • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) := by
  obtain ⟨_, C, _, hC, hc⟩ := sampledSecondDifference_bounds s
  refine ⟨C / (1 - s.val), div_pos hC (by linarith [s.property.2]), ?_⟩
  intro N hN K hK hKN
  let W := fun r : ℕ =>
    (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s N hN (r : Fin (N : ℕ))
  have hfull : Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)) =
      referenceIntervalMatrix s N hN 1 := by
    ext a b
    exact (referenceIntervalMatrix_full s N hN a b).symm
  rw [hfull]
  have hsym := (referenceIntervalMatrix_isHermitian s N hN 1).sub
    (referenceIntervalMatrix_isHermitian s N hN K)
  apply (FiniteMatrixOrder.le_iff_forall_dotProduct_mulVec_le hsym
    (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (star_trivial _)))).mpr
  intro u
  have hq : u ⬝ᵥ ((referenceIntervalMatrix s N hN 1 -
      referenceIntervalMatrix s N hN K) *ᵥ u) =
      ∑ r ∈ Finset.Ico 1 K, W r * ∑ i, (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2 := by
    rw [sub_mulVec, dotProduct_sub, referenceIntervalMatrix_dotProduct,
      referenceIntervalMatrix_dotProduct]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    simp_rw [← Finset.mul_sum]
    have hsplit : (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ 1 ≤ r) =
        Finset.Ico 1 K ∪
          (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_union]
    · simp only [add_sub_cancel_right, W]
    · apply Finset.disjoint_left.mpr
      intro r hr hr'
      have := (Finset.mem_Ico.mp hr).2
      have := (Finset.mem_filter.mp hr').2.2
      omega
  have hterm (r : ℕ) (hr : r ∈ Finset.Ico 1 K) :
      W r * (∑ i, (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2) ≤
        C * (r : ℝ) ^ (-s.val) * ∑ j, u j ^ 2 := by
    obtain ⟨hr1, hrK⟩ := Finset.mem_Ico.mp hr
    have hrN : r < (N : ℕ) := by omega
    have hrhalf : r ≤ (N : ℕ) / 2 := by omega
    have hne : (r : Fin (N : ℕ)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hrN] at this
      omega
    have hd : Riesz1.cyclicIndexDistance N (r : Fin (N : ℕ)) 0 = r := by
      simp only [Riesz1.cyclicIndexDistance, Fin.val_natCast, Fin.val_zero,
        Nat.mod_eq_of_lt hrN, Nat.dist_zero_right]
      omega
    have hweight : 1 - (if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) = 1 := by
      rw [ite_eq_right (by omega)]
      ring
    have hW : 0 ≤ W r := by
      dsimp [W]
      rw [hweight, one_mul]
      exact (sampledSecondDifference_pos s N hN hne).le
    have hupper : W r ≤ C * (r : ℝ) ^ (-s.val - 2) := by
      simpa only [W, hweight, one_mul, hd] using (hc N hN _ hne).2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hscale : (r : ℝ) ^ (-s.val - 2) * (r : ℝ) ^ 2 = (r : ℝ) ^ (-s.val) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hrpos]
      congr 1
      push_cast
      ring
    calc W r * (∑ i, (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2)
        ≤ W r * ((r : ℝ) ^ 2 * ∑ j, u j ^ 2) :=
          mul_le_mul_of_nonneg_left (interval_squares_sum_le N (by omega) u) hW
      _ ≤ (C * (r : ℝ) ^ (-s.val - 2)) * ((r : ℝ) ^ 2 * ∑ j, u j ^ 2) :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = C * (r : ℝ) ^ (-s.val) * ∑ j, u j ^ 2 := by
        rw [mul_assoc C, ← mul_assoc _ _ (∑ j, u j ^ 2), hscale]
        ring
  have hsum : (∑ r ∈ Finset.Ico 1 K, (r : ℝ) ^ (-s.val)) ≤
      (K : ℝ) ^ (1 - s.val) / (1 - s.val) := by
    apply le_trans _ (subcritical_power_sum s.property.1 s.property.2 hK).2
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun r hr => Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hr).1,
        (Finset.mem_Ico.mp hr).2.le⟩)
      (fun r _ _ => Real.rpow_nonneg (Nat.cast_nonneg r) _)
  rw [hq, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  calc (∑ r ∈ Finset.Ico 1 K, W r * ∑ i, (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2)
      ≤ ∑ r ∈ Finset.Ico 1 K, C * (r : ℝ) ^ (-s.val) * ∑ j, u j ^ 2 :=
        Finset.sum_le_sum hterm
    _ = C * (∑ r ∈ Finset.Ico 1 K, (r : ℝ) ^ (-s.val)) * ∑ j, u j ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ C * ((K : ℝ) ^ (1 - s.val) / (1 - s.val)) * ∑ j, u j ^ 2 := by
      gcongr
    _ = C / (1 - s.val) * (K : ℝ) ^ (1 - s.val) * (u ⬝ᵥ u) := by
      simp only [dotProduct, sq]
      ring

/-- Positivity of the literal reference Hessian for every admissible cutoff.
This supplies the nonsingularity required in Subsection 5.1. -/
theorem referenceHessian_posDef (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ) / 4) :
    ((2 : ℝ) • referenceIntervalMatrix s N hN K).PosDef := by
  obtain ⟨c, hc, hb⟩ := referenceIntervalMatrix_truncated_coercivity s
  have hlow := (hb N hN K hK hKN).2.2
  have hsym := referenceIntervalMatrix_isHermitian s N hN K
  have hq := (FiniteMatrixOrder.smul_one_le_iff hsym _).mp hlow
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [IsHermitian, conjTranspose_smul, star_trivial] using
      congrArg (fun A => (2 : ℝ) • A) hsym.eq
  · intro u hu
    have hnorm : 0 < u ⬝ᵥ u := by simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hu)
    have hstrict : 0 < c * (K : ℝ) ^ (-1 - s.val) * (u ⬝ᵥ u) := by positivity
    have hpos := lt_of_lt_of_le hstrict (hq u)
    simpa only [star_trivial, smul_mulVec, dotProduct_smul, smul_eq_mul] using mul_pos two_pos hpos

/-- Every exterior principal block has positive definite inverse, also on the
zero-dimensional carrier. No inverse of a singular block is used. -/
theorem exteriorBlock_posDef (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ) / 4)
    (E : Finset (Fin (N : ℕ))) :
    (((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
      (Subtype.val : E → Fin (N : ℕ)) Subtype.val).PosDef ∧
    ((((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
      (Subtype.val : E → Fin (N : ℕ)) Subtype.val)⁻¹).PosDef := by
  have h := (referenceHessian_posDef s N hN hK hKN).submatrix
    (show Function.Injective (Subtype.val : E → Fin (N : ℕ)) from Subtype.val_injective)
  exact ⟨h, h.inv⟩

/-- The full reference matrix is bounded by `C K²` times its truncation, as used in the proof of Lemma 5.5. -/
theorem full_le_cutoff_sq_mul_truncation (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 →
      Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)) ≤
        (C * (K : ℝ) ^ 2) • referenceIntervalMatrix s N hN K := by
  obtain ⟨A, hA, hdel⟩ := deleted_intervals_bound s
  obtain ⟨c, hc, hcoer⟩ := referenceIntervalMatrix_truncated_coercivity s
  refine ⟨1 + A / c, by positivity, ?_⟩
  intro N hN K hK hKN
  let U := Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))
  let T := referenceIntervalMatrix s N hN K
  have hT := referenceIntervalMatrix_isHermitian s N hN K
  have hU := (sampledRieszKernel_posDef s N hN).isHermitian
  have hd := (FiniteMatrixOrder.le_iff_forall_dotProduct_mulVec_le (hU.sub hT)
    (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (star_trivial _)))).mp
      (hdel N hN K hK hKN)
  have hb := (FiniteMatrixOrder.smul_one_le_iff hT _).mp (hcoer N hN K hK hKN).2.2
  apply (FiniteMatrixOrder.le_iff_forall_dotProduct_mulVec_le hU
    (hT.smul (isSelfAdjoint_iff.mpr (star_trivial _)))).mpr
  intro u
  have hdp := hd u
  simp only [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul] at hdp
  have hbp := mul_le_mul_of_nonneg_left (hb u)
    (show 0 ≤ A / c * (K : ℝ) ^ 2 by positivity)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hscale : A / c * (K : ℝ) ^ 2 * (c * (K : ℝ) ^ (-1 - s.val)) =
      A * (K : ℝ) ^ (1 - s.val) := by
    have hp : (K : ℝ) ^ 2 * (K : ℝ) ^ (-1 - s.val) = (K : ℝ) ^ (1 - s.val) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hKpos]
      congr 1
      push_cast
      ring
    calc A / c * (K : ℝ) ^ 2 * (c * (K : ℝ) ^ (-1 - s.val)) =
        A * ((K : ℝ) ^ 2 * (K : ℝ) ^ (-1 - s.val)) := by field_simp
      _ = _ := by rw [hp]
  rw [← mul_assoc, hscale] at hbp
  have hnonneg : 0 ≤ u ⬝ᵥ (T *ᵥ u) := by
    have h := ((referenceIntervalMatrix_nonneg_le_full s N hN K).1)
    have hp := (Matrix.nonneg_iff_posSemidef.mp h).dotProduct_mulVec_nonneg u
    simpa only [star_trivial] using hp
  have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hrest := mul_le_mul_of_nonneg_right hK1 hnonneg
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
  dsimp [U, T] at *
  nlinarith only [hdp, hbp, hrest]

private theorem inverse_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 < t) (hBA : B ≤ t • A) (v : ι → ℝ) :
    v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ t * (v ⬝ᵥ (B⁻¹ *ᵥ v)) := by
  let u := A⁻¹ *ᵥ v
  have hq := (FiniteMatrixOrder.le_iff_forall_dotProduct_mulVec_le hB.isHermitian
    (hA.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial _)))).mp hBA u
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul] at hq
  have hau : u ⬝ᵥ (A *ᵥ u) = v ⬝ᵥ u := by
    dsimp [u]
    rw [inverse_solves hA, dotProduct_comm]
  rw [hau] at hq
  have hvar := mul_le_mul_of_nonneg_left (variational_upper hB v (t⁻¹ • u)) ht.le
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hvar
  have hidentity : t * (2 * (t⁻¹ * (v ⬝ᵥ u)) -
      t⁻¹ * (t⁻¹ * (u ⬝ᵥ (B *ᵥ u)))) =
        2 * (v ⬝ᵥ u) - t⁻¹ * (u ⬝ᵥ (B *ᵥ u)) := by
    field_simp
  rw [hidentity] at hvar
  have hq' : t⁻¹ * (u ⬝ᵥ (B *ᵥ u)) ≤ v ⬝ᵥ u := by
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hq)
  dsimp [u] at *
  linarith

/-- The full and truncated inverse covariance forms differ by at most `C K²`.
This proves the second inverse comparison used in the proof of Lemma 5.5. -/
theorem truncated_inverse_comparison (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 → ∀ v : Fin (N : ℕ) → ℝ,
      v ⬝ᵥ (((2 : ℝ) • referenceIntervalMatrix s N hN K)⁻¹ *ᵥ v) ≤
        C * (K : ℝ) ^ 2 *
          (v ⬝ᵥ (((2 : ℝ) • Matrix.of (fun a b : Fin (N : ℕ) =>
            sampledRieszKernel s N hN (b - a)))⁻¹ *ᵥ v)) := by
  obtain ⟨C, hC, hb⟩ := full_le_cutoff_sq_mul_truncation s
  refine ⟨C, hC, ?_⟩
  intro N hN K hK hKN v
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hB : ((2 : ℝ) • Matrix.of (fun a b : Fin (N : ℕ) =>
      sampledRieszKernel s N hN (b - a))).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      ((sampledRieszKernel_posDef s N hN).isHermitian.smul
        (isSelfAdjoint_iff.mpr (star_trivial _)))
    intro u hu
    simpa only [smul_mulVec, dotProduct_smul, smul_eq_mul] using
      mul_pos two_pos ((sampledRieszKernel_posDef s N hN).dotProduct_mulVec_pos hu)
  have hcomp : ((2 : ℝ) • Matrix.of (fun a b : Fin (N : ℕ) =>
      sampledRieszKernel s N hN (b - a))) ≤
        (C * (K : ℝ) ^ 2) • ((2 : ℝ) • referenceIntervalMatrix s N hN K) := by
    have h := smul_le_smul_of_nonneg_left (hb N hN K hK hKN) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [smul_smul, mul_comm (2 : ℝ)] using h
  exact inverse_comparison (referenceHessian_posDef s N hN hK hKN) hB
    (by positivity) hcomp v

/-- The exact row mass and entry bounds reduce the full inverse form of an
indicator to its crossing pairs. This is the cancellation step of the proof of Lemma 5.5, before the cyclic interval pair count and power summation.
The set is arbitrary, so this lemma also retains the full-cycle constant mode. -/
theorem full_inverse_indicator_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (J : Finset (Fin (N : ℕ))),
      (∑ i ∈ J, ∑ j ∈ J,
        (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j) ≤
        C * ((J.card : ℝ) * (N : ℝ) ^ (s.val - 1) +
          ∑ i ∈ J, ∑ j ∈ Jᶜ,
            1 / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (2 - s.val))) := by
  obtain ⟨C, hC, hb⟩ := sampledRieszMatrix_inverse_decay hz s
  refine ⟨C, hC, ?_⟩
  intro N hN J
  let A := Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))
  have hsym := (hb N hN).1.inv.isHermitian
  have hrow (i : Fin (N : ℕ)) : (∑ j, A⁻¹ i j) =
      (∑ k, sampledRieszKernel s N hN k)⁻¹ := by
    have heq (j : Fin (N : ℕ)) : A⁻¹ i j = A⁻¹ j i := by
      simpa only [star_trivial] using (hsym.apply j i)
    simp_rw [heq]
    exact sampledRieszMatrix_inverse_column_sum hz s N hN i
  have hmass : (∑ k, sampledRieszKernel s N hN k)⁻¹ ≤ C * (N : ℝ) ^ (s.val - 1) := by
    have h := (hb N hN).2.2
    rw [sampledRieszMatrix_inverse_column_sum hz s N hN 0] at h
    exact (le_abs_self _).trans h
  have hsplit (i : Fin (N : ℕ)) : (∑ j ∈ J, A⁻¹ i j) =
      (∑ k, sampledRieszKernel s N hN k)⁻¹ - ∑ j ∈ Jᶜ, A⁻¹ i j := by
    have h := Finset.sum_add_sum_compl J (fun j => A⁻¹ i j)
    rw [hrow i] at h
    linarith
  have hpoint (i : Fin (N : ℕ)) : (∑ j ∈ J, A⁻¹ i j) ≤
      C * (N : ℝ) ^ (s.val - 1) +
        C * ∑ j ∈ Jᶜ, 1 / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (2 - s.val)) := by
    rw [hsplit]
    have hcross : -(∑ j ∈ Jᶜ, A⁻¹ i j) ≤
        C * ∑ j ∈ Jᶜ, 1 / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (2 - s.val)) := by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc -A⁻¹ i j ≤ |A⁻¹ i j| := neg_le_abs _
        _ ≤ C / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (2 - s.val)) :=
          (hb N hN).2.1 i j
        _ = _ := by ring
    linarith
  have h := Finset.sum_le_sum (fun i (_ : i ∈ J) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at h
  dsimp [A] at h
  convert h using 1
  ring

private theorem sum_zero_extend {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset ι) (f : E → ℝ) :
    (∑ i : ι, if hi : i ∈ E then f ⟨i, hi⟩ else 0) = ∑ i : E, f i := by
  let g : ι → ℝ := fun i => if hi : i ∈ E then f ⟨i, hi⟩ else 0
  have hsub : (∑ i ∈ E, g i) = ∑ i : E, g i.val :=
    Finset.sum_subtype E (fun _ => Iff.rfl) g
  have hzero : (∑ i ∈ E, g i) = ∑ i : ι, g i := by
    apply Finset.sum_subset (Finset.subset_univ E)
    intro i _ hi
    exact dite_eq_right hi
  rw [← hzero, hsub]
  apply Finset.sum_congr rfl
  intro i _
  exact dite_eq_left i.property

/-- Zero extension compares the inverse of an exterior principal block with
the full truncated inverse. This is the first variational comparison in
the proof of Lemma 5.5. The exterior may be empty or disconnected. -/
theorem exterior_inverse_le_full (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ) / 4)
    (E : Finset (Fin (N : ℕ))) (v : E → ℝ) :
    let v₀ : Fin (N : ℕ) → ℝ := fun i => if hi : i ∈ E then v ⟨i, hi⟩ else 0
    v ⬝ᵥ (((((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
      (Subtype.val : E → Fin (N : ℕ)) Subtype.val))⁻¹ *ᵥ v) ≤
      v₀ ⬝ᵥ (((2 : ℝ) • referenceIntervalMatrix s N hN K)⁻¹ *ᵥ v₀) := by
  let A := (2 : ℝ) • referenceIntervalMatrix s N hN K
  let D : Matrix E E ℝ := A.submatrix Subtype.val Subtype.val
  let lift : (E → ℝ) → Fin (N : ℕ) → ℝ :=
    fun x i => if hi : i ∈ E then x ⟨i, hi⟩ else 0
  have hpair (x : E → ℝ) (y : Fin (N : ℕ) → ℝ) :
      lift x ⬝ᵥ y = ∑ i : E, x i * y i.val := by
    unfold dotProduct
    calc (∑ i, lift x i * y i) =
        ∑ i, if hi : i ∈ E then x ⟨i, hi⟩ * y i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [lift]
          split_ifs <;> simp only [zero_mul]
      _ = _ := sum_zero_extend E (fun i => x i * y i.val)
  have hpair' (x y : E → ℝ) : lift x ⬝ᵥ lift y = x ⬝ᵥ y := by
    rw [hpair]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [lift]
    simp only [i.property, ↓reduceIte]
  have hrestrict (x y : E → ℝ) :
      lift x ⬝ᵥ (A *ᵥ lift y) = x ⬝ᵥ (D *ᵥ y) := by
    rw [hpair]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    unfold mulVec dotProduct
    calc (∑ j, A i.val j * lift y j) =
        ∑ j, if hj : j ∈ E then A i.val j * y ⟨j, hj⟩ else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [lift]
          split_ifs <;> simp only [mul_zero]
      _ = _ := by
        simpa only [D, Matrix.submatrix_apply] using
          sum_zero_extend E (fun j => A i.val j.val * y j)
  have hA := referenceHessian_posDef s N hN hK hKN
  have hD := (exteriorBlock_posDef s N hN hK hKN E).1
  have h := variational_upper hA (lift v) (lift (D⁻¹ *ᵥ v))
  rw [hpair', hrestrict, variational_attained hD] at h
  exact h

/-- The exact triangular count for a circulant form on an interval of at most
half a cycle. This is the finite counting step in the proof of Lemma 5.5.
It uses the cyclic intervals throughout. -/
theorem interval_kernel_quadratic (N : ℕ+) (a : Fin (N : ℕ))
    {r : ℕ} (hr : 2 * r ≤ (N : ℕ)) (f : Fin (N : ℕ) → ℝ) :
    (∑ i ∈ cyclicIndexInterval N a r, ∑ j ∈ cyclicIndexInterval N a r, f (j - i)) =
      ∑ h : Fin (N : ℕ), ((r - Riesz1.cyclicIndexDistance N 0 h : ℕ) : ℝ) * f h := by
  let J := cyclicIndexInterval N a r
  let e : Fin (N : ℕ) → ℝ := fun i => if i ∈ J then 1 else 0
  have hrN : r ≤ (N : ℕ) := by omega
  have hcount (h : Fin (N : ℕ)) :
      (∑ i, e i * e (i + h)) = ((r - Riesz1.cyclicIndexDistance N 0 h : ℕ) : ℝ) := by
    calc
      (∑ i, e i * e (i + h)) =
        ∑ b : Fin (N : ℕ),
          (if 0 ∈ cyclicIndexInterval N b r then (1 : ℝ) else 0) *
            (if h ∈ cyclicIndexInterval N b r then (1 : ℝ) else 0) := by
        apply Fintype.sum_equiv (Equiv.subLeft a)
        intro i
        have h0 : (0 : Fin (N : ℕ)) - (a - i) = i - a := by abel
        have hh : h - (a - i) = (i + h) - a := by abel
        simp only [e, J, Equiv.subLeft_apply, mem_cyclicIndexInterval_iff N _ _ hrN, h0, hh]
      _ = _ := cyclicIndexInterval_pair_count N hr 0 h
  have hshift (i : Fin (N : ℕ)) :
      (∑ j, e j * f (j - i)) = ∑ h, e (i + h) * f h := by
    have h := Equiv.sum_comp (Equiv.addLeft i) (fun j => e j * f (j - i))
    simpa only [Equiv.coe_addLeft, add_sub_cancel_left] using h.symm
  calc (∑ i ∈ cyclicIndexInterval N a r, ∑ j ∈ cyclicIndexInterval N a r, f (j - i)) =
      ∑ i, e i * ∑ j, e j * f (j - i) := by
        simp [e, J, ite_mul, Finset.mul_sum]
    _ = ∑ i, ∑ h, (e i * e (i + h)) * f h := by
      simp_rw [hshift, Finset.mul_sum, mul_assoc]
    _ = ∑ h, (∑ i, e i * e (i + h)) * f h := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp_rw [hcount]

/-- The actual centered Gaussian of Subsection 5.1 has the exterior
inverse as covariance. Every linear form is in L², so the real variance here
is finite and cannot take its nonintegrable junk value. -/
theorem exterior_gaussian_linearForm (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ) / 4)
    (E : Finset (Fin (N : ℕ))) (v : E → ℝ) :
    let D := ((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
      (Subtype.val : E → Fin (N : ℕ)) (Subtype.val : E → Fin (N : ℕ))
    let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ E) D⁻¹
    MeasureTheory.MemLp (fun z => inner ℝ (WithLp.toLp 2 v) z) 2 μ ∧
      ProbabilityTheory.variance (fun z => inner ℝ (WithLp.toLp 2 v) z) μ =
        v ⬝ᵥ (D⁻¹ *ᵥ v) := by
  dsimp only
  refine ⟨MeasureTheory.MemLp.const_inner _ ProbabilityTheory.IsGaussian.memLp_two_id, ?_⟩
  rw [← ProbabilityTheory.covarianceBilin_self ProbabilityTheory.IsGaussian.memLp_two_id,
    ProbabilityTheory.covarianceBilin_multivariateGaussian
      (exteriorBlock_posDef s N hN hK hKN E).2.posSemidef]

/-- The head and tail power sum in the proof of Lemma 5.5, uniformly in
the outer summation limit. The positive lower endpoints avoid power junk values. -/
theorem interval_power_sum (s : Riesz1.RieszExponent) {r : ℕ} (hr : 1 ≤ r) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, (min r d : ℕ) * (d : ℝ) ^ (s.val - 2)) ≤
      (1 / s.val + 1 + 1 / (1 - s.val)) * (r : ℝ) ^ s.val := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs := s.property
  let G : ℕ → ℝ := fun k =>
    if (r : ℝ) ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (s.val - 2) else 0
  have hG0 (k : ℕ) : 0 ≤ G k := by dsimp [G]; split_ifs <;> positivity
  have hGs : Summable G := by
    apply Summable.of_nonneg_of_le hG0 _ (summable_one_add_rpow_neg (by linarith : 1 < 2 - s.val))
    intro k
    dsimp [G]
    split_ifs
    · exact (congrArg ((1 + (k : ℝ)) ^ ·) (by ring : s.val - 2 = -(2 - s.val))).le
    · positivity
  have hGt : (∑' k, G k) ≤ (1 + 1 / (1 - s.val)) * (r : ℝ) ^ (s.val - 1) := by
    have h := tsum_tail_indicator_le (t := 2 - s.val) (by linarith)
      (R := (r : ℝ)) (by exact_mod_cast hr)
    simpa only [show -(2 - s.val) = s.val - 2 by ring,
      show 2 - s.val - 1 = 1 - s.val by ring,
      show 1 - (2 - s.val) = s.val - 1 by ring, G] using h
  have hshift : (∑ d ∈ Finset.Icc 1 M, G (d - 1)) = ∑ k ∈ Finset.range M, G k := by
    rw [show Finset.Icc 1 M = Finset.Ico 1 (M + 1) by
      ext d; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    simp
  have htail : (∑ d ∈ Finset.Icc 1 M, if r < d then (d : ℝ) ^ (s.val - 2) else 0) ≤
      (1 + 1 / (1 - s.val)) * (r : ℝ) ^ (s.val - 1) := by
    apply le_trans _ hGt
    apply le_trans _ (hGs.sum_le_tsum (Finset.range M) (fun k _ => hG0 k))
    rw [← hshift]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hcast : 1 + ((d - 1 : ℕ) : ℝ) = d := by
      rw [Nat.cast_sub hd1]
      push_cast
      ring
    dsimp [G]
    rw [hcast]
    split_ifs with hrd hrd' hrd'
    · rfl
    · have : (r : ℝ) ≤ d := by exact_mod_cast (Nat.le_of_lt hrd)
      exact (hrd' this).elim
    · positivity
    · rfl
  have hhead : (∑ d ∈ Finset.Icc 1 M, if d ≤ r then (d : ℝ) ^ (s.val - 1) else 0) ≤
      (r : ℝ) ^ s.val / s.val := by
    have hbound := (subcritical_power_sum (by linarith : 0 < 1 - s.val)
      (by linarith : 1 - s.val < 1) hr).2
    simp only [show -(1 - s.val) = s.val - 1 by ring,
      show 1 - (1 - s.val) = s.val by ring] at hbound
    apply le_trans _ hbound
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd'.1).1, hd'.2⟩
    · intro d _ _
      positivity
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 M) :
      (min r d : ℕ) * (d : ℝ) ^ (s.val - 2) =
        (if d ≤ r then (d : ℝ) ^ (s.val - 1) else 0) +
          (r : ℝ) * (if r < d then (d : ℝ) ^ (s.val - 2) else 0) := by
    by_cases hdr : d ≤ r
    · rw [min_eq_right hdr, ite_eq_left hdr, ite_eq_right (by omega)]
      simp only [mul_zero, add_zero]
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      rw [mul_comm, ← Real.rpow_add_one hdpos.ne']
      congr 1
      ring
    · rw [min_eq_left (by omega), ite_eq_right hdr, ite_eq_left (by omega), zero_add]
  simp_rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h := add_le_add hhead (mul_le_mul_of_nonneg_left htail hrpos.le)
  apply h.trans_eq
  have hscale : (r : ℝ) * (r : ℝ) ^ (s.val - 1) = (r : ℝ) ^ s.val := by
    rw [mul_comm, ← Real.rpow_add_one hrpos.ne']
    congr 1
    ring
  rw [mul_left_comm, hscale]
  ring

/-- The inverse form of a short interval is of order `rˢ`. This implements
the cancellation and power-sum part of the proof of Lemma 5.5 for intervals
of at most half the cycle. The next estimate handles longer intervals by complementation. -/
theorem full_inverse_short_interval_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : Fin (N : ℕ)) (r : ℕ), 1 ≤ r → 2 * r ≤ (N : ℕ) →
      (∑ i ∈ cyclicIndexInterval N a r, ∑ j ∈ cyclicIndexInterval N a r,
        (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j) ≤
          C * (r : ℝ) ^ s.val := by
  obtain ⟨C, hC, hb⟩ := sampledRieszMatrix_inverse_decay hz s
  let L := 1 / s.val + 1 + 1 / (1 - s.val)
  have hsp := s.property.1
  have hs1 : 0 < 1 - s.val := by linarith [s.property.2]
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C * (1 + 2 * L), by positivity, ?_⟩
  intro N hN a r hr hrN
  let A := Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))
  let q := fun h : Fin (N : ℕ) => A⁻¹ 0 h
  let d := fun h : Fin (N : ℕ) => Riesz1.cyclicIndexDistance N 0 h
  let W : ℕ → ℝ := fun k => if k = 0 then 0 else (min r k : ℕ) * (k : ℝ) ^ (s.val - 2)
  have hW0 (k : ℕ) : 0 ≤ W k := by dsimp [W]; split_ifs <;> positivity
  have hWs : Summable W := by
    apply Summable.of_nonneg_of_le hW0 _
      ((Real.summable_nat_rpow.mpr (by linarith [s.property.2] : s.val - 2 < -1)).mul_left (r : ℝ))
    intro k
    dsimp [W]
    split_ifs
    · positivity
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left r k) (by positivity)
  have hWt : (∑' k, W k) ≤ L * (r : ℝ) ^ s.val := by
    apply Real.tsum_le_of_sum_range_le hW0
    intro R
    apply le_trans _ (interval_power_sum s hr R)
    calc
      (∑ k ∈ Finset.range R, W k) ≤ ∑ k ∈ insert 0 (Finset.Icc 1 R), W k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have := Finset.mem_range.mp hk
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        · intro k _ _
          exact hW0 k
      _ = ∑ k ∈ Finset.Icc 1 R, (min r k : ℕ) * (k : ℝ) ^ (s.val - 2) := by
        rw [Finset.sum_insert (by simp), show W 0 = 0 by simp [W], zero_add]
        apply Finset.sum_congr rfl
        intro k hk
        have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
        simp only [W, hk0, ↓reduceIte]
  have hentry (i j : Fin (N : ℕ)) : A⁻¹ i j = q (j - i) := by
    apply Complex.ofReal_injective
    dsimp [A, q]
    rw [sampledRieszMatrix_inverse_formula hz s N hN i j,
      sampledRieszMatrix_inverse_formula hz s N hN 0 (j - i)]
    simp only [sub_zero]
  have hmass : |∑ h, q h| ≤ C * (N : ℝ) ^ (s.val - 1) := by
    have hsym := (hb N hN).1.inv.isHermitian
    have heq (h : Fin (N : ℕ)) : q h = A⁻¹ h 0 := by
      simpa only [star_trivial, q] using hsym.apply h 0
    simp_rw [heq]
    exact (hb N hN).2.2
  have hpoint (h : Fin (N : ℕ)) : -(min r (d h) : ℕ) * q h ≤ C * W (d h) := by
    by_cases hd0 : d h = 0
    · simp only [hd0, Nat.min_zero, Nat.cast_zero, neg_zero, zero_mul, W, ↓reduceIte, mul_zero]
      exact le_rfl
    have hdpos : (0 : ℝ) < d h := by exact_mod_cast (Nat.pos_of_ne_zero hd0)
    have hpow : 1 / (1 + (d h : ℝ) ^ (2 - s.val)) ≤ (d h : ℝ) ^ (s.val - 2) := by
      calc 1 / (1 + (d h : ℝ) ^ (2 - s.val)) ≤ 1 / (d h : ℝ) ^ (2 - s.val) :=
          one_div_le_one_div_of_le (by positivity) (by linarith [Real.rpow_nonneg hdpos.le (2 - s.val)])
        _ = _ := by rw [one_div, ← Real.rpow_neg hdpos.le]; congr 1; ring
    calc -(min r (d h) : ℕ) * q h = (min r (d h) : ℕ) * (-q h) := by ring
      _ ≤ (min r (d h) : ℕ) * |q h| := mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
      _ ≤ (min r (d h) : ℕ) * (C / (1 + (d h : ℝ) ^ (2 - s.val))) :=
        mul_le_mul_of_nonneg_left ((hb N hN).2.1 0 h) (by positivity)
      _ ≤ (min r (d h) : ℕ) * (C * (d h : ℝ) ^ (s.val - 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hpow hC.le
      _ = C * W (d h) := by simp only [W, hd0, ↓reduceIte]; ring
  have hsum : (∑ h, W (d h)) ≤ 2 * L * (r : ℝ) ^ s.val := by
    apply (sum_le_two_mul_tsum_cyclicIndexDistance N 0 hW0 hWs).trans
    have h := mul_le_mul_of_nonneg_left hWt (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_assoc] using h
  have hscale : (r : ℝ) * (N : ℝ) ^ (s.val - 1) ≤ (r : ℝ) ^ s.val := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    calc
      (r : ℝ) * (N : ℝ) ^ (s.val - 1) ≤ (r : ℝ) * (r : ℝ) ^ (s.val - 1) := by
        apply mul_le_mul_of_nonneg_left _ hrpos.le
        exact Real.rpow_le_rpow_of_nonpos hrpos (by exact_mod_cast (show r ≤ (N : ℕ) by omega))
          (by linarith [s.property.2])
      _ = _ := by rw [mul_comm, ← Real.rpow_add_one hrpos.ne']; congr 1; ring
  change (∑ i ∈ cyclicIndexInterval N a r, ∑ j ∈ cyclicIndexInterval N a r, A⁻¹ i j) ≤ _
  simp_rw [hentry]
  rw [interval_kernel_quadratic N a hrN q]
  have htri (h : Fin (N : ℕ)) : ((r - d h : ℕ) : ℝ) = (r : ℝ) - (min r (d h) : ℕ) := by
    have hmin := Nat.sub_add_min_cancel r (d h)
    have h' : ((r - d h : ℕ) : ℝ) + (min r (d h) : ℕ) = (r : ℝ) := by exact_mod_cast hmin
    linarith
  change (∑ h, ((r - d h : ℕ) : ℝ) * q h) ≤ _
  simp_rw [htri, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hp := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hpoint h)
  simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum] at hp
  have hm := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hmass) (Nat.cast_nonneg r)
  have h₁ := mul_le_mul_of_nonneg_left hscale hC.le
  have h₂ := mul_le_mul_of_nonneg_left hsum hC.le
  nlinarith only [hp, hm, h₁, h₂]

private theorem interval_compl (N : ℕ+) (a : Fin (N : ℕ))
    {r : ℕ} (hr : r ≤ (N : ℕ)) :
    (cyclicIndexInterval N a r)ᶜ = cyclicIndexInterval N (a + (r : Fin (N : ℕ))) ((N : ℕ) - r) := by
  ext i
  rw [Finset.mem_compl, mem_cyclicIndexInterval_iff N _ _ hr,
    mem_cyclicIndexInterval_iff N _ _ (Nat.sub_le (N : ℕ) r)]
  by_cases heq : r = (N : ℕ)
  · subst r
    simp only [Nat.sub_self, Nat.not_lt_zero, iff_false]
    exact not_not_intro (i - a).isLt
  have hrlt : r < (N : ℕ) := by omega
  have hsub : i - (a + (r : Fin (N : ℕ))) = (i - a) - (r : Fin (N : ℕ)) := by abel
  have hval : ((i - a) - (r : Fin (N : ℕ))).val =
      ((N : ℕ) - r + (i - a).val) % (N : ℕ) := by
    rw [Fin.val_sub]
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hrlt]
  rw [hsub, hval]
  have hd := (i - a).isLt
  by_cases hdr : (i - a).val < r
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem indicator_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (J : Finset ι) :
    (fun i => if i ∈ J then (1 : ℝ) else 0) ⬝ᵥ
      (A *ᵥ (fun i => if i ∈ J then (1 : ℝ) else 0)) = ∑ i ∈ J, ∑ j ∈ J, A i j := by
  simp [dotProduct, mulVec, ite_mul, mul_ite, Finset.mul_sum]

private theorem quadratic_sub_le {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u - v) ⬝ᵥ (A *ᵥ (u - v)) ≤ 2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  have h := hA.dotProduct_mulVec_nonneg (u + v)
  simp only [star_trivial, mulVec_add, dotProduct_add, add_dotProduct] at h
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
  linarith

/-- The full inverse form of every cyclic interval, with no restriction to a
half-cycle. Long intervals are handled by their short complement and the
constant row mass, as required by the proof of Lemma 5.5. -/
theorem full_inverse_interval_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : Fin (N : ℕ)) (r : ℕ), 1 ≤ r → r ≤ (N : ℕ) →
      (∑ i ∈ cyclicIndexInterval N a r, ∑ j ∈ cyclicIndexInterval N a r,
        (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j) ≤
          C * (r : ℝ) ^ s.val := by
  obtain ⟨C, hC, hshort⟩ := full_inverse_short_interval_bound hz s
  obtain ⟨A, hA, hb⟩ := sampledRieszMatrix_inverse_decay hz s
  refine ⟨C + 2 * A * (2 : ℝ) ^ s.val + 2 * C, by positivity, ?_⟩
  intro N hN a r hr hrN
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  by_cases hhalf : 2 * r ≤ (N : ℕ)
  · apply (hshort N hN a r hr hhalf).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hpos : 0 ≤ 2 * A * (2 : ℝ) ^ s.val + 2 * C := by positivity
    linarith
  let T := Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))
  let J := cyclicIndexInterval N a r
  let v : Fin (N : ℕ) → ℝ := fun i => if i ∈ Jᶜ then 1 else 0
  have hv : (fun i => if i ∈ J then (1 : ℝ) else 0) = (fun _ => (1 : ℝ)) - v := by
    funext i
    simp only [v, Pi.sub_apply, Finset.mem_compl]
    split_ifs <;> norm_num
  have hcomp : v ⬝ᵥ (T⁻¹ *ᵥ v) ≤ C * (r : ℝ) ^ s.val := by
    rw [show v = (fun i => if i ∈ Jᶜ then (1 : ℝ) else 0) from rfl,
      indicator_quadratic, show Jᶜ = cyclicIndexInterval N (a + (r : Fin (N : ℕ))) ((N : ℕ) - r)
        from interval_compl N a hrN]
    by_cases hq : (N : ℕ) - r = 0
    · simp only [hq, cyclicIndexInterval, Finset.range_zero, Finset.image_empty,
        Finset.sum_empty]
      positivity
    · apply (hshort N hN _ ((N : ℕ) - r) (by omega) (by omega)).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show (N : ℕ) - r ≤ r by omega)) s.property.1.le
  have hmass : (fun _ : Fin (N : ℕ) => (1 : ℝ)) ⬝ᵥ
      (T⁻¹ *ᵥ (fun _ => (1 : ℝ))) ≤ A * (2 : ℝ) ^ s.val * (r : ℝ) ^ s.val := by
    have hsym := (hb N hN).1.inv.isHermitian
    have hrow (i : Fin (N : ℕ)) : (∑ j, T⁻¹ i j) =
        (∑ k, sampledRieszKernel s N hN k)⁻¹ := by
      have heq (j : Fin (N : ℕ)) : T⁻¹ i j = T⁻¹ j i := by
        simpa only [star_trivial] using hsym.apply j i
      simp_rw [heq]
      exact sampledRieszMatrix_inverse_column_sum hz s N hN i
    have hbound := (hb N hN).2.2
    rw [sampledRieszMatrix_inverse_column_sum hz s N hN 0] at hbound
    have hbound' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbound) (show (0 : ℝ) ≤ N by positivity)
    have hscale : (N : ℝ) * (N : ℝ) ^ (s.val - 1) = (N : ℝ) ^ s.val := by
      rw [mul_comm, ← Real.rpow_add_one (by positivity : (N : ℝ) ≠ 0)]
      congr 1
      ring
    have hp : (N : ℝ) ^ s.val ≤ (2 : ℝ) ^ s.val * (r : ℝ) ^ s.val := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrpos.le]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show (N : ℕ) ≤ 2 * r by omega)) s.property.1.le
    simp only [dotProduct, mulVec, one_mul, mul_one, hrow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc
      (N : ℝ) * (∑ k, sampledRieszKernel s N hN k)⁻¹ ≤ A * (N : ℝ) ^ s.val := by
        simpa only [mul_left_comm (N : ℝ) A, hscale] using hbound'
      _ ≤ _ := by have h := mul_le_mul_of_nonneg_left hp hA.le; simpa only [mul_assoc] using h
  have hquad := quadratic_sub_le (hb N hN).1.inv.posSemidef (fun _ => (1 : ℝ)) v
  rw [← hv, indicator_quadratic] at hquad
  dsimp [J, T] at *
  nlinarith only [hquad, hmass, hcomp,
    mul_nonneg hC.le (Real.rpow_nonneg hrpos.le s.val)]

/-- See the proof of Lemma 5.5 in the paper: the variance of every exterior interval sum
is bounded by `C(s) K² rˢ`. The exterior is an arbitrary principal restriction
containing the interval. This includes the paper's consecutive exterior arc.
The auxiliary Gaussian is the centered multivariate Gaussian with covariance
equal to the inverse of the actual reference Hessian block. -/
theorem exterior_partial_sums (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ),
      1 ≤ K → K ≤ (N : ℕ) / 4 → ∀ (E : Finset (Fin (N : ℕ)))
      (a : Fin (N : ℕ)) (r : ℕ), 1 ≤ r → r ≤ (N : ℕ) →
      cyclicIndexInterval N a r ⊆ E →
      let D := ((2 : ℝ) • referenceIntervalMatrix s N hN K).submatrix
        (Subtype.val : E → Fin (N : ℕ)) (Subtype.val : E → Fin (N : ℕ))
      let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ E) D⁻¹
      let S := fun z : EuclideanSpace ℝ E =>
        ∑ i : E, if i.val ∈ cyclicIndexInterval N a r then z i else 0
      MeasureTheory.MemLp S 2 μ ∧
        ProbabilityTheory.variance S μ ≤ C * (K : ℝ) ^ 2 * (r : ℝ) ^ s.val := by
  obtain ⟨C₀, hC₀, htrunc⟩ := truncated_inverse_comparison s
  obtain ⟨C₁, hC₁, hinterval⟩ := full_inverse_interval_bound hz s
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro N hN K hK hKN E a r hr hrN hJE
  let J := cyclicIndexInterval N a r
  let v : E → ℝ := fun i => if i.val ∈ J then 1 else 0
  let v₀ : Fin (N : ℕ) → ℝ := fun i => if i ∈ J then 1 else 0
  let U := Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))
  have hobs : (fun z : EuclideanSpace ℝ E => ∑ i : E, if i.val ∈ J then z i else 0) =
      (fun z => inner ℝ (WithLp.toLp 2 v) z) := by
    funext z
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    split_ifs <;> simp
  have hg := exterior_gaussian_linearForm s N hN hK hKN E v
  dsimp only at hg ⊢
  rw [show (fun z : EuclideanSpace ℝ E =>
    ∑ i : E, if i.val ∈ cyclicIndexInterval N a r then z i else 0) =
      (fun z => inner ℝ (WithLp.toLp 2 v) z) from hobs]
  refine ⟨hg.1, ?_⟩
  rw [hg.2]
  have hzero : (fun i : Fin (N : ℕ) => if hi : i ∈ E then v ⟨i, hi⟩ else 0) = v₀ := by
    funext i
    by_cases hi : i ∈ J
    · have hiE := hJE hi
      simp only [hiE, ↓reduceDIte, v, v₀, hi, ↓reduceIte]
    · simp only [v, v₀, hi, ↓reduceIte, dite_eq_ite]
      split_ifs <;> rfl
  have hext := exterior_inverse_le_full s N hN hK hKN E v
  dsimp only at hext
  rw [hzero] at hext
  apply hext.trans
  apply (htrunc N hN K hK hKN v₀).trans
  have hU := sampledRieszKernel_posDef s N hN
  have hform : v₀ ⬝ᵥ (((2 : ℝ) • U)⁻¹ *ᵥ v₀) ≤ C₁ * (r : ℝ) ^ s.val := by
    let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
    rw [Matrix.inv_smul U (2 : ℝ) ((Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit)]
    simp only [invOf_eq_inv, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hn : 0 ≤ v₀ ⬝ᵥ (U⁻¹ *ᵥ v₀) := by
      simpa only [star_trivial] using hU.inv.posSemidef.dotProduct_mulVec_nonneg v₀
    have hq : v₀ ⬝ᵥ (U⁻¹ *ᵥ v₀) ≤ C₁ * (r : ℝ) ^ s.val := by
      rw [show v₀ = (fun i => if i ∈ J then (1 : ℝ) else 0) from rfl, indicator_quadratic]
      exact hinterval N hN a r hr hrN
    norm_num
    linarith
  have h := mul_le_mul_of_nonneg_left hform (show 0 ≤ C₀ * (K : ℝ) ^ 2 by positivity)
  convert h using 1
  ring

/-- The exact truncated reference kernel is a triangular sum, retaining the
half weight at an even antipode. This is the starting identity for the forward
difference estimates in the proof of Lemma 5.5, for every cutoff. -/
theorem reference_entry_triangular (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (a b : Fin (N : ℕ)) :
    referenceIntervalMatrix s N hN K a b =
      ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (r : Fin (N : ℕ)) *
            ((r - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) := by
  unfold referenceIntervalMatrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hrhalf : 2 * r ≤ (N : ℕ) := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    omega
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, cyclicIndexInterval_pair_count N hrhalf a b]
  have hcast : (⟨r % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)) =
      (r : Fin (N : ℕ)) := by
    apply Fin.ext
    simp only [Fin.val_natCast]
  rw [hcast]

end Riesz2.ExteriorForces
