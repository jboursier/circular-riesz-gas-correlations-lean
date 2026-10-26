/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicIntervalBoundary
public import Riesz2.ToMathlib.FiniteMatrixOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Order bounds for interval matrices

Nonnegative interval weights give nonnegative entries and quadratic forms.
The internal and crossing matrices retain exactly the coefficient family of
the full interval matrix.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Riesz2.IntervalBoundary

attribute [local instance] Classical.propDecidable

/-- Interval rank-one matrices are symmetric. -/
theorem rankOne_symm {n : ℕ} (K : Finset (Fin n)) (i j : Fin n) :
    (rankOne K i j : ℝ) = rankOne K j i := by
  simp only [rankOne, and_comm]

/-- Every entry of an interval rank-one matrix is nonnegative. -/
theorem rankOne_nonneg {n : ℕ} (K : Finset (Fin n)) (i j : Fin n) :
    0 ≤ (rankOne K i j : ℝ) := by
  unfold rankOne
  split_ifs <;> norm_num

/-- The interval rank-one matrix is the outer product of its indicator. -/
theorem rankOne_eq_vecMulVec {n : ℕ} (K : Finset (Fin n)) :
    (rankOne K : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.vecMulVec (fun i => if i ∈ K then 1 else 0)
        (fun i => if i ∈ K then 1 else 0) := by
  ext i j
  simp only [rankOne, Matrix.vecMulVec, Matrix.of_apply]
  split_ifs <;> simp_all

/-- Every interval rank-one matrix is positive semidefinite. -/
theorem rankOne_posSemidef {n : ℕ} (K : Finset (Fin n)) :
    Matrix.PosSemidef (rankOne K : Matrix (Fin n) (Fin n) ℝ) := by
  rw [rankOne_eq_vecMulVec]
  exact FiniteMatrixOrder.posSemidef_vecMulVec_self _

variable (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → ℝ)

/-- Symmetry of the complete interval matrix. -/
theorem intervalMatrix_symm (i j : Fin n) :
    intervalMatrix N n hn A i j = intervalMatrix N n hn A j i := by
  simp only [intervalMatrix, rankOne_symm (i := i) (j := j)]

/-- Symmetry of the internal interval matrix. -/
theorem internalMatrix_symm (i j : Fin n) :
    internalMatrix N n hn A i j = internalMatrix N n hn A j i := by
  classical
  simp only [internalMatrix, rankOne_symm (i := i) (j := j)]

/-- Symmetry of the crossing interval matrix. -/
theorem boundaryMatrix_symm (i j : Fin n) :
    boundaryMatrix N n hn A i j = boundaryMatrix N n hn A j i := by
  classical
  simp only [boundaryMatrix, rankOne_symm (i := i) (j := j)]

variable (hA : ∀ t, 0 ≤ A t)
include hA

/-- Nonnegative coefficients give nonnegative complete entries. -/
theorem intervalMatrix_nonneg (i j : Fin n) :
    0 ≤ intervalMatrix N n hn A i j :=
  Finset.sum_nonneg fun t _ => mul_nonneg (hA t) (rankOne_nonneg _ _ _)

/-- Nonnegative coefficients give nonnegative internal entries. -/
theorem internalMatrix_nonneg (i j : Fin n) :
    0 ≤ internalMatrix N n hn A i j := by
  classical
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact mul_nonneg (hA t) (rankOne_nonneg _ _ _)
  · exact le_rfl

/-- Nonnegative coefficients give nonnegative crossing entries. -/
theorem boundaryMatrix_nonneg (i j : Fin n) :
    0 ≤ boundaryMatrix N n hn A i j := by
  classical
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hA t) (rankOne_nonneg _ _ _)

/-- Removing the crossing intervals decreases every entry. -/
theorem internalMatrix_le_intervalMatrix (i j : Fin n) :
    internalMatrix N n hn A i j ≤ intervalMatrix N n hn A i j := by
  have he := congrFun (congrFun (internal_add_boundary N n hn A) i) j
  change internalMatrix N n hn A i j + boundaryMatrix N n hn A i j = _ at he
  linarith [boundaryMatrix_nonneg N n hn A hA i j]

/-- Removing the internal intervals decreases every entry. -/
theorem boundaryMatrix_le_intervalMatrix (i j : Fin n) :
    boundaryMatrix N n hn A i j ≤ intervalMatrix N n hn A i j := by
  have he := congrFun (congrFun (internal_add_boundary N n hn A) i) j
  change internalMatrix N n hn A i j + boundaryMatrix N n hn A i j = _ at he
  linarith [internalMatrix_nonneg N n hn A hA i j]

/-- The internal matrix is positive semidefinite without a lower-bound
assumption on its weights. -/
theorem internalMatrix_posSemidef : (internalMatrix N n hn A).PosSemidef := by
  classical
  have he : internalMatrix N n hn A = ∑ t, (if IsInternal N n t then A t else 0) •
      (rankOne (trace N n hn t.1 (t.2.val + 1)) : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [internalMatrix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  rw [he]
  apply Matrix.posSemidef_sum
  intro t _
  apply (rankOne_posSemidef _).smul
  split_ifs
  · exact hA t
  · exact le_rfl

/-- The crossing matrix is positive semidefinite. -/
theorem boundaryMatrix_posSemidef : (boundaryMatrix N n hn A).PosSemidef := by
  classical
  have he : boundaryMatrix N n hn A = ∑ t, (if IsInternal N n t then 0 else A t) •
      (rankOne (trace N n hn t.1 (t.2.val + 1)) : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [boundaryMatrix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  rw [he]
  apply Matrix.posSemidef_sum
  intro t _
  apply (rankOne_posSemidef _).smul
  split_ifs
  · exact le_rfl
  · exact hA t

omit hA in
/-- The quadratic form of the internal matrix is its literal sum of
squares of interval sums. -/
theorem internalMatrix_quadratic (z : Fin n → ℝ) :
    (∑ i, ∑ j, z i * internalMatrix N n hn A i j * z j) =
      ∑ t, if IsInternal N n t then A t *
        (∑ i ∈ trace N n hn t.1 (t.2.val + 1), z i) ^ 2 else 0 := by
  classical
  have he : internalMatrix N n hn A = ∑ t, (if IsInternal N n t then A t else 0) •
      Matrix.vecMulVec (fun i => if i ∈ trace N n hn t.1 (t.2.val + 1) then 1 else 0)
        (fun i => if i ∈ trace N n hn t.1 (t.2.val + 1) then 1 else 0) := by
    ext i j
    simp only [internalMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec, Matrix.of_apply, rankOne]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp_all
  have hquad := FiniteMatrixOrder.dotProduct_mulVec_rankOneSum Finset.univ
    (fun t => if IsInternal N n t then A t else 0)
    (fun t i => if i ∈ trace N n hn t.1 (t.2.val + 1) then (1 : ℝ) else 0) z
  rw [← he] at hquad
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] using hquad

omit hA in
/-- Length-one cyclic intervals have the expected singleton trace. -/
theorem trace_one (i : Fin n) : trace N n hn (Fin.castLE hn i) 1 = {i} := by
  classical
  ext j
  simp only [trace, Finset.mem_filter, Finset.mem_univ, true_and,
    cyclicIndexInterval, Finset.range_one, Finset.image_singleton,
    Finset.mem_singleton]
  have he : (⟨((Fin.castLE hn i).val + 0) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)) =
      Fin.castLE hn i := by
    apply Fin.ext
    simp only [add_zero, Nat.mod_eq_of_lt (Fin.castLE hn i).isLt]
  rw [he]
  exact ⟨fun h => (Fin.castLE_injective hn) h, fun h => congrArg (Fin.castLE hn) h⟩

/-- Singleton interval coefficients alone supply a coercive lower bound
for the complete internal quadratic form. -/
theorem internalMatrix_singleton_lower (hN : 2 ≤ (N : ℕ)) (c : ℝ)
    (hcoeff : ∀ i : Fin n, c ≤ A (Fin.castLE hn i, ⟨0, by omega⟩))
    (z : Fin n → ℝ) :
    c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * internalMatrix N n hn A i j * z j := by
  classical
  let r₀ : Fin ((N : ℕ) / 2) := ⟨0, by omega⟩
  let f := fun a : Fin (N : ℕ) => ∑ r : Fin ((N : ℕ) / 2),
    if IsInternal N n (a,r) then A (a,r) *
      (∑ i ∈ trace N n hn a (r.val + 1), z i) ^ 2 else 0
  have hf (a : Fin (N : ℕ)) : 0 ≤ f a := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact mul_nonneg (hA _) (sq_nonneg _)
    · exact le_rfl
  have hi (i : Fin n) : c * z i ^ 2 ≤ f (Fin.castLE hn i) := by
    have hint : IsInternal N n (Fin.castLE hn i, r₀) := by
      intro j hj
      have he : cyclicIndexInterval N (Fin.castLE hn i) 1 = {Fin.castLE hn i} := by
        simp only [cyclicIndexInterval, Finset.range_one, Finset.image_singleton]
        congr 1
        apply Fin.ext
        simp only [Fin.val_castLE, add_zero]
        exact Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hn)
      change j ∈ cyclicIndexInterval N (Fin.castLE hn i) 1 at hj
      rw [he, Finset.mem_singleton] at hj
      rw [hj]
      exact i.isLt
    have htrace := trace_one N n hn i
    have hterm := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun r : Fin ((N : ℕ) / 2) => if IsInternal N n (Fin.castLE hn i,r) then
        A (Fin.castLE hn i,r) * (∑ j ∈ trace N n hn (Fin.castLE hn i) (r.val + 1), z j) ^ 2 else 0)
      (fun r _ => by split_ifs; exact mul_nonneg (hA _) (sq_nonneg _); exact le_rfl)
      (Finset.mem_univ r₀)
    change (if IsInternal N n (Fin.castLE hn i,r₀) then
      A (Fin.castLE hn i,r₀) * (∑ j ∈ trace N n hn (Fin.castLE hn i) 1, z j) ^ 2 else 0) ≤ _ at hterm
    rw [ite_eq_left hint, htrace, Finset.sum_singleton] at hterm
    exact (mul_le_mul_of_nonneg_right (hcoeff i) (sq_nonneg _)).trans hterm
  calc
    _ = ∑ i, c * z i ^ 2 := Finset.mul_sum ..
    _ ≤ ∑ i, f (Fin.castLE hn i) := Finset.sum_le_sum fun i _ => hi i
    _ = ∑ a ∈ Finset.univ.image (Fin.castLE hn), f a :=
      (Finset.sum_image (fun _ _ _ _ h => Fin.castLE_injective hn h)).symm
    _ ≤ ∑ a, f a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => hf a)
    _ = _ := by
      rw [internalMatrix_quadratic, Fintype.sum_prod_type]

omit hA in
/-- An interior column of a boundary interval matrix has an explicit
inverse-power bound. The argument counts prefixes and suffixes, including
the empty sums for a singleton block. -/
theorem boundaryMatrix_bulk_entry_le (hnpos : 1 ≤ n) (hhalf : 2 * n ≤ (N : ℕ))
    {s D : ℝ} (hs : -1 ≤ s) (hD : 0 ≤ D)
    (hp : ∀ k ∈ Finset.Ico 1 n, prefixCoefficient N n hn A k ≤ D * (k : ℝ) ^ (-s - 1))
    (hq : ∀ k ∈ Finset.Ico 1 n, suffixCoefficient N n hn A k ≤
      D * (n - k : ℕ) ^ (-s - 1))
    (hd : fullCoefficient N n hn A ≤ D * (n : ℝ) ^ (-s))
    (i j : Fin n) (hj : (n : ℝ) / 8 ≤ (min (j.val + 1) (n - j.val) : ℕ)) :
    boundaryMatrix N n hn A i j ≤
      (2 * (8 : ℝ) ^ (s + 1) + 1) * D * (n : ℝ) ^ (-s) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ₁ : (min (j.val + 1) (n - j.val) : ℕ) ≤ j.val + 1 := min_le_left _ _
  have hδ₂ : (min (j.val + 1) (n - j.val) : ℕ) ≤ n - j.val := min_le_right _ _
  let T := D * ((n : ℝ) / 8) ^ (-s - 1)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hp' (k : ℕ) (hk : k ∈ Finset.Ico 1 n) :
      prefixCoefficient N n hn A k * rankOne (initialSegment n k) i j ≤ T := by
    by_cases hmem : i ∈ initialSegment n k ∧ j ∈ initialSegment n k
    · have hjk : j.val < k := (Finset.mem_filter.mp hmem.2).2
      have hδk : (min (j.val + 1) (n - j.val) : ℕ) ≤ k := by omega
      have hnk : (n : ℝ) / 8 ≤ (k : ℝ) := hj.trans (by exact_mod_cast hδk)
      simp only [rankOne, ite_eq_left hmem, mul_one]
      exact (hp k hk).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hnk (by linarith)) hD)
    · simpa only [rankOne, ite_eq_right hmem, mul_zero] using hT
  have hq' (k : ℕ) (hk : k ∈ Finset.Ico 1 n) :
      suffixCoefficient N n hn A k * rankOne (terminalSegment n k) i j ≤ T := by
    by_cases hmem : i ∈ terminalSegment n k ∧ j ∈ terminalSegment n k
    · have hkj : k ≤ j.val := (Finset.mem_filter.mp hmem.2).2
      have hδk : (min (j.val + 1) (n - j.val) : ℕ) ≤ n - k := by omega
      have hnk : (n : ℝ) / 8 ≤ (n - k : ℕ) := hj.trans (by exact_mod_cast hδk)
      simp only [rankOne, ite_eq_left hmem, mul_one]
      exact (hq k hk).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hnk (by linarith)) hD)
    · simpa only [rankOne, ite_eq_right hmem, mul_zero] using hT
  have hcount : ((Finset.Ico 1 n).card : ℝ) ≤ n := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le n 1
  have hpSum : (∑ k ∈ Finset.Ico 1 n,
      prefixCoefficient N n hn A k * rankOne (initialSegment n k) i j) ≤ (n : ℝ) * T := by
    exact (Finset.sum_le_sum hp').trans (by
      simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hcount hT)
  have hqSum : (∑ k ∈ Finset.Ico 1 n,
      suffixCoefficient N n hn A k * rankOne (terminalSegment n k) i j) ≤ (n : ℝ) * T := by
    exact (Finset.sum_le_sum hq').trans (by
      simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hcount hT)
  have he : (n : ℝ) * T = (8 : ℝ) ^ (s + 1) * D * (n : ℝ) ^ (-s) := by
    dsimp only [T]
    rw [Real.div_rpow hn0.le (by norm_num),
      show -s - 1 = -(s + 1) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_inv_eq_mul]
    have hnexp : (n : ℝ) * (n : ℝ) ^ (-(s + 1)) = (n : ℝ) ^ (-s) := by
      calc
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(s + 1)) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ (1 + -(s + 1)) := (Real.rpow_add hn0 _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = ((n : ℝ) * (n : ℝ) ^ (-(s + 1))) * (8 : ℝ) ^ (s + 1) * D := by ring
      _ = _ := by rw [hnexp]; ring
  rw [boundary_representation N hnpos hhalf A i j]
  calc
    _ ≤ (n : ℝ) * T + (n : ℝ) * T + D * (n : ℝ) ^ (-s) :=
      add_le_add (add_le_add hpSum hqSum) hd
    _ = _ := by rw [he]; ring

end Riesz2.IntervalBoundary
