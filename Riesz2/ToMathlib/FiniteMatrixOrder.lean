/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

/-!
# Finite matrix order: Loewner, rank-one, compression and Schur bridges

All matrices here are real and indexed by finite types. The order `A ≤ B` is the Loewner order
of Mathlib, that is `(B - A).PosSemidef`. It is scoped to `MatrixOrder`.

* Loewner order. Congruence `A ↦ Pᵀ * A * P` preserves `≤` (`loewner_compression`). For real
  symmetric matrices, `A ≤ B` is the inequality of quadratic forms
  (`le_iff_forall_dotProduct_mulVec_le`), and `c • 1 ≤ A` is the lower bound
  `c (u ⬝ᵥ u) ≤ u ⬝ᵥ (A *ᵥ u)` (`smul_one_le_iff`).
* Rank-one sums. A nonnegative combination `∑ c_r x_r x_rᵀ` is positive semidefinite, and the
  empty combination is zero (`posSemidef_rankOneSum`, `zero_le_rankOneSum`). Removing terms with
  nonnegative coefficients lowers the sum in the Loewner order (`rankOneSum_le_of_subset`). Its
  quadratic form is `∑ c_r (x_r ⬝ᵥ u) ^ 2` (`dotProduct_mulVec_rankOneSum`).
* Principal compression. Principal submatrices on a finite set preserve positive semidefiniteness
  and the Loewner order (`posSemidef_principal`, `loewner_principal`).
* Finite Schur complements. For a positive definite block `A`, the block matrix `[[A, B], [Bᵀ, D]]`
  is nonnegative iff `Bᵀ A⁻¹ B ≤ D` (`nonneg_fromBlocks_iff_schur_left`). For a positive definite
  block `D`, it is nonnegative iff `B D⁻¹ Bᵀ ≤ A` (`nonneg_fromBlocks_iff_schur_right`).

These statements concern finite matrices only. The operator Schur complement acts on
unbounded generator domains and needs separate arguments.
-/

@[expose] public section

open Finset Matrix
open scoped MatrixOrder

namespace Riesz2.FiniteMatrixOrder

variable {ι κ τ : Type*}

/-! ### Loewner order -/

/-- Congruence by a rectangular real matrix `P` preserves the Loewner order: if `A ≤ B`, then
`Pᵀ * A * P ≤ Pᵀ * B * P`. -/
theorem loewner_compression [Fintype ι] [Fintype κ] {A B : Matrix ι ι ℝ} (h : A ≤ B)
    (P : Matrix ι κ ℝ) :
    Pᵀ * A * P ≤ Pᵀ * B * P := by
  rw [Matrix.le_iff] at h ⊢
  have hdiff : Pᵀ * B * P - Pᵀ * A * P = Pᵀ * (B - A) * P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff]
  have := h.conjTranspose_mul_mul_same P
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- Congruence by a rectangular real matrix `P` maps positive semidefinite matrices to positive
semidefinite matrices. -/
theorem posSemidef_compression [Fintype ι] [Fintype κ] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (P : Matrix ι κ ℝ) : (Pᵀ * A * P).PosSemidef := by
  have := hA.conjTranspose_mul_mul_same P
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- A real symmetric matrix `A` lies below a real symmetric matrix `B` in the Loewner order iff
`uᵀ A u ≤ uᵀ B u` for every real vector `u`. -/
theorem le_iff_forall_dotProduct_mulVec_le [Fintype ι] {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ u : ι → ℝ, u ⬝ᵥ (A *ᵥ u) ≤ u ⬝ᵥ (B *ᵥ u) := by
  rw [Matrix.le_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  have hstar : ∀ u : ι → ℝ, star u = u := fun u => funext fun j => star_trivial (u j)
  constructor
  · rintro ⟨-, h⟩ u
    have := h u
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub] at this
    linarith
  · intro h
    refine ⟨hB.sub hA, fun u => ?_⟩
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub]
    linarith [h u]

/-- For a real symmetric matrix `A` and a real number `c`, the scalar matrix `c • 1` lies below `A`
iff `c (u ⬝ᵥ u) ≤ uᵀ A u` for every real vector `u`. -/
theorem smul_one_le_iff [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (c : ℝ) : c • (1 : Matrix ι ι ℝ) ≤ A ↔ ∀ u : ι → ℝ, c * (u ⬝ᵥ u) ≤ u ⬝ᵥ (A *ᵥ u) := by
  have hone : (c • (1 : Matrix ι ι ℝ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  rw [le_iff_forall_dotProduct_mulVec_le hone hA]
  refine forall_congr' fun u => ?_
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-! ### Rank-one sums -/

/-- The matrix `x xᵀ` of a real vector `x` acts by `u ↦ (x ⬝ᵥ u) • x`. -/
theorem vecMulVec_self_mulVec [Fintype ι] (x u : ι → ℝ) :
    Matrix.vecMulVec x x *ᵥ u = (x ⬝ᵥ u) • x := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The matrix `x xᵀ` of a real vector `x` is positive semidefinite. -/
theorem posSemidef_vecMulVec_self [Fintype ι] (x : ι → ℝ) :
    (Matrix.vecMulVec x x).PosSemidef := by
  have hx : star x = x := funext fun j => star_trivial (x j)
  have h := Matrix.posSemidef_vecMulVec_self_star x
  rwa [hx] at h

/-- A nonnegative combination `∑ c_r x_r x_rᵀ` over a finite set of indices is positive
semidefinite. The empty combination is zero, which is positive semidefinite. -/
theorem posSemidef_rankOneSum [Fintype ι] (s : Finset τ) (c : τ → ℝ) (x : τ → ι → ℝ)
    (hc : ∀ r ∈ s, 0 ≤ c r) :
    (∑ r ∈ s, c r • Matrix.vecMulVec (x r) (x r)).PosSemidef :=
  Matrix.posSemidef_sum s fun r hr => (posSemidef_vecMulVec_self (x r)).smul (hc r hr)

/-- A nonnegative combination `∑ c_r x_r x_rᵀ` over a finite set of indices is nonnegative in the
Loewner order, including the empty combination. -/
theorem zero_le_rankOneSum [Fintype ι] (s : Finset τ) (c : τ → ℝ) (x : τ → ι → ℝ)
    (hc : ∀ r ∈ s, 0 ≤ c r) :
    0 ≤ ∑ r ∈ s, c r • Matrix.vecMulVec (x r) (x r) :=
  Matrix.nonneg_iff_posSemidef.mpr (posSemidef_rankOneSum s c x hc)

/-- For `t ⊆ s` and nonnegative coefficients on `s`, the rank-one sum over `t` is at most the sum
over `s` in the Loewner order. In particular, removing terms with nonnegative coefficients lowers
the sum. -/
theorem rankOneSum_le_of_subset [Fintype ι] [DecidableEq τ] {s t : Finset τ} (hts : t ⊆ s)
    (c : τ → ℝ) (x : τ → ι → ℝ) (hc : ∀ r ∈ s, 0 ≤ c r) :
    ∑ r ∈ t, c r • Matrix.vecMulVec (x r) (x r) ≤
      ∑ r ∈ s, c r • Matrix.vecMulVec (x r) (x r) := by
  rw [Matrix.le_iff, ← Finset.sum_sdiff hts, add_sub_cancel_right]
  exact posSemidef_rankOneSum (s \ t) c x fun r hr => hc r (Finset.mem_sdiff.mp hr).1

/-- The quadratic form of a rank-one sum is the weighted sum of squared pairings:
`uᵀ (∑ c_r x_r x_rᵀ) u = ∑ c_r (x_r ⬝ᵥ u) ^ 2`. -/
theorem dotProduct_mulVec_rankOneSum [Fintype ι] (s : Finset τ) (c : τ → ℝ) (x : τ → ι → ℝ)
    (u : ι → ℝ) :
    u ⬝ᵥ ((∑ r ∈ s, c r • Matrix.vecMulVec (x r) (x r)) *ᵥ u) =
      ∑ r ∈ s, c r * (x r ⬝ᵥ u) ^ 2 := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, vecMulVec_self_mulVec,
    dotProduct_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dotProduct_comm u (x r), sq]

/-! ### Principal compression -/

/-- The principal submatrix of a positive semidefinite matrix on a finite set `S` is positive
semidefinite. -/
theorem posSemidef_principal {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (S : Finset ι) :
    (A.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).PosSemidef :=
  hA.submatrix _

/-- Principal submatrices on a finite set `S` preserve the Loewner order. -/
theorem loewner_principal {A B : Matrix ι ι ℝ} (h : A ≤ B) (S : Finset ι) :
    A.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) ≤
      B.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) := by
  rw [Matrix.le_iff]
  have hsub : B.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) -
      A.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) =
        (B - A).submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) := rfl
  rw [hsub]
  exact (Matrix.le_iff.mp h).submatrix _

/-! ### Finite Schur complements -/

section Schur

variable {m n : Type*}

/-- Let `A` be a positive definite real matrix and let `B` and `D` be real. The block matrix
`[[A, B], [Bᵀ, D]]` is nonnegative in the Loewner order iff `Bᵀ A⁻¹ B ≤ D`. -/
theorem nonneg_fromBlocks_iff_schur_left [Fintype m] [DecidableEq m] [Fintype n]
    {A : Matrix m m ℝ} (hA : A.PosDef) (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    0 ≤ Matrix.fromBlocks A B Bᵀ D ↔ Bᵀ * A⁻¹ * B ≤ D := by
  have : Invertible A := hA.isUnit.invertible
  simp only [← Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.nonneg_iff_posSemidef, Matrix.le_iff]
  exact Matrix.PosDef.fromBlocks₁₁ B D hA

/-- Let `D` be a positive definite real matrix and let `A` and `B` be real. The block matrix
`[[A, B], [Bᵀ, D]]` is nonnegative in the Loewner order iff `B D⁻¹ Bᵀ ≤ A`. -/
theorem nonneg_fromBlocks_iff_schur_right [Fintype m] [Fintype n] [DecidableEq n]
    {D : Matrix n n ℝ} (hD : D.PosDef) (A : Matrix m m ℝ) (B : Matrix m n ℝ) :
    0 ≤ Matrix.fromBlocks A B Bᵀ D ↔ B * D⁻¹ * Bᵀ ≤ A := by
  have : Invertible D := hD.isUnit.invertible
  simp only [← Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.nonneg_iff_posSemidef, Matrix.le_iff]
  exact Matrix.PosDef.fromBlocks₂₂ A B hD

end Schur

end Riesz2.FiniteMatrixOrder

end
