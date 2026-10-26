/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.InverseIntervalKernelPart2
public import Riesz2.ToMathlib.FiniteMatrixOrder
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# The uniformly coercive factorization

See the proof of Lemma 5.13 in the paper, with
the factorization matrix `𝔸 = μ (H + μ I)⁻¹` of Subsection 5.4, where `H = 2 ℍ_{m,s}`,
`μ = a + B²/a`, and `ℍ_{m,s}` is the sampled Riesz matrix of Subsection 2.4.

The proof writes each vector as `u = (H + μ I) v`. In that variable the quadratic form of
`(1/2)(𝔸 M + M 𝔸)` is `μ (Mv · (H + μ) v)`, which is bounded below by the operator-norm bound
`‖M - H‖ ≤ B` and the lower bound `M ≥ a I`.
-/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Riesz2

/-- The sampled Riesz matrix `ℍ_{m,s}` of Subsection 2.4, the circulant matrix
`(g_{m,s}(j - i))_{i,j}` of the sampled kernel `Riesz2.sampledRieszKernel`, on the cycle of
length `m = N`. -/
def rieszMatrix (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  Matrix.of fun a b => sampledRieszKernel s N hN (b - a)

/-- The factorization matrix `𝔸 = μ (H + μ I)⁻¹` of Subsection 5.4, with `H = 2 ℍ_{m,s}`
and `μ = a + B²/a`. Its argument `a` is positive, so that `μ > 0`, and `H + μ I` is invertible
(Lemma `rieszMatrix_posDef` below). -/
def factorizationMatrix (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : ℝ) (_ha : 0 < a) (B : ℝ) : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  (a + B ^ 2 / a) •
    ((2 : ℝ) • rieszMatrix s N hN + (a + B ^ 2 / a) • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ))⁻¹

/-- The sampled Riesz matrix is positive definite (the positivity part of Lemma 2.5, through `sampledRieszKernel_posDef`). -/
theorem rieszMatrix_posDef (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (rieszMatrix s N hN).PosDef :=
  sampledRieszKernel_posDef s N hN

/-- For a real symmetric matrix `A`, the form `x ⬝ᵥ (A *ᵥ y)` is symmetric in the moved
vector: `x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y`. -/
theorem dotProduct_mulVec_eq_of_transpose_eq {n : Type*} [Fintype n] {A : Matrix n n ℝ}
    (hA : Aᵀ = A) (x y : n → ℝ) : x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  have h : x ᵥ* A = A *ᵥ x := by
    rw [← vecMul_transpose, hA]
  rw [dotProduct_mulVec, h]

/-- The dot product of a real vector with itself is nonnegative. -/
theorem dotProduct_self_nonneg' {n : Type*} [Fintype n] (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The L² operator norm bound `‖E‖ ≤ B` gives the quadratic bound `|E v|² ≤ B² |v|²`. -/
theorem dotProduct_mulVec_self_le_of_norm_le {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) {B : ℝ}
    (hE : ‖E‖ ≤ B) (v : Fin n → ℝ) :
    (E *ᵥ v) ⬝ᵥ (E *ᵥ v) ≤ B ^ 2 * (v ⬝ᵥ v) := by
  let x : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm v
  have hxv : x.ofLp = v := rfl
  have h := Matrix.l2_opNorm_mulVec E x
  have hy : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (E *ᵥ x)‖ ^ 2 = (E *ᵥ v) ⬝ᵥ (E *ᵥ v) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq, Real.norm_eq_abs, hxv]
  have hx : ‖x‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq, Real.norm_eq_abs, hxv]
  have hsq : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (E *ᵥ x)‖ ^ 2 ≤ (‖E‖ * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have hEB : ‖E‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE 2
  calc (E *ᵥ v) ⬝ᵥ (E *ᵥ v) = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (E *ᵥ x)‖ ^ 2 := hy.symm
    _ ≤ (‖E‖ * ‖x‖) ^ 2 := hsq
    _ = ‖E‖ ^ 2 * ‖x‖ ^ 2 := by ring
    _ ≤ B ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hEB (sq_nonneg _)
    _ = B ^ 2 * (v ⬝ᵥ v) := by rw [hx]

/-- See the proof of Lemma 5.13 in the paper: for a real symmetric matrix `M` with `M ≥ a I` and
`‖M - 2 ℍ_{m,s}‖ ≤ B`, the matrix `(1/2)(𝔸 M + M 𝔸)` is at least `(a/4) I`, where `𝔸` is the
factorization matrix of Subsection 5.4. -/
theorem global_factorization (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : ℝ) (ha : 0 < a) (_ha1 : a ≤ 1) (B : ℝ) (hB : 1 ≤ B)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) (hMsymm : M.IsSymm)
    (hMa : a • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤ M)
    (hMB : ‖M - (2 : ℝ) • rieszMatrix s N hN‖ ≤ B) :
    (a / 4) • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤
      (1 / 2 : ℝ) • (factorizationMatrix s N hN a ha B * M +
        M * factorizationMatrix s N hN a ha B) := by
  have hMsym : Mᵀ = M := hMsymm
  set H : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := (2 : ℝ) • rieszMatrix s N hN with hH
  set μ : ℝ := a + B ^ 2 / a with hμ
  set E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := M - H with hE
  set K : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
    H + μ • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) with hK
  set A : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := factorizationMatrix s N hN a ha B with hA
  have hAdef : A = μ • K⁻¹ := rfl
  have hμpos : 0 < μ := by positivity
  have hμa : a ≤ μ := by
    have : 0 ≤ B ^ 2 / a := by positivity
    linarith
  have hμB : B ^ 2 ≤ μ * a := by
    have h : μ * a = a ^ 2 + B ^ 2 := by
      rw [hμ]
      field_simp
    nlinarith [sq_nonneg a]
  -- `H` is symmetric and positive definite, so `K = H + μ I` is invertible.
  have hHpd : H.PosDef := (rieszMatrix_posDef s N hN).smul two_pos
  have hKpd : K.PosDef := hHpd.add (PosDef.one.smul hμpos)
  have hHsym : Hᵀ = H := by
    have h := hHpd.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hKdet : IsUnit K.det := isUnit_iff_ne_zero.2 hKpd.det_pos.ne'
  have hKinv : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hKdet
  have hKinv' : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hKdet
  have hKsym : Kᵀ = K := by
    rw [hK, transpose_add, hHsym, transpose_smul, transpose_one]
  have hAsym : Aᵀ = A := by
    rw [hAdef, transpose_smul, transpose_nonsing_inv, hKsym]
  have hTsym : ((1 / 2 : ℝ) • (A * M + M * A))ᵀ = (1 / 2 : ℝ) • (A * M + M * A) := by
    rw [transpose_smul, transpose_add, transpose_mul, transpose_mul, hAsym, hMsym, add_comm]
  have hT : ((1 / 2 : ℝ) • (A * M + M * A)).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.2 hTsym
  -- The quadratic form of `(1/2)(A M + M A)` is `(A w) ⬝ᵥ (M w)`.
  have hquad : ∀ w : Fin (N : ℕ) → ℝ,
      w ⬝ᵥ (((1 / 2 : ℝ) • (A * M + M * A)) *ᵥ w) = (A *ᵥ w) ⬝ᵥ (M *ᵥ w) := by
    intro w
    have h1 := dotProduct_mulVec_eq_of_transpose_eq hAsym w (M *ᵥ w)
    have h2 := dotProduct_mulVec_eq_of_transpose_eq hMsym w (A *ᵥ w)
    have h3 := dotProduct_comm (M *ᵥ w) (A *ᵥ w)
    rw [smul_mulVec, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_smul,
      dotProduct_add, h1, h2, h3, smul_eq_mul]
    ring
  rw [FiniteMatrixOrder.smul_one_le_iff hT]
  intro u
  obtain ⟨v, rfl⟩ : ∃ v, u = K *ᵥ v := ⟨K⁻¹ *ᵥ u, by rw [mulVec_mulVec, hKinv, one_mulVec]⟩
  have hAu : A *ᵥ (K *ᵥ v) = μ • v := by
    rw [hAdef, smul_mulVec, mulVec_mulVec, hKinv', one_mulVec]
  rw [hquad, hAu, smul_dotProduct,
    dotProduct_mulVec_eq_of_transpose_eq hMsym v (K *ᵥ v), smul_eq_mul]
  -- Write `K v = H v + μ v` and `M v = H v + E v`.
  have hKv : K *ᵥ v = H *ᵥ v + μ • v := by
    simp only [hK, add_mulVec, smul_mulVec, one_mulVec]
  have hMv : M *ᵥ v = H *ᵥ v + E *ᵥ v := by
    rw [hE, sub_mulVec]
    abel
  -- The real quantities of the proof: `P = |H v|²`, `Y = (H v)·v`, `Z = (E v)·(H v)`,
  -- `S = |E v|²`, `Q = |v|²` and `W = v·(M v)`.
  have hS : (E *ᵥ v) ⬝ᵥ (E *ᵥ v) ≤ B ^ 2 * (v ⬝ᵥ v) :=
    dotProduct_mulVec_self_le_of_norm_le E hMB v
  have hMherm : M.IsHermitian := Matrix.isHermitian_iff_isSymm.2 hMsymm
  have hW : a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v) :=
    (FiniteMatrixOrder.smul_one_le_iff hMherm a).1 hMa v
  have hXexp : (K *ᵥ v) ⬝ᵥ (K *ᵥ v) =
      (H *ᵥ v) ⬝ᵥ (H *ᵥ v) + 2 * μ * ((H *ᵥ v) ⬝ᵥ v) + μ ^ 2 * (v ⬝ᵥ v) := by
    rw [hKv]
    simp only [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm v (H *ᵥ v)]
    ring
  have hMKexp : (M *ᵥ v) ⬝ᵥ (K *ᵥ v) =
      (H *ᵥ v) ⬝ᵥ (H *ᵥ v) + (E *ᵥ v) ⬝ᵥ (H *ᵥ v) + μ * (v ⬝ᵥ (M *ᵥ v)) := by
    rw [hMv, hKv]
    simp only [add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm v (H *ᵥ v), dotProduct_comm v (E *ᵥ v)]
  -- Nonnegativity of `|H v + E v|²` and `|H v - μ v|²` gives the two bounds on the cross terms.
  have hRp : 0 ≤ 2 * ((E *ᵥ v) ⬝ᵥ (H *ᵥ v)) + (H *ᵥ v) ⬝ᵥ (H *ᵥ v) +
      (E *ᵥ v) ⬝ᵥ (E *ᵥ v) := by
    have h0 := dotProduct_self_nonneg' (E *ᵥ v + H *ᵥ v)
    simp only [add_dotProduct, dotProduct_add] at h0
    rw [dotProduct_comm (H *ᵥ v) (E *ᵥ v)] at h0
    linarith
  have hYb : 0 ≤ (H *ᵥ v) ⬝ᵥ (H *ᵥ v) - 2 * μ * ((H *ᵥ v) ⬝ᵥ v) + μ ^ 2 * (v ⬝ᵥ v) := by
    have h0 := dotProduct_self_nonneg' (H *ᵥ v - μ • v)
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      at h0
    rw [dotProduct_comm v (H *ᵥ v)] at h0
    linarith
  have hPnn : 0 ≤ (H *ᵥ v) ⬝ᵥ (H *ᵥ v) := dotProduct_self_nonneg' _
  have hQnn : 0 ≤ v ⬝ᵥ v := dotProduct_self_nonneg' _
  -- Final inequality, in the real variables above.
  rw [hXexp, hMKexp]
  have m1 := mul_nonneg hμpos.le hRp
  have m2 := mul_nonneg (mul_nonneg hμpos.le hμpos.le) (sub_nonneg.2 hW)
  have m3 := mul_nonneg hμpos.le (sub_nonneg.2 hS)
  have m4 := mul_nonneg (by positivity : (0 : ℝ) ≤ a / 4) hYb
  have m5 := mul_nonneg (sub_nonneg.2 hμa) hPnn
  have m6 := mul_nonneg (mul_nonneg hμpos.le (sub_nonneg.2 hμB)) hQnn
  nlinarith [m1, m2, m3, m4, m5, m6]

end Riesz2

end
end
