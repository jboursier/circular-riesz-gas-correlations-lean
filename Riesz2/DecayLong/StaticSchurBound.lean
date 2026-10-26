/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.OperatorSchur
public import Mathlib.Analysis.Normed.Operator.Banach
public import Riesz2.Frozen.PeriodizedMatrixBounds

/-!
# Static Schur bound for Lemma 5.4

The finite minimization and exterior resolvent comparison in Lemma 5.4.
The bounded form-domain interface is shared with the restriction proof.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.BoundedMatrixForms

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  {ρ : Measure α} (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
  (M : α → Matrix ι ι ℝ)
  (hMm : ∀ i j, Measurable (fun x => M x i j))
  (hMb : ∃ b : ℝ, ∀ᵐ x ∂ρ, ∀ i j, |M x i j| ≤ b)

include hMm hMb in
omit [DecidableEq ι] in
/-- Bounded entries make every matrix cross pairing of L² fields integrable. -/
theorem integrable_pair (u v : ι → Lp ℝ 2 ρ) :
    Integrable (matrixFieldPair M u v) ρ := by
  obtain ⟨b, hb⟩ := hMb
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hp := ((Lp.memLp (u i)).integrable_mul (Lp.memLp (v j))).bdd_mul
    (hMm i j).aestronglyMeasurable
    (hb.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx i j))
  simpa only [Pi.mul_apply, mul_left_comm, mul_assoc] using hp

include hMm hMb in
omit [DecidableEq ι] in
/-- For bounded matrices the finite-energy condition imposes only the
specified component constraint, on the entire scalar form domain. -/
theorem domain_iff (S : Submodule ℝ (ι → ℝ)) (u : ι → Q.1) :
    WeightedFormDomain Q M S u ↔ ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S :=
  ⟨fun h => h.1, fun h => ⟨h, integrable_pair M hMm hMb _ _⟩⟩

variable (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef)

/-- Forgetting the square-root coordinate is bijective for a bounded matrix.
The natural domain and the full Sobolev product therefore have equivalent norms. -/
def equiv : MatrixEnergy.Natural Q hQ M ⊤ hM ≃L[ℝ] MatrixEnergy.Vector (ι := ι) Q hQ := by
  let b : MatrixEnergy.Natural Q hQ M ⊤ hM →L[ℝ] MatrixEnergy.Vector (ι := ι) Q hQ :=
    MatrixEnergy.base (ι := ι) (κ := ι) (MatrixEnergy.vectorValue Q hQ)
      (fun x => CFC.sqrt (M x)) ⊤
  refine ContinuousLinearEquiv.ofBijective b
    (LinearMap.ker_eq_bot.mpr (MatrixEnergy.base_injective (ι := ι) (κ := ι) _ _ _))
    (LinearMap.range_eq_top.mpr ?_)
  intro u
  obtain ⟨z, hz⟩ := MatrixEnergy.exists_tuple Q hQ M ⊤ hM hMm
    (MatrixEnergy.vectorEquiv Q hQ u)
    ((domain_iff Q M hMm hMb ⊤ _).mpr (Eventually.of_forall (fun _ => Submodule.mem_top)))
  refine ⟨z, ?_⟩
  apply (MatrixEnergy.vectorEquiv Q hQ).injective
  exact hz

theorem equiv_tuple (z : MatrixEnergy.Natural Q hQ M ⊤ hM) :
    MatrixEnergy.vectorEquiv Q hQ (equiv Q hQ M hMm hMb hM z) =
      MatrixEnergy.tuple Q hQ M ⊤ hM z := rfl

theorem tuple_equiv_symm (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    MatrixEnergy.tuple Q hQ M ⊤ hM ((equiv Q hQ M hMm hMb hM).symm u) =
      MatrixEnergy.vectorEquiv Q hQ u := by
  rw [← equiv_tuple Q hQ M hMm hMb hM, ContinuousLinearEquiv.apply_symm_apply]

/-- The full bounded-coefficient form, transported from the existing natural
matrix-energy graph to the literal product of scalar form domains. -/
def form : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
    MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ :=
  (MatrixEnergy.weakForm Q hQ M ⊤ hM).bilinearComp
    (equiv Q hQ M hMm hMb hM).symm.toContinuousLinearMap
    (equiv Q hQ M hMm hMb hM).symm.toContinuousLinearMap

theorem form_apply (u v : MatrixEnergy.Vector (ι := ι) Q hQ) :
    form Q hQ M hMm hMb hM u v =
      (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ u i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
      ∫ x, matrixFieldPair M (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) x ∂ρ := by
  exact (MatrixEnergy.weakForm_apply Q hQ M ⊤ hM
    ((equiv Q hQ M hMm hMb hM).symm u)
    ((equiv Q hQ M hMm hMb hM).symm v)).trans (by
      rw [tuple_equiv_symm Q hQ M hMm hMb hM,
        tuple_equiv_symm Q hQ M hMm hMb hM])

theorem form_symmetric (u v : MatrixEnergy.Vector (ι := ι) Q hQ) :
    form Q hQ M hMm hMb hM u v = form Q hQ M hMm hMb hM v u :=
  MatrixEnergy.weakForm_symm Q hQ M ⊤ hM _ _

include hMm hMb hM in
/-- The transported equation is exactly the unrestricted weak equation. -/
theorem equation_iff (u : MatrixEnergy.Vector (ι := ι) Q hQ) (f : ι → Lp ℝ 2 ρ) :
    (∀ v, form Q hQ M hMm hMb hM u v =
      inner ℝ (WithLp.toLp 2 f) (OperatorSchur.vectorValues Q hQ v)) ↔
      WeightedWeakSolution Q M ⊤ f (MatrixEnergy.vectorEquiv Q hQ u) := by
  rw [← tuple_equiv_symm Q hQ M hMm hMb hM u,
    MatrixEnergy.weightedWeakSolution_iff Q hQ M ⊤ hM hMm]
  constructor
  · intro h w
    have he := h (equiv Q hQ M hMm hMb hM w)
    simpa only [form, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      PiLp.inner_apply, OperatorSchur.vectorValues_apply, equiv_tuple,
      MatrixEnergy.sourcePairing_apply] using he
  · intro h v
    have he := h ((equiv Q hQ M hMm hMb hM).symm v)
    simpa only [form, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe, PiLp.inner_apply,
      OperatorSchur.vectorValues_apply, tuple_equiv_symm,
      MatrixEnergy.sourcePairing_apply] using he

include hMm hMb hM in
/-- The deterministic pointwise lower bound gives coercivity in the full
Sobolev norm, with diffusion coefficient exactly one. -/
theorem form_coercive (a : ℝ)
    (ha : ∀ᵐ x ∂ρ, ∀ t : ι → ℝ,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    min 1 a * ‖u‖ ^ 2 ≤ form Q hQ M hMm hMb hM u u := by
  let z := (equiv Q hQ M hMm hMb hM).symm u
  have hm := MatrixEnergy.matrix_lower_bound Q hQ M ⊤ hM a
    (ha.mono (fun x hx t _ => hx t)) z
  have hv : MatrixEnergy.values Q hQ M ⊤ hM z = OperatorSchur.vectorValues Q hQ u := by
    ext i
    rw [MatrixEnergy.values_apply, tuple_equiv_symm]
    rfl
  rw [hv, tuple_equiv_symm] at hm
  have he := OperatorSchur.vectorEnergy_nonneg Q hQ u
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left 1 a) he
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right 1 a)
    (sq_nonneg ‖OperatorSchur.vectorValues Q hQ u‖)
  rw [OperatorSchur.vector_norm_sq Q hQ, form_apply, OperatorSchur.vectorEnergy_apply]
  rw [OperatorSchur.vectorEnergy_apply] at he h₁
  nlinarith only [hm, h₁, h₂]

end Riesz2.BoundedMatrixForms

namespace Riesz2.StaticSchurBound

open Matrix

section Finite

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Lemma 5.4, finite minimization in equation (5.14): evaluate the block matrix
at the minimizing exterior vector `-D⁻¹Bᵀu`, retaining the active mass. -/
theorem static_schur_lower (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ) (hD : D.PosDef) (a : ℝ) (ha : 0 ≤ a)
    (hfull : ∀ u z, a * (u ⬝ᵥ u + z ⬝ᵥ z) ≤
      Sum.elim u z ⬝ᵥ (Matrix.fromBlocks A B Bᵀ D *ᵥ Sum.elim u z))
    (u : ι → ℝ) :
    a * (u ⬝ᵥ u) ≤ u ⬝ᵥ (A *ᵥ u) -
      (Bᵀ *ᵥ u) ⬝ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ u)) := by
  let z := -(D⁻¹ *ᵥ (Bᵀ *ᵥ u))
  have hsolve : D *ᵥ z = -(Bᵀ *ᵥ u) := by
    rw [mulVec_neg, mulVec_mulVec, D.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hD.det_pos.ne'),
      one_mulVec]
  have hb : u ⬝ᵥ (B *ᵥ z) = (Bᵀ *ᵥ u) ⬝ᵥ z := by
    rw [dotProduct_mulVec, ← vecMul_transpose Bᵀ u, transpose_transpose]
  have hval : Sum.elim u z ⬝ᵥ (Matrix.fromBlocks A B Bᵀ D *ᵥ Sum.elim u z) =
      u ⬝ᵥ (A *ᵥ u) - (Bᵀ *ᵥ u) ⬝ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ u)) := by
    rw [fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add, hsolve, hb,
      dotProduct_neg, dotProduct_comm z (Bᵀ *ᵥ u)]
    dsimp only [z]
    simp only [dotProduct_neg, neg_dotProduct]
    rw [dotProduct_comm (D⁻¹ *ᵥ (Bᵀ *ᵥ u)) (Bᵀ *ᵥ u)]
    ring
  have h := hfull u z
  rw [hval] at h
  have hz : 0 ≤ a * (z ⬝ᵥ z) :=
    mul_nonneg ha (Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i)))
  linarith

/-- Lemma 5.4, the finite variational inequality underlying
`0 ≤ (D + β⁻¹L)⁻¹ ≤ D⁻¹`. -/
theorem matrix_variational_upper {D : Matrix κ κ ℝ} (hD : D.PosDef)
    (v w : κ → ℝ) :
    2 * (v ⬝ᵥ w) - w ⬝ᵥ (D *ᵥ w) ≤ v ⬝ᵥ (D⁻¹ *ᵥ v) := by
  have hsolve : D *ᵥ (D⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, D.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hD.det_pos.ne'), one_mulVec]
  have hsym (a b : κ → ℝ) : a ⬝ᵥ (D *ᵥ b) = b ⬝ᵥ (D *ᵥ a) := by
    have ht : Dᵀ = D := by simpa only [conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.eq
    rw [dotProduct_mulVec, ← vecMul_transpose D a, ht, dotProduct_comm]
  have h := hD.posSemidef.dotProduct_mulVec_nonneg (w - D⁻¹ *ᵥ v)
  simp only [star_trivial, mulVec_sub, dotProduct_sub, sub_dotProduct, hsolve] at h
  rw [hsym (D⁻¹ *ᵥ v) w, hsolve, dotProduct_comm w v,
    dotProduct_comm (D⁻¹ *ᵥ v) v] at h
  linarith

end Finite

/-- Lemma 5.4, the original labels of the active and exterior blocks. -/
def blockIndex (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) :
    Fin (n : ℕ) ⊕ Fin ((m : ℕ) - (n : ℕ)) ≃ Fin (m : ℕ) :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hnm))

/-- Lemma 5.4, the active finite block A₀. -/
def activeMatrix (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (P : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  P.submatrix (fun i => blockIndex n m hnm (.inl i)) (fun i => blockIndex n m hnm (.inl i))

/-- Lemma 5.4, the constant finite coupling block B. -/
def crossMatrix (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (P : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) :
    Matrix (Fin (n : ℕ)) (Fin ((m : ℕ) - (n : ℕ))) ℝ :=
  P.submatrix (fun i => blockIndex n m hnm (.inl i)) (fun i => blockIndex n m hnm (.inr i))

/-- Lemma 5.4, the constant exterior finite block D, including dimension zero. -/
def exteriorMatrix (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (P : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) :
    Matrix (Fin ((m : ℕ) - (n : ℕ))) (Fin ((m : ℕ) - (n : ℕ))) ℝ :=
  P.submatrix (fun i => blockIndex n m hnm (.inr i)) (fun i => blockIndex n m hnm (.inr i))

/-- Lemma 5.4, finite block reassembly, with the lower-left block Bᵀ. -/
theorem reindex_eq_fromBlocks (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (P : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (hs : ∀ i j, P i j = P j i) :
    P.submatrix (blockIndex n m hnm) (blockIndex n m hnm) =
      Matrix.fromBlocks (activeMatrix n m hnm P) (crossMatrix n m hnm P)
        (crossMatrix n m hnm P)ᵀ (exteriorMatrix n m hnm P) := by
  ext (i | i) (j | j) <;> simp [activeMatrix, crossMatrix, exteriorMatrix, hs]

/-- Lemma 5.4, a strictly positive finite mass makes the matrix positive
 definite, including on the empty exterior carrier. -/
theorem posDef_of_mass {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hs : ∀ i j, P i j = P j i) (a : ℝ) (ha : 0 < a)
    (hl : ∀ u : ι → ℝ, a * (∑ i, u i ^ 2) ≤ ∑ i, ∑ j, u i * P i j * u j) : P.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun u hu => ?_⟩
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hs j i
  · have hpos : 0 < ∑ i, u i ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
      exact (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i))
    have h := (mul_pos ha hpos).trans_le (hl u)
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using h

/-- Lemma 5.4, equation (5.14) for the periodized matrix blocks.
Positivity of the fixed exterior is asserted almost everywhere. -/
theorem periodized_static_schur_lower {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ) (hC : 1 ≤ C)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M) :
    let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
    let B := crossMatrix n m hnm H
    let D := exteriorMatrix n m hnm H
    ∀ᵐ x ∂ρ, D.PosDef ∧ ∀ u : Fin (n : ℕ) → ℝ,
      (C⁻¹ * (n : ℝ) ^ (-κ * ε)) * (u ⬝ᵥ u) ≤
        u ⬝ᵥ (activeMatrix n m hnm (M x) *ᵥ u) -
          (Bᵀ *ᵥ u) ⬝ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ u)) := by
  let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
  let a := C⁻¹ * (n : ℝ) ^ (-κ * ε)
  have ha : 0 < a := mul_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC))
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  filter_upwards [hP.2.1] with x hx
  have hp := posDef_of_mass (M x) hx.1 a ha hx.2.2.1
  have hext : exteriorMatrix n m hnm (M x) = exteriorMatrix n m hnm H := by
    ext i j
    apply hx.2.1
    left
    simp [blockIndex]
  have hcross : crossMatrix n m hnm (M x) = crossMatrix n m hnm H := by
    ext i j
    apply hx.2.1
    right
    simp [blockIndex]
  have hd : (exteriorMatrix n m hnm H).PosDef := by
    rw [← hext]
    exact hp.submatrix ((blockIndex n m hnm).injective.comp Sum.inr_injective)
  refine ⟨hd, fun u => ?_⟩
  apply static_schur_lower _ _ _ hd a ha.le
  intro v z
  let t := Sum.elim v z ∘ (blockIndex n m hnm).symm
  have ht := hx.2.2.1 t
  have hsum : (∑ i, t i ^ 2) = v ⬝ᵥ v + z ⬝ᵥ z := by
    rw [← (blockIndex n m hnm).sum_comp]
    simp [t, Fintype.sum_sum_type, dotProduct, pow_two]
  have hquad : (∑ i, ∑ j, t i * M x i j * t j) =
      Sum.elim v z ⬝ᵥ ((M x).submatrix (blockIndex n m hnm) (blockIndex n m hnm) *ᵥ
        Sum.elim v z) := by
    rw [← (blockIndex n m hnm).sum_comp]
    simp only [t, Function.comp_apply, Equiv.symm_apply_apply]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (blockIndex n m hnm).sum_comp]
    simp [mul_assoc]
  rw [hsum, hquad, reindex_eq_fromBlocks n m hnm _ hx.1, hext, hcross] at ht
  exact ht

end Riesz2.StaticSchurBound

namespace Riesz2.StaticSchurBound

open Matrix

section Fields

variable {α ι κ : Type*} [MeasurableSpace α] {ρ : Measure α}
  [Fintype ι] [Fintype κ]

/-- Lemma 5.4, the pointwise finite matrix pairing of two L² fields. -/
def fieldPair (P : Matrix ι κ ℝ) (u : ι → Lp ℝ 2 ρ) (v : κ → Lp ℝ 2 ρ) (x : α) : ℝ :=
  (fun i => u i x) ⬝ᵥ (P *ᵥ fun j => v j x)

/-- Lemma 5.4, bounded finite matrix pairings are integrable for arbitrary
L² fields, without restricting their dependence on the configuration. -/
theorem integrable_fieldPair (P : Matrix ι κ ℝ) (u : ι → Lp ℝ 2 ρ)
    (v : κ → Lp ℝ 2 ρ) : Integrable (fieldPair P u v) ρ := by
  change Integrable (fun x => ∑ i, u i x * (∑ j, P i j * v j x)) ρ
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa only [Pi.mul_apply, mul_left_comm] using
    ((Lp.memLp (u i)).integrable_mul (Lp.memLp (v j))).const_mul (P i j)

/-- Lemma 5.4, constant finite matrices act on the whole L² product. -/
def fieldMul (P : Matrix ι κ ℝ) (v : κ → Lp ℝ 2 ρ) : ι → Lp ℝ 2 ρ :=
  fun i => ∑ j, P i j • v j

/-- Lemma 5.4, the L² matrix action has its literal pointwise representative. -/
theorem fieldMul_coe (P : Matrix ι κ ℝ) (v : κ → Lp ℝ 2 ρ) :
    ∀ᵐ x ∂ρ, ∀ i, fieldMul P v i x = (P *ᵥ fun j => v j x) i := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => P i j • v j),
    ae_all_iff.mpr (fun j => Lp.coeFn_smul (P i j) (v j))] with x hs hc
  rw [fieldMul, hs]
  exact Finset.sum_congr rfl (fun j _ => hc j)

/-- Lemma 5.4, the L² product pairing is the integral of the pointwise dot product. -/
theorem inner_eq_integral_dot (u v : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    inner ℝ u v = ∫ x, (fun i => u i x) ⬝ᵥ (fun i => v i x) ∂ρ := by
  rw [PiLp.inner_apply]
  simp only [dotProduct]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    simp only [Real.inner_apply]
  · intro i _
    exact (Lp.memLp (u i)).integrable_mul (Lp.memLp (v i))

/-- Lemma 5.4, the finite coupling B is represented by the L² source Bᵀu. -/
theorem fieldMul_transpose_pair (B : Matrix ι κ ℝ)
    (u : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (w : PiLp 2 (fun _ : κ => Lp ℝ 2 ρ)) :
    (∫ x, fieldPair B u.ofLp w.ofLp x ∂ρ) =
      inner ℝ (WithLp.toLp 2 (fieldMul Bᵀ u.ofLp)) w := by
  rw [inner_eq_integral_dot]
  apply integral_congr_ae
  filter_upwards [fieldMul_coe Bᵀ u.ofLp] with x hx
  change _ = (fun i => fieldMul Bᵀ u.ofLp i x) ⬝ᵥ (fun i => w i x)
  simp_rw [hx]
  rw [dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec B (fun i => w i x) (fun i => u i x)).symm

/-- Lemma 5.4, scaling both fields scales a static quadratic integral by β². -/
theorem integral_fieldPair_smul (D : Matrix ι ι ℝ) (β : ℝ)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    (∫ x, fieldPair D (β • f).ofLp (β • f).ofLp x ∂ρ) =
      β ^ 2 * ∫ x, fieldPair D f.ofLp f.ofLp x ∂ρ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_smul β (f i))] with x hx
  have hv : ∀ i, (β • f) i x = β * f i x := hx
  simp only [fieldPair]
  simp_rw [hv]
  change (β • fun i => f i x) ⬝ᵥ (D *ᵥ (β • fun i => f i x)) = _
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- Lemma 5.4, the integrated finite inverse variational bound for arbitrary
L² fields, retaining the exact temperature factor. -/
theorem field_variational_upper [DecidableEq ι] {D : Matrix ι ι ℝ} (hD : D.PosDef)
    {β : ℝ} (hβ : 0 < β) (f w : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    2 * inner ℝ f w - β * ∫ x, fieldPair D w.ofLp w.ofLp x ∂ρ ≤
      β⁻¹ * ∫ x, fieldPair D⁻¹ f.ofLp f.ofLp x ∂ρ := by
  have hip : Integrable (fun x => (fun i => f i x) ⬝ᵥ (fun i => w i x)) ρ :=
    integrable_finsetSum _ (fun i _ => (Lp.memLp (f i)).integrable_mul (Lp.memLp (w i)))
  rw [inner_eq_integral_dot, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hip.const_mul 2) ((integrable_fieldPair D _ _).const_mul β),
    ← integral_const_mul]
  apply integral_mono_ae ((hip.const_mul 2).sub ((integrable_fieldPair D _ _).const_mul β))
    ((integrable_fieldPair D⁻¹ _ _).const_mul β⁻¹)
  filter_upwards with x
  have h := mul_le_mul_of_nonneg_left
    (matrix_variational_upper hD (β⁻¹ • fun i => f i x) (fun i => w i x)) hβ.le
  rw [smul_dotProduct, mulVec_smul, smul_dotProduct, dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  dsimp only [fieldPair, Pi.sub_apply]
  convert h using 1 <;> field_simp

end Fields

section Resolvent

variable {α ι V : Type*} [MeasurableSpace α] {ρ : Measure α}
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Internal form comparison for Lemma 5.4: adding a nonnegative scalar
energy to βD decreases its inverse, for every exterior L² source. -/
theorem internal_exterior_resolvent_le_static_inverse (D : Matrix ι ι ℝ) (hD : D.PosDef)
    (β : ℝ) (hβ : 0 < β) (E : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hE : ∀ z, c * ‖z‖ ^ 2 ≤ E z z)
    (J : V →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (hl : ∀ z, β * (∫ x, fieldPair D (J z).ofLp (J z).ofLp x ∂ρ) ≤ E z z)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    let z := CoerciveSolution.solution E c hc hE J f
    0 ≤ inner ℝ f (J z) ∧ inner ℝ f (J z) ≤
      β⁻¹ * ∫ x, fieldPair D⁻¹ f.ofLp f.ofLp x ∂ρ := by
  dsimp only
  let z := CoerciveSolution.solution E c hc hE J f
  have he : E z z = inner ℝ f (J z) :=
    CoerciveSolution.solution_solves E c hc hE J f z
  have hpos : 0 ≤ E z z := (mul_nonneg hc.le (sq_nonneg _)).trans (hE z)
  have hvar := field_variational_upper hD hβ f (J z)
  have hlower := hl z
  exact ⟨he ▸ hpos, by linarith⟩

end Resolvent

end Riesz2.StaticSchurBound
