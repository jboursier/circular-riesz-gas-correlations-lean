/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedField
public import Riesz2.DecayLong.BoundarySchurBounds

/-!
# The actual exterior Schur field

Reindex the exterior form of Subsection 5.5 to the carrier used by
Lemma 5.5, retaining the scalar form and both temperature factors.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical

namespace Riesz2.LocalizedFieldPart3

/-- See Subsection 5.5 of the paper: the exterior labels, in their original cycle. -/
def exteriorIndexEquiv (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) :
    Fin ((m : ℕ) - (n : ℕ)) ≃
      ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)) where
  toFun i := ⟨⟨(n : ℕ) + i.val, by have := i.isLt; omega⟩, by simp⟩
  invFun a := ⟨a.val.val - (n : ℕ), by
    have := a.val.isLt
    have : (n : ℕ) ≤ a.val.val := (Finset.mem_filter.mp a.property).2
    omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have : (n : ℕ) ≤ a.val.val := (Finset.mem_filter.mp a.property).2
    dsimp
    omega

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See Subsection 5.5 of the paper: isometric reindexing, with no change of scalar form domain. -/
def exteriorReindex (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (ScalarFormHilbert.Space Q hQ)
    (exteriorIndexEquiv n m hnm)

/-- See Subsection 5.5 of the paper: reindexed exterior values are the assembled values. -/
theorem reindex_values_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (a : ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val))) :
    (MatrixEnergy.vectorEquiv Q hQ (exteriorReindex Q hQ n m hnm w) a).val =
      (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) a.val).val := by
  let i := (exteriorIndexEquiv n m hnm).symm a
  have he : Fin.cast (Nat.add_sub_of_le hnm) (Fin.natAdd (n : ℕ) i) = a.val := by
    apply Fin.ext
    have : (n : ℕ) ≤ a.val.val := (Finset.mem_filter.mp a.property).2
    change (n : ℕ) + (a.val.val - (n : ℕ)) = a.val.val
    omega
  change (ScalarFormHilbert.equiv Q hQ (w i)).val =
    (ScalarFormHilbert.equiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w) a.val)).val
  rw [← he, LocalizedBoundary.assemble_right_apply_internal]

/-- See Subsection 5.5 of the paper: exterior sums equal subtype sums, with zero active coordinates. -/
theorem sum_exterior_internal {V : Type*} [AddCommMonoid V]
    (n m : ℕ+) (_hnm : (n : ℕ) ≤ (m : ℕ))
    (f : Fin (m : ℕ) → V) (hf : ∀ i, i.val < (n : ℕ) → f i = 0) :
    (∑ i, f i) = ∑ a : ↥(Finset.univ.filter
      (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)), f a.val := by
  symm
  rw [Finset.sum_coe_sort, Finset.sum_filter]
  symm
  ·
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (n : ℕ) ≤ i.val
    · simp [hi]
    · simp [hi, hf i (by omega)]

/-- See Subsection 5.5 of the paper: the exterior matrix pairing is unchanged by reindexing. -/
theorem exterior_pair_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (H : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (w v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    matrixFieldPair (fun _ : Ω => H)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) =ᵐ[ν]
    matrixFieldPair (fun _ : Ω => H.submatrix Subtype.val Subtype.val)
      (OperatorSchur.vectorValues Q hQ (exteriorReindex Q hQ n m hnm w)).ofLp
      (OperatorSchur.vectorValues Q hQ (exteriorReindex Q hQ n m hnm v)).ofLp := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  have hz (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
      (i : Fin (m : ℕ)) (hi : i.val < (n : ℕ)) :
      (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, z)) i).val x = 0 := by
    rw [SchurRestriction.exterior_values_zero Q hQ n m hnm z i hi]
    exact hx
  unfold matrixFieldPair
  rw [sum_exterior_internal n m hnm _ (fun i hi => by simp [hz w i hi])]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_exterior_internal n m hnm _ (fun i hi => by simp [hz v i hi])]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.submatrix_apply, OperatorSchur.vectorValues_apply,
    reindex_values_internal]


/-- See Subsection 5.5 of the paper: reindexing preserves the componentwise scalar energy. -/
theorem reindex_energy_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (w v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    (∑ a, Q.2 (MatrixEnergy.vectorEquiv Q hQ (exteriorReindex Q hQ n m hnm w) a)
      (MatrixEnergy.vectorEquiv Q hQ (exteriorReindex Q hQ n m hnm v) a)) =
    ∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i) := by
  exact (exteriorIndexEquiv n m hnm).symm.sum_comp
    (fun i => Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i))

/-- See Subsection 5.5 of the paper: a constant matrix pairing is the finite sum of L² pairings. -/
theorem integral_pair_internal {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (u v : ι → Lp ℝ 2 ν) :
    (∫ x, matrixFieldPair (fun _ : Ω => H) u v x ∂ν) =
      ∑ i, ∑ j, H i j * inner ℝ (u i) (v j) := by
  have hi (i j : ι) : Integrable (fun x => u i x * H i j * v j x) ν := by
    simpa only [Pi.mul_apply, mul_left_comm, mul_comm, mul_assoc] using
      ((Lp.memLp (u i)).integrable_mul (Lp.memLp (v j))).const_mul (H i j)
  simp only [matrixFieldPair]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.inner_apply]
  ring

/-- See Subsection 5.5 of the paper: exterior reference coupling, as an L² class. -/
def referenceRow (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (z : MatrixEnergy.Vector
      (ι := ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val))) Q hQ)
    (l : Fin (m : ℕ)) : Lp ℝ 2 ν :=
  ∑ a, (2 * referenceIntervalMatrix s m hm K l a.val) •
    (MatrixEnergy.vectorEquiv Q hQ z a).val

/-- See the proof of Proposition 5.15 in the paper: the row pairing is the tensor pairing of Lemma 5.5. -/
theorem row_pair_internal (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (z : MatrixEnergy.Vector
      (ι := ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val))) Q hQ)
    (l : Fin (m : ℕ)) (η : Lp ℝ 2 ν) :
    inner ℝ η (referenceRow Q hQ s n m hm K z l) =
      inner ℝ (BoundarySchurBounds.tensor
        (fun a => 2 * referenceIntervalMatrix s m hm K l a.val) η)
        (OperatorSchur.vectorValues Q hQ z) := by
  simp only [referenceRow, inner_sum, real_inner_smul_right, PiLp.inner_apply,
    BoundarySchurBounds.tensor, real_inner_smul_left,
    OperatorSchur.vectorValues_apply]

/-- See Subsection 5.5 of the paper: the assembled cross pairing is the sum of tensor sources. -/
theorem cross_pair_internal (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
    inner ℝ (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (fun a : ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)) =>
        2 * referenceIntervalMatrix s m hm K (i.castLE hnm) a.val)
      (MatrixEnergy.vectorEquiv Q hQ p i).val)
      (OperatorSchur.vectorValues Q hQ (exteriorReindex Q hQ n m hnm v)) := by
  rw [integral_pair_internal]
  rw [LocalizedBoundary.sum_active_internal n m hnm _ (fun i hi => by
    rw [LocalizedBoundary.active_extension_zero_internal Q hQ n m hnm p i hi]
    simp)]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_exterior_internal n m hnm _ (fun a ha => by
    rw [SchurRestriction.exterior_values_zero Q hQ n m hnm v a ha]
    simp)]
  simp only [PiLp.inner_apply, BoundarySchurBounds.tensor,
    real_inner_smul_left, OperatorSchur.vectorValues_apply, reindex_values_internal,
    Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  change _ * inner ℝ (ScalarFormHilbert.equiv Q hQ
    (SchurRestriction.assemble Q hQ n m hnm (p, 0) (i.castLE hnm))).val _ = _
  rw [SchurRestriction.assemble_left_apply]
  rfl


/-- See Subsection 5.5 of the paper: the reindexed exterior form is exactly βD + L. -/
theorem exterior_form_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (β : ℝ)
    (hD : (β • (((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
      (Subtype.val : ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)) → Fin (m : ℕ))
      Subtype.val)).PosSemidef)
    (w v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    BoundarySchurBounds.constantForm Q hQ _ hD
      (exteriorReindex Q hQ n m hnm w) (exteriorReindex Q hQ n m hnm v) =
    (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
      β * ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν := by
  rw [BoundarySchurBounds.constantForm, BoundedMatrixForms.form_apply,
    reindex_energy_internal]
  congr 1
  rw [SchurRestriction.integral_pair_smul]
  congr 1
  exact (integral_congr_ae (exterior_pair_internal Q hQ n m hnm _ w v)).symm

/-- See the proof of Proposition 5.15: identify the actual normalized
exterior equation in `loc_boundary` with the unique resolvent in Lemma 5.5.
This internal lemma takes the exact equation, rather than an estimate. -/
theorem reindexed_resolvent_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (β : ℝ) (hβ : 0 < β)
    (hD : (β • (((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
      (Subtype.val : ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)) → Fin (m : ℕ))
      Subtype.val)).PosSemidef)
    (R : PiLp 2 (fun _ : ↥(Finset.univ.filter
      (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)) => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := ↥(Finset.univ.filter
        (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val))) Q hQ)
    (huniq : ∀ f z, (∀ v, BoundarySchurBounds.constantForm Q hQ _ hD z v =
      inner ℝ f (OperatorSchur.vectorValues Q hQ v)) → z = R f)
    (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (hw : ∀ v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ,
      β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) :
    exteriorReindex Q hQ n m hnm w =
      β • ∑ i : Fin (n : ℕ), R (BoundarySchurBounds.tensor
        (fun a : ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val)) =>
          2 * referenceIntervalMatrix s m hm K (i.castLE hnm) a.val)
        (MatrixEnergy.vectorEquiv Q hQ p i).val) := by
  rw [← map_sum, ← map_smul]
  apply huniq
  intro z
  let v := (exteriorReindex Q hQ n m hnm).symm z
  have he := congrArg (fun t : ℝ => β * t) (hw v)
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul,
    cross_pair_internal] at he
  rw [real_inner_smul_left]
  rw [← (exteriorReindex Q hQ n m hnm).apply_symm_apply z]
  exact (exterior_form_internal Q hQ s n m hnm hm K β hD w v).trans he


/-- See the proof of Proposition 5.15 in the paper: the actual Schur row is linear in its exterior response. -/
theorem row_linear_internal (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (l : Fin (m : ℕ)) :
    IsLinearMap ℝ (fun z => referenceRow Q hQ s n m hm K z l) := by
  constructor
  · intro z v
    simp only [referenceRow, map_add, Pi.add_apply, Submodule.coe_add,
      smul_add, Finset.sum_add_distrib]
  · intro b z
    simp only [referenceRow, map_smul, Pi.smul_apply, Submodule.coe_smul,
      smul_comm b, Finset.smul_sum]

/-- See Subsection 5.5 of the paper: the Schur row is literally the matrix row appearing in
`loc_boundary`, including its temperature factor and its original component order. -/
theorem schur_row_ae_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (C κ γ ε β : ℝ) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (l : Fin (n : ℕ)) :
    (β • referenceRow Q hQ s n m hm K (exteriorReindex Q hQ n m hnm w)
      (l.castLE hnm) : Lp ℝ 2 ν) =ᵐ[ν]
    fun x => ∑ i, (MatrixEnergy.vectorEquiv Q hQ
      (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val x *
        (β * M x i (l.castLE hnm)) := by
  let z := exteriorReindex Q hQ n m hnm w
  have hr := Lp.coeFn_finsetSum Finset.univ (fun a =>
    (2 * referenceIntervalMatrix s m hm K (l.castLE hnm) a.val) •
      (MatrixEnergy.vectorEquiv Q hQ z a).val)
  have hs : ∀ᵐ x ∂ν, ∀ a, ((2 * referenceIntervalMatrix s m hm K
      (l.castLE hnm) a.val) • (MatrixEnergy.vectorEquiv Q hQ z a).val : Lp ℝ 2 ν) x =
    (2 * referenceIntervalMatrix s m hm K (l.castLE hnm) a.val) *
      (MatrixEnergy.vectorEquiv Q hQ z a).val x := by
    rw [ae_all_iff]
    intro a
    exact Lp.coeFn_smul _ _
  filter_upwards [hM.2.1, Lp.coeFn_zero ℝ 2 ν, Lp.coeFn_smul β
    (referenceRow Q hQ s n m hm K z (l.castLE hnm)), hr, hs] with x hx hz hb hr hs
  rw [hb]
  change β * (∑ a, _ : Lp ℝ 2 ν) x = _
  rw [hr]
  rw [sum_exterior_internal n m hnm _ (fun i hi => by
    rw [SchurRestriction.exterior_values_zero Q hQ n m hnm w i hi]
    simp only [hz, Pi.zero_apply, zero_mul])]
  simp only [Finset.sum_apply] at hr ⊢
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hs a]
  have ha : (n : ℕ) ≤ a.val.val := (Finset.mem_filter.mp a.property).2
  rw [hx.2.1 a.val (l.castLE hnm) (Or.inl ha)]
  rw [BoundarySchurBounds.reference_column_eq]
  rw [show (MatrixEnergy.vectorEquiv Q hQ z a).val = _ from
    reindex_values_internal Q hQ n m hnm w a]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

section Estimates

/-- See the proof of Proposition 5.15 in the paper: superposition and duality for the actual
exterior response in `loc_boundary`. Both entry and arbitrary active-row
increment estimates retain the cutoff loss K² and the endpoint source sum.
The equation hypothesis is the exact defining equation, under an internal name. -/
theorem normalized_schur_bounds_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ))
      (K : ℕ) (_hK : 1 ≤ K) (_hKm : K ≤ (m : ℕ) / 4),
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    ∀ (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
      (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ),
    (∀ v : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ,
      β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
        (∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m hm K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (0, v)) i).val) x ∂ν) →
    let field := fun l : Fin (n : ℕ) => β • referenceRow Q hQ s n m hm K
      (exteriorReindex Q hQ n m hnm w) (l.castLE hnm)
    let weight := fun i : Fin (n : ℕ) =>
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2)
    (∀ l, ‖field l‖ ≤ C * (K : ℝ) ^ 2 * weight l *
      ∑ i, weight i * ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖) ∧
    (∀ l k, ‖field l - field k‖ ≤ C * (K : ℝ) ^ 2 * (Nat.dist l.val k.val : ℝ) *
      (min (min (l.val + 1) ((n : ℕ) - l.val))
        (min (k.val + 1) ((n : ℕ) - k.val)) : ℕ) ^ (-1 - s.val / 2) *
      ∑ i, weight i * ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖) := by
  obtain ⟨B, hB, hmain⟩ := BoundarySchurBounds.bilinear_schur_cutoff hzeta s β hβ
  refine ⟨β ^ 2 * B, by positivity, ?_⟩
  intro n m hnm hm K hK hKm Ω _ ν Q hQ p w hw
  obtain ⟨R, _hR, huniq, hest⟩ := hmain m hm K hK hKm (n : ℕ) hnm ν Q hQ
  have he := reindexed_resolvent_internal Q hQ s n m hnm hm K β hβ _ R huniq p w hw
  let E := ↥(Finset.univ.filter (fun a : Fin (m : ℕ) => (n : ℕ) ≤ a.val))
  let col := fun (i : Fin (m : ℕ)) (a : E) => 2 * referenceIntervalMatrix s m hm K i a.val
  let f := fun i : Fin (n : ℕ) => BoundarySchurBounds.tensor
    (col (i.castLE hnm)) (MatrixEnergy.vectorEquiv Q hQ p i).val
  let wt := fun i : Fin (n : ℕ) =>
    ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2)
  have hp (η : Lp ℝ 2 ν) (l : Fin (n : ℕ)) :
      inner ℝ η (β • referenceRow Q hQ s n m hm K
        (exteriorReindex Q hQ n m hnm w) (l.castLE hnm)) =
      β ^ 2 * ∑ i : Fin (n : ℕ), inner ℝ (BoundarySchurBounds.tensor
        (col (l.castLE hnm)) η) (OperatorSchur.vectorValues Q hQ (R (f i))) := by
    rw [he, (row_linear_internal Q hQ s n m hm K (l.castLE hnm)).map_smul]
    rw [real_inner_smul_right, real_inner_smul_right]
    rw [row_pair_internal, map_sum, inner_sum]
    ring
  have hpinc (η : Lp ℝ 2 ν) (l k : Fin (n : ℕ)) :
      inner ℝ η ((β • referenceRow Q hQ s n m hm K
        (exteriorReindex Q hQ n m hnm w) (l.castLE hnm)) -
        (β • referenceRow Q hQ s n m hm K
          (exteriorReindex Q hQ n m hnm w) (k.castLE hnm))) =
      β ^ 2 * ∑ i : Fin (n : ℕ), inner ℝ (BoundarySchurBounds.tensor
        (col (l.castLE hnm) - col (k.castLE hnm)) η)
        (OperatorSchur.vectorValues Q hQ (R (f i))) := by
    rw [inner_sub_right, hp, hp, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← inner_sub_left]
    congr 1
    apply PiLp.ext
    intro a
    change col (l.castLE hnm) a • η - col (k.castLE hnm) a • η =
      (col (l.castLE hnm) a - col (k.castLE hnm) a) • η
    rw [sub_smul]
  dsimp only
  constructor
  · intro l
    apply LocalizedField.norm_of_pairing_bound_internal _ _ (by positivity)
    intro η
    rw [hp, abs_mul, abs_of_nonneg (sq_nonneg β)]
    calc
      _ ≤ β ^ 2 * ∑ i, |inner ℝ (BoundarySchurBounds.tensor (col (l.castLE hnm)) η)
          (OperatorSchur.vectorValues Q hQ (R (f i)))| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ β ^ 2 * ∑ i, B * (K : ℝ) ^ 2 * wt i * wt l * ‖η‖ *
          ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖ := by
        gcongr with i
        exact (hest η (MatrixEnergy.vectorEquiv Q hQ p i).val
          (i.castLE hnm) (l.castLE hnm) (l.castLE hnm) i.isLt l.isLt l.isLt).1
      _ = _ := by simp only [wt, Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  · intro l k
    apply LocalizedField.norm_of_pairing_bound_internal _ _ (by positivity)
    intro η
    rw [hpinc, abs_mul, abs_of_nonneg (sq_nonneg β)]
    calc
      _ ≤ β ^ 2 * ∑ i, |inner ℝ (BoundarySchurBounds.tensor
          (col (l.castLE hnm) - col (k.castLE hnm)) η)
          (OperatorSchur.vectorValues Q hQ (R (f i)))| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ β ^ 2 * ∑ i, B * (K : ℝ) ^ 2 * (Nat.dist l.val k.val : ℝ) * wt i *
          (min (min (l.val + 1) ((n : ℕ) - l.val))
            (min (k.val + 1) ((n : ℕ) - k.val)) : ℕ) ^ (-1 - s.val / 2) * ‖η‖ *
          ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖ := by
        gcongr with i
        exact (hest η (MatrixEnergy.vectorEquiv Q hQ p i).val
          (i.castLE hnm) (l.castLE hnm) (k.castLE hnm) i.isLt l.isLt k.isLt).2
      _ = _ := by simp only [wt, Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring


/-- See the proof of Proposition 5.15 in the paper, Schur contribution only: entry and increment
bounds for the literal `SchurRestriction.exteriorResponse`, whose equation is
proved rather than added as a source hypothesis. The field is identified a.e.
with the exact Schur row in `LocalizedBoundary.loc_boundary`. The endpoint source
sum is estimated on the whole scalar form domain. -/
theorem schur_response_bounds (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (hm : 2 ≤ (m : ℕ))
      (K : ℕ) (_hK : 1 ≤ K) (_hKm : K ≤ (m : ℕ) / 4),
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    ∀ (Cstar κ γ ε : ℝ) (hCstar : 1 ≤ Cstar)
      (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
      (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κ γ ε M)
      (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ),
    let w := SchurRestriction.exteriorResponse Q hQ n m hnm s hm K Cstar κ γ ε
      β hCstar hβ M hM p
    let field := fun l : Fin (n : ℕ) => β • referenceRow Q hQ s n m hm K
      (exteriorReindex Q hQ n m hnm w) (l.castLE hnm)
    let mass := (n : ℝ) ^ ((1 - s.val) / 2) *
      Real.sqrt (∑ i, ‖(MatrixEnergy.vectorEquiv Q hQ p i).val‖ ^ 2)
    (∀ l, (field l : Lp ℝ 2 ν) =ᵐ[ν] fun x =>
      ∑ i, (MatrixEnergy.vectorEquiv Q hQ
        (SchurRestriction.assemble Q hQ n m hnm (0, w)) i).val x *
          (β * M x i (l.castLE hnm))) ∧
    (∀ l, ‖field l‖ ≤ C * (K : ℝ) ^ 2 *
      (min (l.val + 1) ((n : ℕ) - l.val) : ℕ) ^ (-s.val / 2) * mass) ∧
    (∀ l k, ‖field l - field k‖ ≤ C * (K : ℝ) ^ 2 * (Nat.dist l.val k.val : ℝ) *
      (min (min (l.val + 1) ((n : ℕ) - l.val))
        (min (k.val + 1) ((n : ℕ) - k.val)) : ℕ) ^ (-1 - s.val / 2) * mass) := by
  obtain ⟨B, hB, hmain⟩ := normalized_schur_bounds_internal hzeta s β hβ
  refine ⟨B * Real.sqrt (2 / (1 - s.val)), by
    exact mul_pos hB (Real.sqrt_pos.mpr (div_pos (by norm_num) (sub_pos.mpr s.property.2))), ?_⟩
  intro n m hnm hm K hK hKm Ω _ ν Q hQ Cstar κ γ ε hCstar M hM p
  dsimp only
  let w := SchurRestriction.exteriorResponse Q hQ n m hnm s hm K Cstar κ γ ε
    β hCstar hβ M hM p
  obtain ⟨hp, hi⟩ := hmain n m hnm hm K hK hKm ν Q hQ p w
    (SchurRestriction.exterior_resolvent_equation Q hQ n m hnm s hm K Cstar κ γ ε
      β hCstar hβ M hM p)
  have hw := LocalizedField.schur_source_weight_internal s n
    (fun i => (MatrixEnergy.vectorEquiv Q hQ p i).val)
  refine ⟨fun l => schur_row_ae_internal Q hQ s n m hnm hm K Cstar κ γ ε β M hM w l, ?_, ?_⟩
  · intro l
    calc
      _ ≤ _ := hp l
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  · intro l k
    calc
      _ ≤ _ := hi l k
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring

end Estimates
end Riesz2.LocalizedFieldPart3
