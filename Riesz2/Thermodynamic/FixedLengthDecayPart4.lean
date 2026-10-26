/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart3

/-!
# Fixed-length comparison: identification of the two Schur forms

The exterior component relabelling preserves the full scalar form domain. These internal
bridges support Subsection 6.1 and Lemma 6.4.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical MatrixOrder

namespace Riesz2.FixedLengthDecay

/-- See Subsection 6.1 of the paper: split a finite sum at the active boundary. -/
theorem sum_components_internal {G : Type*} [AddCommMonoid G]
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (f : Fin (m : ℕ) → G) :
    ∑ i, f i = (∑ i : Fin (n : ℕ), f (i.castLE hnm)) +
      ∑ i : Fin ((m : ℕ) - (n : ℕ)), f (exteriorIndexEquiv_internal n m i).val := by
  have h := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hnm))
    (fun i => f (Fin.cast (Nat.add_sub_of_le hnm) i)) f (fun _ => rfl)
  rw [← h, Fin.sum_univ_add]
  rfl

section Assembly

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))

local notation "V" => MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ
local notation "W" => MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ
local notation "J" => OperatorSchur.vectorValues Q hQ
local notation "e" => exteriorIndexEquiv_internal n m
local notation "assemble" => SchurRestriction.assemble Q hQ n m hnm

/-- See Subsection 6.1 of the paper: the assembled field has exactly its original active values. -/
theorem assemble_left_values_internal (u : V) (z : W) (i : Fin (n : ℕ)) :
    J (assemble (u,z)) (i.castLE hnm) = J u i := by
  change (ScalarFormHilbert.equiv Q hQ (assemble (u,z) (i.castLE hnm))).val = _
  rw [SchurRestriction.assemble_left_apply]
  rfl

/-- See Subsection 6.1 of the paper: the assembled field has exactly its original exterior values. -/
theorem assemble_right_values_internal (u : V) (z : W)
    (i : Fin ((m : ℕ) - (n : ℕ))) : J (assemble (u,z)) (e i).val = J z i := by
  change (ScalarFormHilbert.equiv Q hQ (assemble (u,z) (e i).val)).val = _
  rw [assemble_right_apply_internal]
  rfl

/-- See Subsection 6.1 of the paper: active zero extensions restrict a matrix pairing to
its active principal block, with equality of actual integrands almost everywhere. -/
theorem assembled_active_pair_internal
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (u v : V) :
    matrixFieldPair M (J (assemble (u,0))).ofLp (J (assemble (v,0))).ofLp =ᵐ[ν]
      matrixFieldPair (fun x => (M x).submatrix (Fin.castLE hnm) (Fin.castLE hnm))
        (J u).ofLp (J v).ofLp := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  unfold matrixFieldPair
  rw [sum_components_internal n m hnm]
  simp_rw [sum_components_internal n m hnm]
  simp only [Matrix.submatrix_apply, assemble_left_values_internal,
    assemble_right_values_internal, map_zero, PiLp.zero_apply, hx,
    Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

/-- See Subsection 6.1 of the paper: exterior zero extensions restrict a matrix pairing
to the original exterior block. -/
theorem assembled_exterior_pair_internal
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (z w : W) :
    matrixFieldPair M (J (assemble (0,z))).ofLp (J (assemble (0,w))).ofLp =ᵐ[ν]
      matrixFieldPair (fun x => (M x).submatrix (fun i => (e i).val) (fun i => (e i).val))
        (J z).ofLp (J w).ofLp := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  unfold matrixFieldPair
  rw [sum_components_internal n m hnm]
  simp_rw [sum_components_internal n m hnm]
  simp only [Matrix.submatrix_apply, assemble_left_values_internal,
    assemble_right_values_internal, map_zero, PiLp.zero_apply, hx,
    Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]

/-- See Subsection 6.1 of the paper: the off-diagonal pairing is the actual active to
exterior block, including its sign and normalization. -/
theorem assembled_cross_pair_internal
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (u : V) (z : W) :
    matrixFieldPair M (J (assemble (u,0))).ofLp (J (assemble (0,z))).ofLp =ᵐ[ν]
      (fun x => ∑ i : Fin (n : ℕ), ∑ j : Fin ((m : ℕ) - (n : ℕ)),
        (J u i x) * M x (i.castLE hnm) (e j).val * J z j x) := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  unfold matrixFieldPair
  rw [sum_components_internal n m hnm]
  simp_rw [sum_components_internal n m hnm]
  simp only [assemble_left_values_internal, assemble_right_values_internal,
    map_zero, PiLp.zero_apply, hx, Pi.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]

end Assembly

section SchurCongruence

variable {U W Z : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

/-- See Subsection 6.1 of the paper: uniqueness of the full-domain exterior inverse
makes Schur reduction invariant under an exterior form-domain equivalence.
The two coercivity witnesses may be different. -/
theorem reduced_congr_internal
    (A : U →L[ℝ] U →L[ℝ] ℝ)
    (D : W →L[ℝ] W →L[ℝ] ℝ) (D' : Z →L[ℝ] Z →L[ℝ] ℝ)
    (C : U →L[ℝ] W →L[ℝ] ℝ) (C' : U →L[ℝ] Z →L[ℝ] ℝ)
    (E : W ≃L[ℝ] Z)
    (hD : ∀ z w, D z w = D' (E z) (E w))
    (hC : ∀ u w, C u w = C' u (E w))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ w, a * ‖w‖ ^ 2 ≤ D w w)
    (hl' : ∀ z, b * ‖z‖ ^ 2 ≤ D' z z) :
    OperatorSchur.reduced A D C a ha hl = OperatorSchur.reduced A D' C' b hb hl' := by
  have he (u : U) : E (OperatorSchur.exterior D C a ha hl u) =
      OperatorSchur.exterior D' C' b hb hl' u := by
    apply CoerciveSolution.inverse_unique D' b hb hl' (C' u)
    intro w
    have ht := OperatorSchur.exterior_solves D C a ha hl u (E.symm w)
    rw [hD, hC, E.apply_symm_apply] at ht
    exact ht
  ext u v
  rw [OperatorSchur.reduced_apply, OperatorSchur.reduced_apply, hC, he]

end SchurCongruence

section ExteriorIsometry

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+)

/-- See Subsection 6.1 of the paper: relabel the exterior Sobolev product by the canonical
exterior index equivalence, preserving its whole norm and scalar domain. -/
def exteriorFormIso_internal :
    MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ ≃ₗᵢ[ℝ]
      MatrixEnergy.Vector (ι := InterpolationMatrix.exteriorIndices m n) Q hQ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (ScalarFormHilbert.Space Q hQ)
    (exteriorIndexEquiv_internal n m)

/-- See Subsection 6.1 of the paper: evaluation of the exterior form-domain isometry. -/
theorem exteriorFormIso_apply_internal
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (i : Fin ((m : ℕ) - (n : ℕ))) :
    exteriorFormIso_internal Q hQ n m z (exteriorIndexEquiv_internal n m i) = z i := by
  simp [exteriorFormIso_internal, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- See Subsection 6.1 of the paper: scalar diffusion is unchanged by exterior relabelling. -/
theorem exterior_energy_reindex_internal
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    OperatorSchur.vectorEnergy Q hQ (exteriorFormIso_internal Q hQ n m z)
      (exteriorFormIso_internal Q hQ n m w) = OperatorSchur.vectorEnergy Q hQ z w := by
  rw [OperatorSchur.vectorEnergy_apply, OperatorSchur.vectorEnergy_apply]
  rw [← (exteriorIndexEquiv_internal n m).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  change Q.2 (ScalarFormHilbert.equiv Q hQ
    (exteriorFormIso_internal Q hQ n m z (exteriorIndexEquiv_internal n m i)))
    (ScalarFormHilbert.equiv Q hQ
    (exteriorFormIso_internal Q hQ n m w (exteriorIndexEquiv_internal n m i))) = _
  rw [exteriorFormIso_apply_internal, exteriorFormIso_apply_internal]
  rfl

/-- See Subsection 6.1 of the paper: matrix multiplication pairings use the same
exterior labels after the form-domain isometry. -/
theorem exterior_pair_reindex_internal
    (M : X → Matrix (InterpolationMatrix.exteriorIndices m n)
      (InterpolationMatrix.exteriorIndices m n) ℝ)
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    matrixFieldPair M
      (OperatorSchur.vectorValues Q hQ (exteriorFormIso_internal Q hQ n m z)).ofLp
      (OperatorSchur.vectorValues Q hQ (exteriorFormIso_internal Q hQ n m w)).ofLp =
    matrixFieldPair (fun x => (M x).submatrix (exteriorIndexEquiv_internal n m)
      (exteriorIndexEquiv_internal n m))
      (OperatorSchur.vectorValues Q hQ z).ofLp (OperatorSchur.vectorValues Q hQ w).ofLp := by
  funext x
  unfold matrixFieldPair
  rw [← (exteriorIndexEquiv_internal n m).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (exteriorIndexEquiv_internal n m).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  change (ScalarFormHilbert.equiv Q hQ
    (exteriorFormIso_internal Q hQ n m z (exteriorIndexEquiv_internal n m i))).val x * _ *
    (ScalarFormHilbert.equiv Q hQ
    (exteriorFormIso_internal Q hQ n m w (exteriorIndexEquiv_internal n m j))).val x = _
  rw [exteriorFormIso_apply_internal, exteriorFormIso_apply_internal]
  rfl

end ExteriorIsometry

section DiagonalBlocks

variable {X : Type} [MeasurableSpace X] {ν : Measure X}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
  (s : Riesz1.RieszExponent) (hm : 2 ≤ (m : ℕ)) (k : ℕ)
  (C κ γ ε : ℝ) (β : InverseTemperature) (hC : 1 ≤ C)
  (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
  (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ ε M)

local notation "F" => SchurRestriction.splitForm Q hQ n m hnm s hm k C κ γ ε
  β.val hC β.property M hM
local notation "A0" => fun x => Matrix.submatrix (β.val • M x) (Fin.castLE hnm) (Fin.castLE hnm)
local notation "E" => exteriorFormIso_internal Q hQ n m

/-- See Subsection 6.1 of the paper: the active diagonal is exactly the bounded
active matrix form, including the unchanged scalar diffusion. -/
theorem active_diagonal_identity_internal
    (hAm : ∀ i j, Measurable (fun x => A0 x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A0 x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A0 x).PosSemidef)
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    SchurRestriction.active Q hQ n ((m : ℕ) - (n : ℕ)) F u v =
      BoundedMatrixForms.form Q hQ A0 hAm hAb hA u v := by
  change BoundedMatrixForms.form Q hQ (fun x => β.val • M x) _ _ _
    (SchurRestriction.assemble Q hQ n m hnm (u,0))
    (SchurRestriction.assemble Q hQ n m hnm (v,0)) = _
  rw [BoundedMatrixForms.form_apply, SchurRestriction.assemble_energy,
    BoundedMatrixForms.form_apply]
  simp only [map_zero, Pi.zero_apply, Finset.sum_const_zero, add_zero]
  congr 1
  exact integral_congr_ae (assembled_active_pair_internal Q hQ n m hnm _ u v)

/-- See Subsection 6.1 of the paper: the exterior diagonal is the native reference
exterior form across the explicit exterior index isometry. -/
theorem exterior_diagonal_identity_internal (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    SchurRestriction.exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) F z w =
      InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n (E z) (E w) := by
  rw [SchurRestriction.exteriorForm_reference]
  unfold InterpolationMatrix.referenceExteriorForm BoundarySchurBounds.constantForm
  rw [BoundedMatrixForms.form_apply]
  rw [← OperatorSchur.vectorEnergy_apply, ← OperatorSchur.vectorEnergy_apply,
    exterior_energy_reindex_internal]
  congr 1
  change (∫ x, matrixFieldPair (fun _ => β.val • ((2 : ℝ) • referenceIntervalMatrix s m hm k))
    (OperatorSchur.vectorValues Q hQ (SchurRestriction.assemble Q hQ n m hnm (0,z))).ofLp
    (OperatorSchur.vectorValues Q hQ (SchurRestriction.assemble Q hQ n m hnm (0,w))).ofLp x ∂ν) =
    ∫ x, matrixFieldPair (fun _ => β.val • InterpolationMatrix.referenceExteriorMatrix s m hm k n)
      (OperatorSchur.vectorValues Q hQ (E z)).ofLp (OperatorSchur.vectorValues Q hQ (E w)).ofLp x ∂ν
  rw [exterior_pair_reindex_internal]
  exact integral_congr_ae (assembled_exterior_pair_internal Q hQ n m hnm _ z w)

/-- See Subsection 6.1 of the paper: integration of a finite constant rectangular
matrix pairing is its finite sum of L² inner products. -/
theorem rectangular_pair_integral_internal {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (D : ι → ι' → ℝ) (u : ι → Lp ℝ 2 ν) (z : ι' → Lp ℝ 2 ν) :
    (∫ x, ∑ i, ∑ j, u i x * D i j * z j x ∂ν) =
      ∑ i, ∑ j, D i j * inner ℝ (u i) (z j) := by
  have hi (i : ι) (j : ι') : Integrable (fun x => u i x * D i j * z j x) ν := by
    simpa only [Pi.mul_apply, mul_left_comm, mul_assoc] using
      ((Lp.memLp (u i)).integrable_mul (Lp.memLp (z j))).const_mul (D i j)
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

/-- See Subsection 6.1 of the paper: the off-diagonal block is the native reference
coupling, across the same exterior form-domain isometry. -/
theorem cross_coupling_identity_internal
    (T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : InterpolationMatrix.exteriorIndices m n => Lp ℝ 2 ν))
    (hT : ∀ f, T f = β.val • ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (f i))
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    SchurRestriction.cross Q hQ n ((m : ℕ) - (n : ℕ)) F u z =
      OperatorSchur.coupling (OperatorSchur.vectorValues Q hQ)
        (OperatorSchur.vectorValues Q hQ) T u (E z) := by
  rw [SchurRestriction.cross_reference]
  change (∫ x, matrixFieldPair (fun _ => β.val • ((2 : ℝ) • referenceIntervalMatrix s m hm k))
    (OperatorSchur.vectorValues Q hQ (SchurRestriction.assemble Q hQ n m hnm (u,0))).ofLp
    (OperatorSchur.vectorValues Q hQ (SchurRestriction.assemble Q hQ n m hnm (0,z))).ofLp x ∂ν) = _
  rw [integral_congr_ae (assembled_cross_pair_internal Q hQ n m hnm _ u z)]
  rw [rectangular_pair_integral_internal]
  rw [OperatorSchur.coupling_apply, hT, real_inner_smul_left, sum_inner]
  simp only [PiLp.inner_apply, BoundarySchurBounds.tensor,
    real_inner_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (exteriorIndexEquiv_internal n m).sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (β.val * (2 * referenceIntervalMatrix s m hm k
    (i.castLE hnm) (exteriorIndexEquiv_internal n m j).val)) * _ =
    β.val * (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)
      (exteriorIndexEquiv_internal n m j) *
      inner ℝ (OperatorSchur.vectorValues Q hQ u i)
        (ScalarFormHilbert.equiv Q hQ (E z (exteriorIndexEquiv_internal n m j))).val)
  rw [exteriorFormIso_apply_internal]
  simp only [InterpolationMatrix.referenceColumn, OperatorSchur.vectorValues_apply, mul_assoc]
  rfl

/-- See Subsection 6.1 of the paper: the two full-domain Schur forms are equal. This
identifies the active diagonal, exterior diagonal and coupling before applying
uniqueness. The native coercivity witness is arbitrary. -/
theorem schurForm_native_internal
    (hAm : ∀ i j, Measurable (fun x => A0 x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A0 x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A0 x).PosSemidef)
    (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
    (T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : InterpolationMatrix.exteriorIndices m n => Lp ℝ 2 ν))
    (hT : ∀ f, T f = β.val • ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (f i))
    (a : ℝ) (ha : 0 < a)
    (hD : ∀ w, a * ‖w‖ ^ 2 ≤
      InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n w w) :
    SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ ε β.val hC β.property M hM =
      OperatorSchur.reduced (BoundedMatrixForms.form Q hQ A0 hAm hAb hA)
        (InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n)
        (OperatorSchur.coupling (OperatorSchur.vectorValues Q hQ)
          (OperatorSchur.vectorValues Q hQ) T) a ha hD := by
  have hactive : SchurRestriction.active Q hQ n ((m : ℕ) - (n : ℕ)) F =
      BoundedMatrixForms.form Q hQ A0 hAm hAb hA := by
    ext u v
    exact active_diagonal_identity_internal Q hQ n m hnm s hm k C κ γ ε β hC M hM
      hAm hAb hA u v
  unfold SchurRestriction.schurForm
  dsimp only
  rw [hactive]
  apply reduced_congr_internal _ _ _ _ _ (E).toContinuousLinearEquiv
    (exterior_diagonal_identity_internal Q hQ n m hnm s hm k C κ γ ε β hC M hM hk hkm)
    (cross_coupling_identity_internal Q hQ n m hnm s hm k C κ γ ε β hC M hM T hT)

end DiagonalBlocks

section FixedExteriorIdentity

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε η t
local notation "A0" => fun x => β.val •
  InterpolationMatrix.activeBlock β s n d e hde m hm hnm k θ ε η t x

/-- See Subsection 6.1 of the paper, supporting Lemma 6.4: the precise form identity
needed to use the proof of Lemma 6.4 for the native physical comparison. It uses
the actual fixed-exterior matrix and its actual active block. -/
theorem fixed_exterior_schur_identity_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hAm : ∀ i j, Measurable (fun x => A0 x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A0 x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A0 x).PosSemidef)
    (T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : InterpolationMatrix.exteriorIndices m n => Lp ℝ 2 ν))
    (hT : ∀ f, T f = β.val • ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (f i))
    (a : ℝ) (ha : 0 < a)
    (hD : ∀ w, a * ‖w‖ ^ 2 ≤
      InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n w w) :
    SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ η β.val hC β.property M hM =
      OperatorSchur.reduced (BoundedMatrixForms.form Q hQ A0 hAm hAb hA)
        (InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n)
        (OperatorSchur.coupling (OperatorSchur.vectorValues Q hQ)
          (OperatorSchur.vectorValues Q hQ) T) a ha hD := by
  have he : (fun x => Matrix.submatrix (β.val • M x) (Fin.castLE hnm) (Fin.castLE hnm)) = A0 := by
    funext x
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, InterpolationMatrix.matrix_active]
  have hm' : ∀ i j, Measurable (fun x => (Matrix.submatrix (β.val • M x)
      (Fin.castLE hnm) (Fin.castLE hnm)) i j) := by
    simpa only [Matrix.submatrix_apply, Matrix.smul_apply, InterpolationMatrix.matrix_active] using hAm
  have hb' : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(Matrix.submatrix (β.val • M x)
      (Fin.castLE hnm) (Fin.castLE hnm)) i j| ≤ b := by
    simpa only [Matrix.submatrix_apply, Matrix.smul_apply, InterpolationMatrix.matrix_active] using hAb
  have hp' : ∀ᵐ x ∂ν, (Matrix.submatrix (β.val • M x)
      (Fin.castLE hnm) (Fin.castLE hnm)).PosSemidef := by
    filter_upwards [hA] with x hx
    rw [congrFun he x]
    exact hx
  simpa only [he] using schurForm_native_internal Q hQ n m hnm s hm k C κ γ η β hC M hM
    hm' hb' hp' hk hkm T hT a ha hD

variable (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "b" => MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
  (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤

/-- See Subsection 6.1 of the paper, supporting Lemma 6.4: the physical form minus
the Schur form actually used by the auxiliary-mean theorem equals the native
perturbation. The native inverse and all three active-form certificates are
constructed from the periodized-matrix conclusion. -/
theorem fixed_exterior_physical_comparison_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (u v : MatrixEnergy.Natural Q hQ H ⊤ hH) :
    let U := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH u i).val
    let V := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val
    ∃ hint : Integrable (matrixFieldPair Y U V) ν,
      MatrixEnergy.weakForm Q hQ H ⊤ hH u v -
        SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ η
          β.val hC β.property M hM (b u) (b v) =
      InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm
        θ ε η t ν Q hQ P U V hint := by
  intro U V
  obtain ⟨hAm,hAb,hA⟩ := active_form_data_internal β s n d e hde m hm hnm k
    θ ε η t ν C κ γ hC hM
  obtain ⟨T,hT⟩ := reference_coupling_map_internal ν s β n m hm hnm k
  let c := min 1 (β.val * (C⁻¹ * (n : ℝ) ^ (-κ * η)))
  have hc : 0 < c := SchurRestriction.coercivity_pos n C κ η β.val hC β.property
  let F := SchurRestriction.splitForm Q hQ n m hnm s hm k C κ γ η β.val hC β.property M hM
  have hDold := SchurRestriction.exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) F c
    (SchurRestriction.splitForm_coercive Q hQ n m hnm s hm k C κ γ η β.val hC β.property M hM)
  let E := exteriorFormIso_internal Q hQ n m
  have hD : ∀ w, c * ‖w‖ ^ 2 ≤
      InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n w w := by
    intro w
    have hh := hDold (E.symm w)
    rw [exterior_diagonal_identity_internal Q hQ n m hnm s hm k C κ γ η β hC M hM hk hkm] at hh
    simpa only [E, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using hh
  obtain ⟨hint,he⟩ := physical_schur_comparison_internal β s n d e hde m hm hnm k hk hkm
    θ ε η t ν Q hQ P hH hAm hAb hA T hT c hc hD u v
  refine ⟨hint, ?_⟩
  rw [fixed_exterior_schur_identity_internal β s n d e hde m hm hnm k hk hkm θ ε η t
    ν Q hQ C κ γ hC hM hAm hAb hA T hT c hc hD]
  exact he

end FixedExteriorIdentity

section SchurSymmetry

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
  (s : Riesz1.RieszExponent) (hm : 2 ≤ (m : ℕ)) (k : ℕ)
  (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
  (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
  (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ ε M)

/-- See Subsection 6.1 of the paper: symmetry of the actual auxiliary Schur form. -/
theorem schurForm_symmetric_internal
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ ε β hC hβ M hM u v =
      SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ ε β hC hβ M hM v u := by
  unfold SchurRestriction.schurForm
  dsimp only
  apply OperatorSchur.reduced_symmetric
  · intro u v
    exact BoundedMatrixForms.form_symmetric Q hQ (fun x => β • M x)
      (SchurRestriction.periodized_scaled_measurable β hM)
      (SchurRestriction.periodized_scaled_bounded β hM)
      (SchurRestriction.periodized_scaled_psd β hβ hC hM) _ _
  · intro z w
    exact BoundedMatrixForms.form_symmetric Q hQ (fun x => β • M x)
      (SchurRestriction.periodized_scaled_measurable β hM)
      (SchurRestriction.periodized_scaled_bounded β hM)
      (SchurRestriction.periodized_scaled_psd β hβ hC hM) _ _

end SchurSymmetry

section NaturalSchurTangent

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Lemma 6.4 of the paper: tangent subtraction for a symmetric auxiliary
Schur form on the original Sobolev product. This generic bridge keeps the
physical graph domain throughout. -/
theorem natural_schur_tangent_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (f : Fin (n : ℕ) → Lp ℝ 2 ν)
    (ψ v r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ))) f
      (MatrixEnergy.tuple Q hQ H ⊤ hH ψ))
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i =
      (n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH v j)
    (S : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (hS : ∀ u w, S u w = S w u)
    (L τ R : ℝ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hrenergy : MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤ R) :
    let base := MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
      (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤
    (∀ w : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      S (base v) w = inner ℝ (WithLp.toLp 2 f) (OperatorSchur.vectorValues Q hQ w)) →
    (|MatrixEnergy.weakForm Q hQ H ⊤ hH (v-r-ψ) v - S (base (v-r-ψ)) (base v)| ≤
      L*‖MatrixEnergy.values Q hQ H ⊤ hH (v-r-ψ)‖+τ) →
    ‖MatrixEnergy.values Q hQ H ⊤ hH (ψ-v)‖ ≤
      2*L/a + Real.sqrt ((2*τ+R)/a) + ‖MatrixEnergy.values Q hQ H ⊤ hH r‖ := by
  intro base haux hres
  let A := S.bilinearComp base base
  have hz : ∑ i, MatrixEnergy.tuple Q hQ H ⊤ hH (v-r) i = 0 := by
    simp only [map_sub, Pi.sub_apply, hr]
    exact subtract_mean_sum_zero Q n (MatrixEnergy.tuple Q hQ H ⊤ hH v)
  have haux' (w : MatrixEnergy.Natural Q hQ H ⊤ hH) :
      A v w = ∑ i, inner ℝ (f i) (MatrixEnergy.tuple Q hQ H ⊤ hH w i).val := by
    have hh := haux (base w)
    rw [PiLp.inner_apply] at hh
    exact hh
  have hp : |MatrixEnergy.weakForm Q hQ H ⊤ hH v (v-r-ψ) - A v (v-r-ψ)| ≤
      L*‖MatrixEnergy.values Q hQ H ⊤ hH (v-r-ψ)‖+τ := by
    rw [MatrixEnergy.weakForm_symm Q hQ H ⊤ hH (v-r-ψ) v, hS] at hres
    exact hres
  exact natural_tangent_comparison_internal Q hQ n H hH a ha hlower f ψ v r hψ hz
    A haux' L τ R hL hτ hR hp hrenergy

end NaturalSchurTangent

section TangentApplication

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε η t
local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "b" => MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
  (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤

/-- See Lemma 6.4 of the paper: apply the tangent comparison to the actual
`u = v - r - ψ`, with `r = (sum v)/n`. The auxiliary equation is precisely
that of the auxiliary-mean theorem. The remaining perturbation input is the
native bilinear pairing controlled by the column-cancellation theorem. -/
theorem fixed_exterior_tangent_comparison_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * H x i j * z j)
    (f : Fin (n : ℕ) → Lp ℝ 2 ν)
    (ψ v r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ))) f
      (MatrixEnergy.tuple Q hQ H ⊤ hH ψ))
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i =
      (n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH v j)
    (haux : ∀ w : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ η β.val hC β.property M hM
        (b v) w = inner ℝ (WithLp.toLp 2 f) (OperatorSchur.vectorValues Q hQ w))
    (L τ R : ℝ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hrenergy : MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤ R) :
    let u := v - r - ψ
    let U := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH u i).val
    let V := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val
    (∀ hint : Integrable (matrixFieldPair Y U V) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm
        θ ε η t ν Q hQ P U V hint| ≤ L * ‖WithLp.toLp 2 U‖ + τ) →
    ‖MatrixEnergy.values Q hQ H ⊤ hH (ψ - v)‖ ≤
      2 * L / a + Real.sqrt ((2 * τ + R) / a) +
        ‖MatrixEnergy.values Q hQ H ⊤ hH r‖ := by
  intro u U V hpert
  apply natural_schur_tangent_internal Q hQ n H hH a ha hlower f ψ v r hψ hr
    (SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ η β.val hC β.property M hM)
    (schurForm_symmetric_internal Q hQ n m hnm s hm k C κ γ η β.val hC β.property M hM)
    L τ R hL hτ hR hrenergy haux
  obtain ⟨hint,he⟩ := fixed_exterior_physical_comparison_internal β s n d e hde m hm hnm k
    hk hkm θ ε η t ν Q hQ P C κ γ hC hM hH u v
  have hh := (congrArg abs he).le.trans (hpert hint)
  have hU : WithLp.toLp 2 U = MatrixEnergy.values Q hQ H ⊤ hH u := by
    apply PiLp.ext
    intro i
    exact (MatrixEnergy.values_apply Q hQ H ⊤ hH u i).symm
  rw [hU] at hh
  exact hh

end TangentApplication

section RateComposition

/-- See Lemma 6.4 of the paper: absorb every polynomial exceptional factor and
then take the comparison square root. The constant precedes the size, source
norms and error. The loss exponent and tail power are preserved. -/
theorem error_rate_from_square_internal (A T q loss c δ : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x F B E : ℝ, 1 ≤ x → 0 ≤ F → 0 ≤ B → 0 ≤ E →
      E ^ 2 ≤ A * x ^ (2 * loss - 1) * F ^ 2 +
        T * x ^ q * Real.exp (-c * x ^ δ) * B ^ 2 →
      E ≤ D * x ^ (loss - 1 / 2) *
        (F + Real.exp (-(c / 4) * x ^ δ) * B) := by
  obtain ⟨K,hK,habs⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := q - (2 * loss - 1)) (c := c) (c' := c/2) hδ (by linarith)
  refine ⟨Real.sqrt A + Real.sqrt (T*K) + 1, by positivity, ?_⟩
  intro x F B E hx hF hB hE herror
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hpow : x ^ q = x ^ (2 * loss - 1) * x ^ (q - (2 * loss - 1)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hsquare : (x ^ (loss - 1 / 2)) ^ 2 = x ^ (2 * loss - 1) := by
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    norm_num
    ring
  have hexp : Real.exp (-(c/2) * x^δ) = (Real.exp (-(c/4) * x^δ)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have htail : T * x ^ q * Real.exp (-c * x^δ) * B^2 ≤
      T*K*x^(2*loss-1)*(Real.exp (-(c/4)*x^δ)*B)^2 := by
    have hh := mul_le_mul_of_nonneg_left (habs x hx)
      (show 0 ≤ T * x ^ (2*loss-1) * B^2 by positivity)
    rw [hexp] at hh
    calc
      _ = (T * x ^ (2*loss-1) * B^2) *
          (x^(q-(2*loss-1))*Real.exp (-c*x^δ)) := by rw [hpow]; ring
      _ ≤ _ := hh
      _ = _ := by ring
  have hbound : E^2 ≤ (Real.sqrt A * x^(loss-1/2)*F)^2 +
      (Real.sqrt (T*K)*x^(loss-1/2)*Real.exp (-(c/4)*x^δ)*B)^2 := by
    apply (herror.trans (add_le_add le_rfl htail)).trans_eq
    simp only [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt (mul_nonneg hT hK), hsquare]
    ring
  have he : E ≤ Real.sqrt A*x^(loss-1/2)*F +
      Real.sqrt (T*K)*x^(loss-1/2)*Real.exp (-(c/4)*x^δ)*B := by
    apply (sq_le_sq₀ hE (by positivity)).mp
    apply hbound.trans
    have hp : 0 ≤ (Real.sqrt A*x^(loss-1/2)*F) *
      (Real.sqrt (T*K)*x^(loss-1/2)*Real.exp (-(c/4)*x^δ)*B) := by positivity
    nlinarith only [hp]
  apply he.trans
  have h₁ : Real.sqrt A ≤ Real.sqrt A + Real.sqrt (T*K) + 1 := by linarith [Real.sqrt_nonneg (T*K)]
  have h₂ : Real.sqrt (T*K) ≤ Real.sqrt A + Real.sqrt (T*K) + 1 := by linarith [Real.sqrt_nonneg A]
  have hh₁ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ x^(loss-1/2)*F by positivity)
  have hh₂ := mul_le_mul_of_nonneg_right h₂
    (show 0 ≤ x^(loss-1/2)*Real.exp (-(c/4)*x^δ)*B by positivity)
  nlinarith only [hh₁,hh₂]

/-- See Lemma 6.4 of the paper: square the actual tangent-comparison bound
without discarding its normal correction or exceptional energy. -/
theorem comparison_square_internal (E L τ R a r : ℝ)
    (hE : 0 ≤ E) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (ha : 0 < a) (hr : 0 ≤ r)
    (hcomp : E ≤ 2*L/a + Real.sqrt ((2*τ+R)/a) + r) :
    E^2 ≤ 3 * ((2*L/a)^2 + (2*τ+R)/a + r^2) := by
  have hsq := (sq_le_sq₀ hE (by positivity)).mpr hcomp
  have hs := Real.sq_sqrt (show 0 ≤ (2*τ+R)/a by positivity)
  nlinarith only [hsq, hs, sq_nonneg (2*L/a - Real.sqrt ((2*τ+R)/a)),
    sq_nonneg (2*L/a-r), sq_nonneg (Real.sqrt ((2*τ+R)/a)-r)]

/-- See Lemma 6.4 of the paper: normalize the coercivity losses in the actual
comparison. The exceptional term retains its full polynomial factor. -/
theorem comparison_square_scaled_internal
    (x loss q c δ a0 L0 R0 T0 D0 F B E L τ R r : ℝ)
    (hx : 1 ≤ x) (hloss : 0 ≤ loss) (ha0 : 0 < a0)
    (hL0 : 0 ≤ L0) (hR0 : 0 ≤ R0) (hD0 : 0 ≤ D0)
    (hF : 0 ≤ F) (hE : 0 ≤ E)
    (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hLb : L ≤ L0*x^(loss-1/2)*F)
    (hτb : τ ≤ T0*x^q*Real.exp (-c*x^δ)*B^2)
    (hRb : R ≤ R0*x^(2*loss-1)*F^2 + T0*x^q*Real.exp (-c*x^δ)*B^2)
    (hrb : r ≤ D0*x^(loss-1/2)*F)
    (hcomp : E ≤ 2*L/(a0*x^(-loss)) +
      Real.sqrt ((2*τ+R)/(a0*x^(-loss))) + r) :
    E^2 ≤ (3*((2*L0/a0)^2+R0/a0+D0^2))*x^(4*loss-1)*F^2 +
      (9*T0/a0)*x^(q+loss)*Real.exp (-c*x^δ)*B^2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ha : 0 < a0*x^(-loss) := by positivity
  have hdiv (v : ℝ) : v/(a0*x^(-loss)) = (v/a0)*x^loss := by
    rw [Real.rpow_neg hx0.le]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hp (p : ℝ) : (x^p)^2 = x^(2*p) := by
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    norm_num
    ring
  have hl : (2*L/(a0*x^(-loss)))^2 ≤
      (2*L0/a0)^2*x^(4*loss-1)*F^2 := by
    have hh : 2*L/(a0*x^(-loss)) ≤ (2*L0/a0)*x^(2*loss-1/2)*F := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLb (by norm_num)) ha.le).trans_eq
      rw [hdiv, show 2*loss-1/2 = (loss-1/2)+loss by ring, Real.rpow_add hx0]
      ring
    have hh2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hh
    apply hh2.trans_eq
    simp only [mul_pow, hp]
    rw [show 2*(2*loss-1/2) = 4*loss-1 by ring]
  have henergy : (2*τ+R)/(a0*x^(-loss)) ≤
      (R0/a0)*x^(4*loss-1)*F^2 +
        (3*T0/a0)*x^(q+loss)*Real.exp (-c*x^δ)*B^2 := by
    have hh : 2*τ+R ≤ R0*x^(2*loss-1)*F^2 +
        3*T0*x^q*Real.exp (-c*x^δ)*B^2 := by linarith only [hτb,hRb]
    have heq : (R0*x^(2*loss-1)*F^2 + 3*T0*x^q*Real.exp (-c*x^δ)*B^2)/
        (a0*x^(-loss)) = (R0/a0)*x^(3*loss-1)*F^2 +
        (3*T0/a0)*x^(q+loss)*Real.exp (-c*x^δ)*B^2 := by
      rw [hdiv, Real.rpow_add hx0,
        show 3*loss-1 = (2*loss-1)+loss by ring, Real.rpow_add hx0]
      ring
    apply ((div_le_div_of_nonneg_right hh ha.le).trans_eq heq).trans
    apply add_le_add _ le_rfl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity)) (sq_nonneg F)
  have hr2 : r^2 ≤ D0^2*x^(4*loss-1)*F^2 := by
    have hh := (sq_le_sq₀ hr (by positivity)).mpr hrb
    apply hh.trans
    simp only [mul_pow, hp]
    rw [show 2*(loss-1/2) = 2*loss-1 by ring]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (sq_nonneg D0)) (sq_nonneg F)
  have hh := comparison_square_internal E L τ R (a0*x^(-loss)) r
    hE hL hτ hR ha hr hcomp
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hl henergy) hr2)
    (by norm_num : (0 : ℝ) ≤ 3)
  exact hb.trans_eq (by ring)

/-- See Lemma 6.4 of the paper: a single prefactor converts all physical
comparison bounds at once. With `loss = κ₀ ε`, the output degree is `2 κ₀`. The only exponential change is `c` to `c/4`, with the same tail power. -/
theorem comparison_rate_uniform_internal (loss q c δ a0 L0 R0 T0 D0 : ℝ)
    (hloss : 0 ≤ loss) (hc : 0 < c) (hδ : 0 < δ) (ha0 : 0 < a0)
    (hL0 : 0 ≤ L0) (hR0 : 0 ≤ R0) (hT0 : 0 ≤ T0) (hD0 : 0 ≤ D0) :
    ∃ D : ℝ, 0 < D ∧ ∀ x F B E L τ R r : ℝ,
      1 ≤ x → 0 ≤ F → 0 ≤ B → 0 ≤ E → 0 ≤ L → 0 ≤ τ → 0 ≤ R → 0 ≤ r →
      L ≤ L0*x^(loss-1/2)*F →
      τ ≤ T0*x^q*Real.exp (-c*x^δ)*B^2 →
      R ≤ R0*x^(2*loss-1)*F^2 + T0*x^q*Real.exp (-c*x^δ)*B^2 →
      r ≤ D0*x^(loss-1/2)*F →
      E ≤ 2*L/(a0*x^(-loss)) + Real.sqrt ((2*τ+R)/(a0*x^(-loss))) + r →
      E ≤ D*x^(2*loss-1/2)*(F+Real.exp (-(c/4)*x^δ)*B) := by
  let A := 3*((2*L0/a0)^2+R0/a0+D0^2)
  let T := 9*T0/a0
  obtain ⟨D,hD,hbound⟩ := error_rate_from_square_internal A T (q+loss) (2*loss) c δ
    (by dsimp only [A]; positivity) (by dsimp only [T]; positivity) hc hδ
  refine ⟨D,hD,?_⟩
  intro x F B E L τ R r hx hF hB hE hL hτ hR hr hLb hτb hRb hrb hcomp
  have hh := comparison_square_scaled_internal x loss q c δ a0 L0 R0 T0 D0 F B E L τ R r
    hx hloss ha0 hL0 hR0 hD0 hF hE hL hτ hR hr hLb hτb hRb hrb hcomp
  apply hbound x F B E hx hF hB hE
  simpa only [A,T,show 2*(2*loss)-1 = 4*loss-1 by ring] using hh

variable {H : Type*} [NormedAddCommGroup H]


/-- See Lemma 6.4 of the paper: long-range rate composition from the
auxiliary value profile and a squared vector comparison. Constants are uniform
in size and sources. Polynomial exceptional losses are absorbed once. -/
theorem long_rates_from_square_internal (s : Riesz1.RieszExponent)
    (D0 A T q loss c δ : ℝ) (hD0 : 0 ≤ D0)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (i₀ : Fin (n : ℕ)),
      |(i₀.val : ℝ) + 1 - (n : ℝ)/2| ≤ (n : ℝ)/4 →
      ∀ (F B : ℝ) (ψ v : Fin (n : ℕ) → H), 0 ≤ F → 0 ≤ B →
      (∀ j, ‖v j‖ ≤ D0*(n : ℝ)^loss *
        (1 + (Nat.dist j.val i₀.val : ℝ))^(s.val - 2)*F) →
      (∑ j, ‖v j‖) ≤ D0*(n : ℝ)^loss*F →
      ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
        A*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ)*B^2 →
      (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖ψ j‖) ≤
        C*(n : ℝ)^(loss-s.val/2)*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) ∧
      (∑ j, ‖ψ j‖) ≤ C*(n : ℝ)^loss*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) := by
  obtain ⟨E0,hE0,herr⟩ := error_rate_from_square_internal A T q loss c δ hA hT hc hδ
  let K : ℝ := 8 ^ (2 - s.val) * (2 / (1 - s.val / 2)) + 8 ^ (s.val / 2)
  let W : ℝ := 2 / (1 - s.val)
  let C := max (K*D0+Real.sqrt W*E0) (D0+E0) + 1
  have hC : 0 < C := by
    have := le_max_right (K*D0+Real.sqrt W*E0) (D0+E0)
    dsimp only [C]
    linarith
  have hw : K*D0+Real.sqrt W*E0 ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hu : D0+E0 ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C,hC,?_⟩
  intro n i₀ hi₀ F B ψ v hF hB hvalue hsum herror
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let G := F+Real.exp (-(c/4)*(n : ℝ)^δ)*B
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hFG : F ≤ G := le_add_of_nonneg_right (by positivity)
  have hErr := herr n F B ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ hn1 hF hB (norm_nonneg _) herror
  have hErr' : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ ≤
      (E0*(n : ℝ)^loss)*(n : ℝ)^(-(1 : ℝ)/2)*G := by
    apply hErr.trans_eq
    rw [show loss-1/2 = loss+(-(1 : ℝ)/2) by ring, Real.rpow_add hn]
    ring
  have hb := long_decay_sums_internal s n i₀ hi₀ (D0*(n : ℝ)^loss) (E0*(n : ℝ)^loss)
    F G (by positivity) (by positivity) hF hFG hG ψ v hvalue hsum hErr'
  constructor
  · calc
      _ ≤ _ := hb.1
      _ = (K*D0+Real.sqrt W*E0)*(n : ℝ)^(loss-s.val/2)*G := by
        rw [show loss-s.val/2 = loss+(-(s.val/2)) by ring, Real.rpow_add hn]
        dsimp only [K,W]
        simp only [neg_div]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (by positivity)) hG
  · calc
      _ ≤ _ := hb.2
      _ = (D0+E0)*(n : ℝ)^loss*G := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) hG

/-- See Lemma 6.4 of the paper: short-range rate composition from the
auxiliary value profile and a squared vector comparison. Constants are uniform
in size and sources. Polynomial exceptional losses are absorbed once. -/
theorem short_rates_from_square_internal (s : ℝ) (hs : 1 < s)
    (D0 A T q loss c δ : ℝ) (hD0 : 0 ≤ D0)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (i₀ : Fin (n : ℕ)),
      |(i₀.val : ℝ) + 1 - (n : ℝ)/2| ≤ (n : ℝ)/4 →
      ∀ (F B : ℝ) (ψ v : Fin (n : ℕ) → H), 0 ≤ F → 0 ≤ B →
      (∀ j, ‖v j‖ ≤ D0*(n : ℝ)^loss *
        (1 + (Nat.dist j.val i₀.val : ℝ))^(-s)*F) →
      (∑ j, ‖v j‖) ≤ D0*(n : ℝ)^loss*F →
      ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
        A*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ)*B^2 →
      (∑ j, InteractionDifferential.boundaryWeight s n j*‖ψ j‖) ≤
        C*(n : ℝ)^(loss-1/2)*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) ∧
      (∑ j, ‖ψ j‖) ≤ C*(n : ℝ)^loss*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) := by
  obtain ⟨E0,hE0,herr⟩ := error_rate_from_square_internal A T q loss c δ hA hT hc hδ
  let K : ℝ := 4 * 8 ^ s + Real.sqrt 8
  let W : ℝ := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2*s-1))
  let C := max (K*D0+Real.sqrt W*E0) (D0+E0) + 1
  have hC : 0 < C := by
    have := le_max_right (K*D0+Real.sqrt W*E0) (D0+E0)
    dsimp only [C]
    linarith
  have hw : K*D0+Real.sqrt W*E0 ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hu : D0+E0 ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C,hC,?_⟩
  intro n i₀ hi₀ F B ψ v hF hB hvalue hsum herror
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let G := F+Real.exp (-(c/4)*(n : ℝ)^δ)*B
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hFG : F ≤ G := le_add_of_nonneg_right (by positivity)
  have hErr := herr n F B ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ hn1 hF hB (norm_nonneg _) herror
  have hErr' : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ ≤
      (E0*(n : ℝ)^loss)*(n : ℝ)^(-(1 : ℝ)/2)*G := by
    apply hErr.trans_eq
    rw [show loss-1/2 = loss+(-(1 : ℝ)/2) by ring, Real.rpow_add hn]
    ring
  have hb := short_decay_sums_internal s hs n i₀ hi₀ (D0*(n : ℝ)^loss) (E0*(n : ℝ)^loss)
    F G (by positivity) (by positivity) hF hFG hG ψ v hvalue hsum hErr'
  constructor
  · calc
      _ ≤ _ := hb.1
      _ = (K*D0+Real.sqrt W*E0)*(n : ℝ)^(loss-1/2)*G := by
        rw [show loss-1/2 = loss+(-(1/2)) by ring, Real.rpow_add hn]
        dsimp only [K,W]
        simp only [neg_div]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (by positivity)) hG
  · calc
      _ ≤ _ := hb.2
      _ = (D0+E0)*(n : ℝ)^loss*G := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) hG

/-- See Lemma 6.4 of the paper: join the lower-curvature small-size
estimate with both large-size conclusions. A single positive prefactor works
for every size and source, retaining the chosen loss and tail exponents. -/
theorem all_size_join_internal (n0 κ0 κ ε q C0 Cbig c δ : ℝ)
    (hn0 : 0 ≤ n0) (hκ : κ0 ≤ κ) (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hC0 : 0 ≤ C0) (hCbig : 0 ≤ Cbig) :
    ∃ C : ℝ, 0 < C ∧ ∀ n F B weighted unweighted : ℝ,
      1 ≤ n → 0 ≤ F → 0 ≤ B →
      (n < n0 → weighted ≤ Real.sqrt n*(C0*n^(κ0*ε)*F) ∧
        unweighted ≤ Real.sqrt n*(C0*n^(κ0*ε)*F)) →
      (n0 ≤ n → weighted ≤ Cbig*n^(κ*ε-q)*(F+Real.exp (-c*n^δ)*B) ∧
        unweighted ≤ Cbig*n^(κ*ε)*(F+Real.exp (-c*n^δ)*B)) →
      weighted ≤ C*n^(κ*ε-q)*(F+Real.exp (-c*n^δ)*B) ∧
      unweighted ≤ C*n^(κ*ε)*(F+Real.exp (-c*n^δ)*B) := by
  let Csmall := C0 * (n0^(q+1/2) + n0^((1 : ℝ)/2))
  let C := Cbig + Csmall + 1
  have hsmall0 : 0 ≤ Csmall := by
    dsimp only [Csmall]
    exact mul_nonneg hC0 (add_nonneg (Real.rpow_nonneg hn0 _)
      (Real.rpow_nonneg hn0 _))
  have hbig : Cbig ≤ C := by dsimp only [C]; linarith
  have hw : C0*n0^(q+1/2) ≤ C := by
    dsimp only [C,Csmall]
    have : 0 ≤ C0*n0^((1 : ℝ)/2) := mul_nonneg hC0 (Real.rpow_nonneg hn0 _)
    nlinarith only [hCbig,this]
  have hu : C0*n0^((1 : ℝ)/2) ≤ C := by
    dsimp only [C,Csmall]
    have : 0 ≤ C0*n0^(q+1/2) := mul_nonneg hC0 (Real.rpow_nonneg hn0 _)
    nlinarith only [hCbig,this]
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro n F B weighted unweighted hn hF hB hsmall hlarge
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hG : 0 ≤ F+Real.exp (-c*n^δ)*B := by positivity
  have hp : κ0*ε ≤ κ*ε := mul_le_mul_of_nonneg_right hκ hε
  by_cases h : n0 ≤ n
  · obtain ⟨hw',hu'⟩ := hlarge h
    exact ⟨hw'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbig (by positivity)) hG),
      hu'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbig (by positivity)) hG)⟩
  · obtain ⟨hw',hu'⟩ := hsmall (lt_of_not_ge h)
    have hw'' := small_size_absorption_internal n n0 κ0 ε q C0 F B c δ weighted
      hn (le_of_not_ge h) hq hC0 hF hB hw'
    have hu'' := small_size_absorption_internal n n0 κ0 ε 0 C0 F B c δ unweighted
      hn (le_of_not_ge h) (by norm_num) hC0 hF hB hu'
    simp only [sub_zero, zero_add] at hu''
    constructor
    · apply hw''.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul hw
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
        (by positivity) (by dsimp only [C]; linarith)) hG
    · apply hu''.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul hu
        (Real.rpow_le_rpow_of_exponent_le hn hp)
        (by positivity) (by dsimp only [C]; linarith)) hG

end RateComposition

end Riesz2.FixedLengthDecay
