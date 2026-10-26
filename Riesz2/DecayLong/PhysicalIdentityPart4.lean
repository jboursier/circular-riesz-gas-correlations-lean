/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentityPart3
public import Riesz2.DecayLong.BoundarySchurBounds

/-!
# The physical exterior resolvent on the ambient Sobolev domain

The constant reference form can be realized directly over the physical
ambient measure. Its exterior inverse and coupling therefore use exactly
the scalar domain already used by the physical Hessian. This is the
nonlocal common-domain step in Subsection 5.1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalIdentity.Internal

/-- Integrate a pointwise matrix lower bound on the literal Sobolev product.
This does not require a bounded multiplication operator. -/
theorem matrix_pair_lower {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ν : Measure α} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ) (a : ℝ)
    (hl : ∀ᵐ x ∂ν, ∀ t : ι → ℝ,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ)
    (hi : Integrable (matrixFieldPair M
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)) ν) :
    a * ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 ≤
      ∫ x, matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val) x ∂ν := by
  have hm : ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 =
      ∫ x, ∑ i, ((MatrixEnergy.vectorEquiv Q hQ u i).val x) ^ 2 ∂ν := by
    rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [OperatorSchur.vectorValues_apply, ← real_inner_self_eq_norm_sq, L2.inner_def]
      exact integral_congr_ae (Eventually.of_forall (fun _ => by
        dsimp only; rw [Real.inner_apply, sq]))
    · exact fun i _ => (Lp.memLp (MatrixEnergy.vectorEquiv Q hQ u i).val).integrable_sq
  rw [hm, ← integral_const_mul]
  have hi' := (integrable_finsetSum Finset.univ (fun i _ =>
    (Lp.memLp (MatrixEnergy.vectorEquiv Q hQ u i).val).integrable_sq)).const_mul a
  exact integral_mono_ae hi' hi (hl.mono (fun _ hx => hx _))

/-- Preserve the diffusion coefficient when passing from the mass bound to
coercivity in the graph norm. -/
theorem graph_form_coercive {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ν : Measure α} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (A : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ) (a : ℝ)
    (henergy : ∀ u, a * ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 +
      OperatorSchur.vectorEnergy Q hQ u u ≤ A u u)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    min 1 a * ‖u‖ ^ 2 ≤ A u u := by
  rw [OperatorSchur.vector_norm_sq Q hQ, mul_add]
  apply (add_le_add
    (mul_le_mul_of_nonneg_right (min_le_right 1 a)
      (sq_nonneg ‖OperatorSchur.vectorValues Q hQ u‖))
    (mul_le_mul_of_nonneg_right (min_le_left 1 a)
      (OperatorSchur.vectorEnergy_nonneg Q hQ u))).trans
  simpa only [one_mul] using henergy u

/-- Internal assembly on one complete domain: a continuous physical
multiplication pairing and its pointwise lower bound give physical
solvability and the comparison estimate for any proved form decomposition. -/
theorem form_source_comparison {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ν : Measure α} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ)
    (H : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ)
    (hH : ∀ u v, Integrable (matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ν ∧
      H u v = ∫ x, matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) x ∂ν)
    (a : ℝ) (ha : 0 < a)
    (hl : ∀ᵐ x ∂ν, ∀ t : ι → ℝ,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (S T : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ)
    (he : OperatorSchur.vectorEnergy Q hQ + H = S + T) :
    let A := OperatorSchur.vectorEnergy Q hQ + H
    (∀ f : PiLp 2 (fun _ : ι => Lp ℝ 2 ν),
      ∃! ψ, ∀ z, A ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) ∧
    ∀ (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)) (v ψ),
      (∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
      (∀ z, A ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
      (∀ z, A (v - ψ) z = T v z) ∧
        a * ‖OperatorSchur.vectorValues Q hQ (v - ψ)‖ ^ 2 +
          OperatorSchur.vectorEnergy Q hQ (v - ψ) (v - ψ) ≤ T v (v - ψ) := by
  intro A
  have henergy (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
      a * ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 +
        OperatorSchur.vectorEnergy Q hQ u u ≤ A u u := by
    have h := matrix_pair_lower Q hQ M a hl u (hH u u).1
    change _ ≤ OperatorSchur.vectorEnergy Q hQ u u + H u u
    rw [(hH u u).2]
    linarith only [h]
  have hcoer (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
      min 1 a * ‖u‖ ^ 2 ≤ A u u := graph_form_coercive Q hQ A a henergy u
  constructor
  · intro f
    have hex := CoerciveSolution.inverse_existsUnique A (min 1 a)
      (lt_min zero_lt_one ha) hcoer
      (CoerciveSolution.forcing (OperatorSchur.vectorValues Q hQ) f)
    simpa only [CoerciveSolution.forcing_apply] using hex
  · intro f v ψ hv hψ
    let f' := CoerciveSolution.forcing (OperatorSchur.vectorValues Q hQ) f
    exact ⟨comparison_equation A S T he f' v ψ hv hψ,
      comparison_energy A S T he f' v ψ hv hψ _ henergy⟩

/-- The literal truncated reference form is coercive on the existing scalar
Sobolev product, independently of the coefficient field of the physical core.
This constructs a reference realization over the ambient physical measure,
without transferring the scalar generator to the open-carrier subtype. -/
theorem reference_form {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4) :
    ∃ F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ,
      ∃ c : ℝ, 0 < c ∧
        (∀ u v, F u v = F v u) ∧
        (∀ u, c * ‖u‖ ^ 2 ≤ F u u) ∧
        ∀ u v,
          let P := matrixFieldPair
            (fun _ : α => (2 : ℝ) • referenceIntervalMatrix s M hM K)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)
          Integrable P ν ∧ F u v = OperatorSchur.vectorEnergy Q hQ u v +
            β.val * ∫ x, P x ∂ν := by
  obtain ⟨a, ha, href⟩ := referenceIntervalMatrix_truncated_coercivity s
  let H := (2 : ℝ) • referenceIntervalMatrix s M hM K
  let b := 2 * (a * (K : ℝ) ^ (-1 - s.val))
  have hb : 0 < b := by
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    dsimp only [b]
    positivity
  have hH : H.PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp (href M hM K hK hKM).1).smul
      (by norm_num : (0 : ℝ) ≤ 2)
  have hlow : b • (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤ H := by
    simpa only [b, H, smul_smul] using
      smul_le_smul_of_nonneg_left (href M hM K hK hKM).2.2 (by norm_num : (0 : ℝ) ≤ 2)
  have hl := (FiniteMatrixOrder.smul_one_le_iff hH.isHermitian b).mp hlow
  have hl' : ∀ᵐ x ∂ν, ∀ t : Fin (M : ℕ) → ℝ,
      (β.val * b) * (∑ i, t i ^ 2) ≤
        ∑ i, ∑ j, t i * (β.val • H) i j * t j := by
    apply Eventually.of_forall
    intro x t
    have h := mul_le_mul_of_nonneg_left (hl t) β.property.le
    simpa only [Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, sq] using h
  let F := BoundedMatrixForms.form Q hQ (fun _ : α => β.val • H)
    (fun _ _ => measurable_const) (BoundarySchurBounds.constant_bounded _)
    (Eventually.of_forall (fun _ => hH.smul β.property.le))
  refine ⟨F, min 1 (β.val * b), lt_min zero_lt_one (mul_pos β.property hb),
    BoundedMatrixForms.form_symmetric _ _ _ _ _ _,
    BoundedMatrixForms.form_coercive _ _ _ _ _ _ _ hl', fun u v => ?_⟩
  have hi := BoundedMatrixForms.integrable_pair (fun _ : α => H)
    (fun _ _ => measurable_const) (BoundarySchurBounds.constant_bounded H)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)
  refine ⟨hi, ?_⟩
  rw [BoundedMatrixForms.form_apply, ← OperatorSchur.vectorEnergy_apply,
    SchurRestriction.integral_pair_smul]

end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalIdentity

/-- See Subsection 5.1 of the paper (exterior form domain): the
reference exterior equation is solved on the same ambient scalar form domain
as the physical Hessian. The response is `R_D C`, as verified by its equation
with diffusion coefficient `β⁻¹`. The Schur correction has the literal
reference coupling pairing, is symmetric, and is nonnegative. -/
theorem reference_exterior_resolvent {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ)) (hM : 2 ≤ (M : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4) :
    ∃ R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin ((M : ℕ) - (n : ℕ))) Q hQ,
      ∃ G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
          MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ,
        (∀ u v, G u v = G v u) ∧ (∀ u, 0 ≤ G u u) ∧
        (∀ u w,
          let P := fun z z' => matrixFieldPair
            (fun _ : α => (2 : ℝ) • referenceIntervalMatrix s M hM K)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ
              (SchurRestriction.assemble Q hQ n M hnM z) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ
              (SchurRestriction.assemble Q hQ n M hnM z') i).val)
          Integrable (P (0, R u) (0, w)) ν ∧
          Integrable (P (u, 0) (0, w)) ν ∧
          β.val⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
            (∫ x, P (0, R u) (0, w) x ∂ν) =
            ∫ x, P (u, 0) (0, w) x ∂ν) ∧
        ∀ u v,
          let P := matrixFieldPair
            (fun _ : α => (2 : ℝ) • referenceIntervalMatrix s M hM K)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ
              (SchurRestriction.assemble Q hQ n M hnM (v, 0)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ
              (SchurRestriction.assemble Q hQ n M hnM (0, R u)) i).val)
          Integrable P ν ∧ G u v = β.val * ∫ x, P x ∂ν := by
  obtain ⟨F, c, hc, hs, hl, hF⟩ := Internal.reference_form Q hQ β s M hM K hK hKM
  let k := (M : ℕ) - (n : ℕ)
  let F' := F.bilinearComp
    (SchurRestriction.castIso Q hQ n M hnM).toContinuousLinearEquiv.toContinuousLinearMap
    (SchurRestriction.castIso Q hQ n M hnM).toContinuousLinearEquiv.toContinuousLinearMap
  have hF' (u : MatrixEnergy.Vector (ι := Fin ((n : ℕ) + k)) Q hQ) :
      c * ‖u‖ ^ 2 ≤ F' u u := by
    simpa only [F', ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map] using
      hl (SchurRestriction.castIso Q hQ n M hnM u)
  let E := SchurRestriction.exteriorForm Q hQ n k F'
  let C := SchurRestriction.cross Q hQ n k F'
  have hE : ∀ w, c * ‖w‖ ^ 2 ≤ E w w :=
    SchurRestriction.exterior_coercive Q hQ n k F' c hF'
  have hEs (z w) : E z w = E w z := hs _ _
  let R := OperatorSchur.exterior E C c hc hE
  let G := C.flip.comp R
  have hR (u w) : E (R u) w = C u w := OperatorSchur.exterior_solves E C c hc hE u w
  have hEc (z w : MatrixEnergy.Vector (ι := Fin k) Q hQ) :
      E z w = OperatorSchur.vectorEnergy Q hQ z w + β.val *
        ∫ x, matrixFieldPair
          (fun _ : α => (2 : ℝ) • referenceIntervalMatrix s M hM K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ
            (SchurRestriction.assemble Q hQ n M hnM (0, z)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ
            (SchurRestriction.assemble Q hQ n M hnM (0, w)) i).val) x ∂ν := by
    change F (SchurRestriction.assemble Q hQ n M hnM (0, z))
      (SchurRestriction.assemble Q hQ n M hnM (0, w)) = _
    rw [(hF _ _).2, OperatorSchur.vectorEnergy_apply, SchurRestriction.assemble_energy]
    simp only [map_zero, Pi.zero_apply, Finset.sum_const_zero, zero_add]
    rw [OperatorSchur.vectorEnergy_apply]
  have hCc (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
      (w : MatrixEnergy.Vector (ι := Fin k) Q hQ) :
      C u w = β.val *
        ∫ x, matrixFieldPair
          (fun _ : α => (2 : ℝ) • referenceIntervalMatrix s M hM K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ
            (SchurRestriction.assemble Q hQ n M hnM (u, 0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ
            (SchurRestriction.assemble Q hQ n M hnM (0, w)) i).val) x ∂ν := by
    change F (SchurRestriction.assemble Q hQ n M hnM (u, 0))
      (SchurRestriction.assemble Q hQ n M hnM (0, w)) = _
    rw [(hF _ _).2, OperatorSchur.vectorEnergy_apply, SchurRestriction.assemble_energy]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, Finset.sum_const_zero,
      zero_add, add_zero]
  refine ⟨R, G, ?_, ?_, ?_, ?_⟩
  · intro u v
    change C v (R u) = C u (R v)
    rw [← hR v (R u), ← hR u (R v), hEs]
  · intro u
    change 0 ≤ C u (R u)
    rw [← hR u (R u)]
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hE _)
  · intro u w P
    refine ⟨(hF _ _).1, (hF _ _).1, ?_⟩
    have he := hR u w
    rw [hEc, hCc] at he
    have he' := congrArg (fun t : ℝ => β.val⁻¹ * t) he
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ β.property.ne', one_mul, P] using he'
  · intro u v P
    exact ⟨(hF _ _).1, hCc v (R u)⟩

end Riesz2.PhysicalIdentity

namespace Riesz2.PhysicalIdentity

/-- See Subsection 5.1 of the paper (proper-marginal form identity and energy): the
actual physical and auxiliary forms share the original ambient Sobolev
domain. The Schur correction uses the literal reference exterior response.
The signed multiplication part is combined before integration. The physical
equation has a unique solution for every L² source. Whenever the auxiliary
equation is solved, subtraction has the source sign and the physical energy
bound with exponent `s+2`, independent of temperature and total volume.
-/
theorem proper_schur_comparison (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ν := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    let a := min 1 (s.val * (s.val + 1)) * (n : ℝ) ^ (-(s.val + 2) * ε)
    0 < a ∧
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
      ∃ hQ : IsClosedScalarDirichletForm Q,
        (∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
          WeightedFormDomain Q (hessianMatrix V) S u ↔
            ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ S) ∧
        ∃ (A S T G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
          (R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin ((M : ℕ) - (n : ℕ))) Q hQ),
          A = S + T ∧
          (∀ u v, G u v = G v u) ∧ (∀ u, 0 ≤ G u u) ∧
          (∀ u w,
            let P := fun z z' => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) =>
                (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ
                (SchurRestriction.assemble Q hQ n M hnM z) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ
                (SchurRestriction.assemble Q hQ n M hnM z') i).val)
            Integrable (P (0, R u) (0, w)) ν ∧ Integrable (P (u, 0) (0, w)) ν ∧
            β.val⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
              (∫ x, P (0, R u) (0, w) x ∂ν) = ∫ x, P (u, 0) (0, w) x ∂ν) ∧
          (∀ u v,
            let U := fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val
            let W := fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val
            let A₀ := PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀
            let P := fun x : Ω => ∑ i, ∑ j, U i x.val * A₀ x i j * W j x.val
            let D := fun x : Ω => ∑ i, ∑ j,
              U i x.val * (hessianMatrix V x.val i j - β.val * A₀ x i j) * W j x.val
            let C := matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) =>
                (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ
                (SchurRestriction.assemble Q hQ n M hnM (v, 0)) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ
                (SchurRestriction.assemble Q hQ n M hnM (0, R u)) i).val)
            Integrable (matrixFieldPair (hessianMatrix V) U W) ν ∧
            A u v = OperatorSchur.vectorEnergy Q hQ u v +
              ∫ x, matrixFieldPair (hessianMatrix V) U W x ∂ν ∧
            Integrable P μ ∧
            S u v = OperatorSchur.vectorEnergy Q hQ u v + β.val * (∫ x, P x ∂μ) - G u v ∧
            Integrable D μ ∧ T u v = (∫ x, D x ∂μ) + G u v ∧
            Integrable C ν ∧ G u v = β.val * ∫ x, C x ∂ν) ∧
          (∀ f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν),
            ∃! ψ, ∀ z, A ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) ∧
          ∀ (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν)) (v ψ),
            (∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
            (∀ z, A ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
            (∀ z, A (v - ψ) z = T v z) ∧
              β.val * a * ‖OperatorSchur.vectorValues Q hQ (v - ψ)‖ ^ 2 +
                OperatorSchur.vectorEnergy Q hQ (v - ψ) (v - ψ) ≤ T v (v - ψ) := by
  intro p hn ν Ω μ V a
  have ha : 0 < a := mul_pos
    (lt_min zero_lt_one (mul_pos s.property.1 (by linarith [s.property.1])))
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  refine ⟨ha, ?_⟩
  obtain ⟨Q, hreal, hQ, hdom, H, hH, hcore⟩ := proper_core_forms β s n m θ ε κ₀
  obtain ⟨B, D, he, hBD⟩ := hcore M hM hnM K
  obtain ⟨R, G, hGs, hG0, hR, hG⟩ := reference_exterior_resolvent Q hQ β s n M hnM hM K hK hKM
  let A := OperatorSchur.vectorEnergy Q hQ + H
  let S := OperatorSchur.vectorEnergy Q hQ + β.val • B - G
  let T := D + G
  have hident : A = S + T := by dsimp only [A, S, T]; rw [he]; abel
  have hlo : ∀ᵐ x ∂ν, ∀ t : Fin (n : ℕ) → ℝ,
      (β.val * a) * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * hessianMatrix V x i j * t j := by
    have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
    filter_upwards [IntrinsicScalarCore.supported (AffineSimplex.isOpen_chartDomain n _) hpot] with x hx
    intro t
    have hsmooth := hpot.1.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)
    have h := (proper_scaled_curvature β s n m θ ε hε).2 x hx (WithLp.toLp 2 t)
    rw [← PhysicalEnergy.hessianMatrix_quadratic (hsmooth.of_le (by norm_num)),
      EuclideanSpace.real_norm_sq_eq] at h
    convert h using 1 <;> dsimp only [a, V, p, ofLong]
    ring
  have hsolve := Internal.form_source_comparison Q hQ (hessianMatrix V) H hH
    (β.val * a) (mul_pos β.property ha) hlo S T hident
  refine ⟨Q, hreal, hQ, hdom, A, S, T, G, R, hident, hGs, hG0, hR, ?_, hsolve.1, hsolve.2⟩
  · intro u v U W A₀ P D' C
    obtain ⟨hPi, hBi, hDi, hD⟩ := hBD u v
    obtain ⟨hCi, hGi⟩ := hG u v
    refine ⟨(hH u v).1, ?_, hPi, ?_, hDi, ?_, hCi, hGi⟩
    · change OperatorSchur.vectorEnergy Q hQ u v + H u v = _
      rw [(hH u v).2]
    · change OperatorSchur.vectorEnergy Q hQ u v + β.val * B u v - G u v = _
      rw [hBi]
    · change D u v + G u v = _
      rw [hD]

end Riesz2.PhysicalIdentity
