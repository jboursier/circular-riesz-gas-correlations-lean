/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentityPart6

/-!
# Full-cycle comparison on the zero-sum Sobolev space

Completes the full-cycle clause of Subsection 5.1, using the actual
physical Hessian, core and intrinsic scalar form.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalIdentity

namespace Internal

/-- Literal multiplication pairing on the existing scalar Sobolev product.
This predicate only abbreviates integrability and equality with the integral. -/
def MatrixPairing {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (H : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ) : Prop :=
  ∀ u v, Integrable (matrixFieldPair M
    (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ρ ∧
    H u v = ∫ z,matrixFieldPair M
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) z ∂ρ

/-- Certificate for the entire physical matrix domain on an existing measure.
The scalar realization, Hilbert product and matrix domain are those of the
physical equation. -/
def HasPhysicalForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (ρ : Measure E) (Ω : Set E) (N : ℕ+)
    (M : E → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) : Prop :=
  ∃ Q : ScalarFormData ρ, IsNeumannRealization Ω Q ∧
    ∃ hQ : IsClosedScalarDirichletForm Q,
      (∀ (W : Submodule ℝ (Fin (N : ℕ) → ℝ)) (u : Fin (N : ℕ) → Q.1),
        WeightedFormDomain Q M W u ↔ ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ W) ∧
      ∃ H, MatrixPairing Q hQ N M H

/-- Express the norm conversion before specializing the physical measure. -/
theorem vectorize_domain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {ρ : Measure E} (Ω : Set E) (N : ℕ+)
    (M : E → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (Q : ScalarFormData ρ) (hr : IsNeumannRealization Ω Q)
    (hQ : IsClosedScalarDirichletForm Q)
    (hd : ∀ (W : Submodule ℝ (Fin (N : ℕ) → ℝ)) (u : Fin (N : ℕ) → Q.1),
      WeightedFormDomain Q M W u ↔ ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ W)
    (H₀ : (Fin (N : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ]
      (Fin (N : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ)
    (hH₀ : ∀ u v : Fin (N : ℕ) → Q.1,
      Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val)) ρ ∧
      H₀ (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
        (fun i => (ScalarFormHilbert.equiv Q hQ).symm (v i)) =
          ∫ z,matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) z ∂ρ) :
    HasPhysicalForm ρ Ω N M := by
  exact ⟨Q,hr,hQ,hd,vectorize_form Q hQ N M H₀ hH₀⟩

end Internal

/-- See Subsection 5.1 of the paper: the physical multiplication form on the original
Hilbert product, with its entire finite-energy domain. -/
theorem full_physical_form (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y) ∧
      Internal.HasPhysicalForm (fullIntrinsicTiltedGapLaw (ofLong β s) N θ ε false)
        (intrinsicGapDomain N) N
        (fun z => hessianMatrix U (WithLp.toLp 2 (fun i => 1+z.val i))) := by
  obtain ⟨U,hU,hv,Q,hr,hQ,_,hd,H₀,hH₀⟩ :=
    PhysicalFormDomain.full_form_domain β s N hN θ ε
  exact ⟨U,hU,hv,Internal.vectorize_domain _ N _ Q hr hQ hd H₀ hH₀⟩

namespace Internal

/-- The common-domain comparison after restricting both forms to the same
closed zero-sum space. The forms are specified literally, including the
signed perturbation and the original diffusion coefficient. -/
def CompressedComparison {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (H B : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ) (β a : ℝ) : Prop :=
  let W := fullZeroSumSpace Q hQ N
  let A := (OperatorSchur.vectorEnergy Q hQ + H).bilinearComp W.subtypeL W.subtypeL
  let S := (OperatorSchur.vectorEnergy Q hQ + β • B).bilinearComp W.subtypeL W.subtypeL
  let T := (H - β • B).bilinearComp W.subtypeL W.subtypeL
  let J := (OperatorSchur.vectorValues Q hQ).comp W.subtypeL
  A = S + T ∧
    (∀ f : PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ρ),
      (∃! v, ∀ z, S v z = inner ℝ f (J z)) ∧
      (∃! ψ, ∀ z, A ψ z = inner ℝ f (J z))) ∧
    ∀ (f : PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ρ)) (v ψ : W),
      (∀ z, S v z = inner ℝ f (J z)) →
      (∀ z, A ψ z = inner ℝ f (J z)) →
      (∀ z, A (v-ψ) z = T v z) ∧
        β*a*‖J (v-ψ)‖^2 +
          OperatorSchur.vectorEnergy Q hQ (v-ψ).val (v-ψ).val ≤ T v (v-ψ)

/-- Generic same-space assembly. Analytic hypotheses occur only in this
internal lemma. The physical theorem below proves them for the actual law. -/
theorem compressed_comparison {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (M C : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (H B : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ)
    (hH : MatrixPairing Q hQ N M H) (hB : MatrixPairing Q hQ N C B)
    (β a b : ℝ) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ᵐ x ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      β*a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*M x i j*t j)
    (hc : ∀ᵐ x ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      b*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*C x i j*t j) :
    CompressedComparison Q hQ N H B β a := by
  let W := fullZeroSumSpace Q hQ N
  have : CompleteSpace W := (isClosed_fullZeroSumSpace Q hQ N).completeSpace_coe
  let E := OperatorSchur.vectorEnergy (ι := Fin (N : ℕ)) Q hQ
  let A₀ := E+H
  let S₀ := E+β • B
  have he (u : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :
      β*a*‖OperatorSchur.vectorValues Q hQ u‖^2 + E u u ≤ A₀ u u := by
    have hh := matrix_pair_lower Q hQ M (β*a) hl u (hH u u).1
    rw [← (hH u u).2] at hh
    change _ ≤ E u u + H u u
    linarith only [hh]
  have heS (u : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :
      (β*b)*‖OperatorSchur.vectorValues Q hQ u‖^2 + E u u ≤ S₀ u u := by
    have hh := matrix_pair_lower Q hQ C b hc u (hB u u).1
    rw [← (hB u u).2] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hβ.le
    change _ ≤ E u u + β*B u u
    nlinarith only [hh']
  let A := A₀.bilinearComp W.subtypeL W.subtypeL
  let S := S₀.bilinearComp W.subtypeL W.subtypeL
  let T := (H-β • B).bilinearComp W.subtypeL W.subtypeL
  let J := (OperatorSchur.vectorValues Q hQ).comp W.subtypeL
  have hA (u : W) : min 1 (β*a)*‖u‖^2 ≤ A u u :=
    graph_form_coercive Q hQ A₀ (β*a) he u.val
  have hS (u : W) : min 1 (β*b)*‖u‖^2 ≤ S u u :=
    graph_form_coercive Q hQ S₀ (β*b) heS u.val
  have hid : A = S+T := by
    ext u v
    change E u.val v.val + H u.val v.val =
      (E u.val v.val + β*B u.val v.val) + (H u.val v.val - β*B u.val v.val)
    ring
  refine ⟨hid,?_,?_⟩
  · intro f
    constructor
    · simpa only [CoerciveSolution.forcing_apply] using
        CoerciveSolution.inverse_existsUnique S (min 1 (β*b))
          (lt_min zero_lt_one (mul_pos hβ hb)) hS (CoerciveSolution.forcing J f)
    · simpa only [CoerciveSolution.forcing_apply] using
        CoerciveSolution.inverse_existsUnique A (min 1 (β*a))
          (lt_min zero_lt_one (mul_pos hβ ha)) hA (CoerciveSolution.forcing J f)
  · intro f v ψ hv hψ
    exact ⟨comparison_equation A S T hid (CoerciveSolution.forcing J f) v ψ hv hψ,
      comparison_energy A S T hid (CoerciveSolution.forcing J f) v ψ hv hψ
        (fun u : W => β*a*‖J u‖^2+E u.val u.val) (fun u => he u.val)⟩

/-- The literal combined signed coefficient is integrable before it is
split into any physical pieces. -/
theorem signed_pairing {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (M C : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (H B : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ)
    (hH : MatrixPairing Q hQ N M H) (hB : MatrixPairing Q hQ N C B) (β : ℝ) :
    MatrixPairing Q hQ N (fun x => M x - β • C x) (H-β • B) := by
  intro u v
  let U := fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val
  let V := fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val
  have he : matrixFieldPair (fun x => M x-β • C x) U V =
      fun x => matrixFieldPair M U V x - β*matrixFieldPair C U V x := by
    funext x
    simp only [matrixFieldPair,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨?_,?_⟩
  · rw [he]
    exact (hH u v).1.sub ((hB u v).1.const_mul β)
  · change H u v - β*B u v = _
    rw [(hH u v).2,(hB u v).2,he,integral_sub (hH u v).1 ((hB u v).1.const_mul β),
      integral_const_mul]

/-- Continuous matrix pairings put every constrained Sobolev tuple in the
finite-energy domain. -/
theorem domain_of_pairing {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (H : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ)
    (hH : MatrixPairing Q hQ N M H)
    (W : Submodule ℝ (Fin (N : ℕ) → ℝ)) (u : Fin (N : ℕ) → Q.1) :
    WeightedFormDomain Q M W u ↔ ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ W := by
  have hi := (hH ((MatrixEnergy.vectorEquiv Q hQ).symm u)
    ((MatrixEnergy.vectorEquiv Q hQ).symm u)).1
  rw [LinearEquiv.apply_symm_apply] at hi
  exact ⟨fun h => h.1,fun h => ⟨h,hi⟩⟩

/-- A compact statement of the complete comparison on the existing measure.
All matrices, forms and domains in this certificate are specified by their
definitions or integral pairings. -/
def CommonDomainComparison {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (ρ : Measure E) (Ω : Set E) (N : ℕ+)
    (M C : E → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) (β a : ℝ) : Prop :=
  ∃ Q : ScalarFormData ρ, IsNeumannRealization Ω Q ∧
    ∃ hQ : IsClosedScalarDirichletForm Q,
      (∀ (W : Submodule ℝ (Fin (N : ℕ) → ℝ)) (u : Fin (N : ℕ) → Q.1),
        (WeightedFormDomain Q M W u ↔ ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ W) ∧
        (WeightedFormDomain Q C W u ↔ ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ W)) ∧
      ∃ H B,
        MatrixPairing Q hQ N M H ∧ MatrixPairing Q hQ N C B ∧
        MatrixPairing Q hQ N (fun z => M z-β • C z) (H-β • B) ∧
        CompressedComparison Q hQ N H B β a

/-- Comparison for a general measure, before specialization to the physical law. -/
theorem common_domain_comparison {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {ρ : Measure E} (Ω : Set E) (N : ℕ+)
    (M C : E → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hphys : HasPhysicalForm ρ Ω N M)
    (hcore : ∀ (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q),
      ∃ B, MatrixPairing Q hQ N C B)
    (β a b : ℝ) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ᵐ x ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      β*a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*M x i j*t j)
    (hc : ∀ᵐ x ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      b*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*C x i j*t j) :
    CommonDomainComparison ρ Ω N M C β a := by
  obtain ⟨Q,hr,hQ,hd,H,hH⟩ := hphys
  obtain ⟨B,hB⟩ := hcore Q hQ
  exact ⟨Q,hr,hQ,(fun W u => ⟨hd W u,domain_of_pairing Q hQ N C B hB W u⟩),H,B,hH,hB,
    signed_pairing Q hQ N M C H B hH hB β,
    compressed_comparison Q hQ N M C H B hH hB β a b hβ ha hb hl hc⟩

/-- See Subsection 5.1 of the paper: the full-cycle signed multiplication defect is
zero on the good event and the physical-minus-reference defect elsewhere.
There is no conditional covariance or exterior Schur term. -/
theorem full_multiplication_defect (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (i j : Fin (N : ℕ)) :
    hessianMatrix U y i j - β.val*PhysicalCore.fullMatrix s N hN K θ ε κ₀ y i j =
      if y ∈ PhysicalCore.fullGapGoodSet s N ε κ₀ then 0 else
        β.val*(PhysicalCore.forcingHessian N θ ε y i j + GoodBlocks.gapHessian s N i j y -
          2*referenceIntervalMatrix s N hN K i j) := by
  rw [full_hessian_eq β s N hN θ ε U hU hv y hy i j]
  unfold PhysicalCore.fullMatrix
  split_ifs <;> simp only [Matrix.add_apply,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul] <;> ring

end Internal

/-- See Subsection 5.1 of the paper, full-cycle clause. The literal physical and
core forms have the entire intrinsic Sobolev domain. Both equations
are compressed to its same closed zero-sum component subspace. They have
unique solutions for every L² vector source. Their signed difference is
integrable, vanishes on the good event, and yields the subtraction and
physical energy inequality. The mass is explicitly
`min(1,s(s+1)) N^(-(s+2)ε)`, with structural exponent independent of beta. -/
theorem full_comparison (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ)/4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε) :
    let ρ := fullIntrinsicTiltedGapLaw (ofLong β s) N θ ε false
    let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
    let C := fun z => PhysicalCore.fullMatrix s N hN K θ ε κ₀ (Y z)
    let a := min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*ε)
    0 < a ∧ ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y) ∧
      (∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))), WithLp.ofLp y ∈ Riesz1.gapSimplex N →
        ∀ i j, hessianMatrix U y i j - β.val*PhysicalCore.fullMatrix s N hN K θ ε κ₀ y i j =
          if y ∈ PhysicalCore.fullGapGoodSet s N ε κ₀ then 0 else
            β.val*(PhysicalCore.forcingHessian N θ ε y i j + GoodBlocks.gapHessian s N i j y -
              2*referenceIntervalMatrix s N hN K i j)) ∧
      Internal.CommonDomainComparison ρ (intrinsicGapDomain N) N
        (fun z => hessianMatrix U (Y z)) C β.val a := by
  intro ρ Y C a
  obtain ⟨U,hU,hv,hphys⟩ := full_physical_form β s N hN θ ε
  have ha : 0 < a := (Internal.full_physical_lower β s N hN θ ε hε U hU hv).1
  obtain ⟨b,hb,hc⟩ := PhysicalCore.fullMatrix_lower β s N hN K hK hKN θ ε κ₀ hε
  refine ⟨ha,U,hU,hv,?_,?_⟩
  · exact fun y hy i j => Internal.full_multiplication_defect β s N hN K θ ε κ₀ U hU hv y hy i j
  · apply Internal.common_domain_comparison (intrinsicGapDomain N) N _ C hphys
      (fun Q hQ => Internal.full_core_form β s N hN K θ ε κ₀ Q hQ)
      β.val a b β.property ha hb
    · exact Internal.full_physical_lower_ae β s N hN θ ε hε U hU hv
    · exact ae_of_all ρ (fun z t => hc (Y z) t)

/-- See Subsection 5.1 of the paper, uniform mass constants for both geometry clauses.
The constants precede every volume, epsilon and inverse temperature. -/
theorem comparison_mass_constants (s : Riesz1.RieszExponent) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (n : ℕ+) (ε : ℝ),
      0 < min 1 (s.val*(s.val+1))*(n : ℝ)^(-(s.val+2)*ε) ∧
      C⁻¹*(n : ℝ)^(-κ*ε) ≤ min 1 (s.val*(s.val+1))*(n : ℝ)^(-(s.val+2)*ε) := by
  have hp : 0 < min 1 (s.val*(s.val+1)) := lt_min zero_lt_one (by nlinarith [s.property.1])
  refine ⟨(min 1 (s.val*(s.val+1)))⁻¹,s.val+2,inv_pos.mpr hp,by linarith [s.property.1],?_⟩
  intro n ε
  exact ⟨mul_pos hp (Real.rpow_pos_of_pos (by positivity) _),by rw [inv_inv]⟩

end Riesz2.PhysicalIdentity
