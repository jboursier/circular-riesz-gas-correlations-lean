/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart5
public import Riesz2.ToMathlib.ScalarFormEmbeddingInverse

/-!
# Fixed-length Schur transport and rate composition

The scalar embedding preserves the entire auxiliary Schur form and its equation. These
bridges support Lemma 6.4 on the same physical scalar domain as its native perturbation
estimates.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical MatrixOrder ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FixedLengthDecay

universe u

section ReducedTransport

variable {U U' W W' : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup U'] [InnerProductSpace ℝ U']
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [CompleteSpace W']

/-- See Subsection 6.1 and Lemma 6.4 of the paper: simultaneous changes of the
active and exterior full form domains preserve Schur reduction. -/
theorem reduced_transport_internal
    (A : U →L[ℝ] U →L[ℝ] ℝ) (A' : U' →L[ℝ] U' →L[ℝ] ℝ)
    (D : W →L[ℝ] W →L[ℝ] ℝ) (D' : W' →L[ℝ] W' →L[ℝ] ℝ)
    (C : U →L[ℝ] W →L[ℝ] ℝ) (C' : U' →L[ℝ] W' →L[ℝ] ℝ)
    (E : U ≃L[ℝ] U') (F : W ≃L[ℝ] W')
    (hA : ∀ u v, A u v = A' (E u) (E v))
    (hD : ∀ z w, D z w = D' (F z) (F w))
    (hC : ∀ u w, C u w = C' (E u) (F w))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ w, a * ‖w‖ ^ 2 ≤ D w w)
    (hl' : ∀ w, b * ‖w‖ ^ 2 ≤ D' w w) (u v : U) :
    OperatorSchur.reduced A D C a ha hl u v =
      OperatorSchur.reduced A' D' C' b hb hl' (E u) (E v) := by
  have he : F (OperatorSchur.exterior D C a ha hl u) =
      OperatorSchur.exterior D' C' b hb hl' (E u) := by
    apply CoerciveSolution.inverse_unique D' b hb hl' (C' (E u))
    intro w
    have hh := OperatorSchur.exterior_solves D C a ha hl u (F.symm w)
    rw [hD, hC, F.apply_symm_apply] at hh
    exact hh
  rw [OperatorSchur.reduced_apply, OperatorSchur.reduced_apply, hA, hC, he]

end ReducedTransport

section ScalarEmbedding

variable {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
  (μ : Measure X) (f : X → Z) (hf : MeasurableEmbedding f)
  (Q : ScalarFormData μ) (hQ : IsClosedScalarDirichletForm Q)

local notation "Q'" => ScalarFormEmbedding.form μ f hf Q
local notation "hQ'" => ScalarFormEmbedding.closed_dirichlet μ f hf Q hQ
local notation "E" => InterpolationTransport.vectorEquiv μ f hf Q hQ
local notation "T" => ScalarFormEmbedding.pullback μ f hf

/-- See Lemma 6.4 of the paper: a bounded full matrix form transports with
its entire scalar diffusion and actual multiplication integral. -/
theorem bounded_form_embedding_internal {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Z → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (hb : ∃ b : ℝ, ∀ᵐ x ∂μ.map f, ∀ i j, |M x i j| ≤ b)
    (hp : ∀ᵐ x ∂μ.map f, (M x).PosSemidef)
    (hm' : ∀ i j, Measurable (fun x => M (f x) i j))
    (hb' : ∃ b : ℝ, ∀ᵐ x ∂μ, ∀ i j, |M (f x) i j| ≤ b)
    (hp' : ∀ᵐ x ∂μ, (M (f x)).PosSemidef)
    (u v : MatrixEnergy.Vector (ι := ι) Q' hQ') :
    BoundedMatrixForms.form Q' hQ' M hm hb hp u v =
      BoundedMatrixForms.form Q hQ (M ∘ f) hm' hb' hp' (E ι u) (E ι v) := by
  rw [BoundedMatrixForms.form_apply, BoundedMatrixForms.form_apply]
  rw [InterpolationTransport.matrixFieldPair_integral μ f hf]
  rfl

/-- See Subsection 6.1 and Lemma 6.4 of the paper: scalar pullback commutes with
the active/exterior assembly, including empty exterior blocks. -/
theorem assemble_embedding_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q' hQ')
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ)-(n : ℕ))) Q' hQ') :
    E (Fin (m : ℕ)) (SchurRestriction.assemble Q' hQ' n m hnm (u,z)) =
      SchurRestriction.assemble Q hQ n m hnm
        (E (Fin (n : ℕ)) u, E (Fin ((m : ℕ)-(n : ℕ))) z) := by
  apply PiLp.ext
  intro i
  by_cases hi : i.val < (n : ℕ)
  · let j : Fin (n : ℕ) := ⟨i.val, hi⟩
    have hij : j.castLE hnm = i := Fin.ext rfl
    rw [← hij]
    change ScalarFormEmbedding.domainIsometry μ f hf Q hQ
      (SchurRestriction.assemble Q' hQ' n m hnm (u,z) (j.castLE hnm)) = _
    rw [SchurRestriction.assemble_left_apply, SchurRestriction.assemble_left_apply]
    rfl
  · let j : Fin ((m : ℕ)-(n : ℕ)) := ⟨i.val-(n : ℕ), by omega⟩
    have hij : (exteriorIndexEquiv_internal n m j).val = i := by
      apply Fin.ext
      change (n : ℕ)+(i.val-(n : ℕ)) = i.val
      omega
    rw [← hij]
    change ScalarFormEmbedding.domainIsometry μ f hf Q hQ
      (SchurRestriction.assemble Q' hQ' n m hnm (u,z)
        (exteriorIndexEquiv_internal n m j).val) = _
    rw [assemble_right_apply_internal, assemble_right_apply_internal]
    rfl

variable (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
  (hm : 2 ≤ (m : ℕ)) (k : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
  (M : Z → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
  (hM : PeriodizedMatrixBounds (ν := μ.map f) s n m hm k C κ γ ε M)

local notation "hM'" => FullCycleComparison.matrix_bounds_pullback_internal μ f hf.measurable
  s n m hm k C κ γ ε M hM
local notation "Schur" => SchurRestriction.schurForm Q' hQ' n m hnm s hm k C κ γ ε β hC hβ M hM
local notation "Schur'" => SchurRestriction.schurForm Q hQ n m hnm s hm k C κ γ ε β hC hβ
  (M ∘ f) hM'

/-- See Subsection 6.1 and Lemma 6.4 of the paper: the Schur form used by the
auxiliary mean theorem transports under a scalar embedding. Both sides
act on the full active Sobolev product. -/
theorem schurForm_embedding_internal
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q' hQ') :
    Schur u v = Schur' (E (Fin (n : ℕ)) u) (E (Fin (n : ℕ)) v) := by
  let G := SchurRestriction.splitForm Q' hQ' n m hnm s hm k C κ γ ε β hC hβ M hM
  let G' := SchurRestriction.splitForm Q hQ n m hnm s hm k C κ γ ε β hC hβ (M ∘ f) hM'
  have hfull (u v : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q' hQ') :
      SchurRestriction.periodizedForm Q' hQ' n m s hm k C κ γ ε β hC hβ M hM u v =
      SchurRestriction.periodizedForm Q hQ n m s hm k C κ γ ε β hC hβ (M ∘ f) hM'
        (E (Fin (m : ℕ)) u) (E (Fin (m : ℕ)) v) :=
    bounded_form_embedding_internal μ f hf Q hQ _
      (SchurRestriction.periodized_scaled_measurable β hM)
      (SchurRestriction.periodized_scaled_bounded β hM)
      (SchurRestriction.periodized_scaled_psd β hβ hC hM)
      (SchurRestriction.periodized_scaled_measurable β hM')
      (SchurRestriction.periodized_scaled_bounded β hM')
      (SchurRestriction.periodized_scaled_psd β hβ hC hM') u v
  have hsplit (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q' hQ')
      (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ)-(n : ℕ))) Q' hQ') :
      G (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (u,z))
        (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (v,w)) =
      G' (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (E _ u,E _ z))
        (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (E _ v,E _ w)) := by
    change SchurRestriction.periodizedForm Q' hQ' n m s hm k C κ γ ε β hC hβ M hM
      (SchurRestriction.assemble Q' hQ' n m hnm (u,z))
      (SchurRestriction.assemble Q' hQ' n m hnm (v,w)) = _
    rw [hfull, assemble_embedding_internal, assemble_embedding_internal]
    rfl
  unfold SchurRestriction.schurForm
  apply reduced_transport_internal _ _ _ _ _ _
    (E (Fin (n : ℕ))).toContinuousLinearEquiv
    (E (Fin ((m : ℕ)-(n : ℕ)))).toContinuousLinearEquiv
  · intro a b
    change G (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (a,0))
      (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (b,0)) =
      G' (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (E _ a,0))
        (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (E _ b,0))
    simpa only [map_zero] using hsplit a b 0 0
  · intro z w
    change G (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (0,z))
      (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (0,w)) =
      G' (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (0,E _ z))
        (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (0,E _ w))
    simpa only [map_zero] using hsplit 0 0 z w
  · intro a w
    change G (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (a,0))
      (SchurRestriction.join Q' hQ' n ((m : ℕ)-(n : ℕ)) (0,w)) =
      G' (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (E _ a,0))
        (SchurRestriction.join Q hQ n ((m : ℕ)-(n : ℕ)) (0,E _ w))
    simpa only [map_zero] using hsplit a 0 0 w

/-- See Lemma 6.4 of the paper: the auxiliary Schur equation, its source
and every active test transport together. This is a bidirectional equation,
not just equality of the two energies on a core. -/
theorem schur_equation_embedding_iff_internal
    (χ : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 (μ.map f)))
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q' hQ') :
    (∀ v, Schur u v = inner ℝ χ (OperatorSchur.vectorValues Q' hQ' v)) ↔
      ∀ v, Schur' (E (Fin (n : ℕ)) u) v =
        inner ℝ (InterpolationTransport.sourceEquiv μ f hf _ χ)
          (OperatorSchur.vectorValues Q hQ v) := by
  have heq (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q' hQ') :=
    schurForm_embedding_internal μ f hf Q hQ s n m hnm hm k C κ γ ε β hC hβ M hM u v
  have hinner (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q' hQ') :
      inner ℝ χ (OperatorSchur.vectorValues Q' hQ' v) =
        inner ℝ (InterpolationTransport.sourceEquiv μ f hf _ χ)
          (OperatorSchur.vectorValues Q hQ (E _ v)) := by
    rw [← InterpolationTransport.vectorValues_transport μ f hf Q hQ]
    exact ((InterpolationTransport.sourceEquiv μ f hf _).inner_map_map _ _).symm
  constructor
  · intro hu v
    have hh := hu ((E _).symm v)
    rw [heq, hinner, (E _).apply_symm_apply] at hh
    exact hh
  · intro hu v
    rw [heq, hinner]
    exact hu (E _ v)

end ScalarEmbedding

section AuxiliaryTransport

variable {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
  (μ : Measure X) (f : X → Z) (hf : MeasurableEmbedding f)
  (Q : ScalarFormData μ)

local notation "Q'" => ScalarFormEmbedding.form μ f hf Q
local notation "e" => ScalarFormEmbedding.domainEquiv μ f hf Q
local notation "T" => ScalarFormEmbedding.pullback μ f hf

/-- See the proof of Lemma 6.4 and Lemma 6.4 of the paper: the vector essential
norm of a scalar-form tuple transports exactly, at every exponent. -/
theorem tuple_eLpNorm_embedding_internal {ι : Type} [Fintype ι]
    (v : ι → Q'.1) (p : ℝ≥0∞) :
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => (e (v i)).val x) : EuclideanSpace ℝ ι)) p μ =
      eLpNorm (fun x => (WithLp.toLp 2 (fun i => (v i).val x) : EuclideanSpace ℝ ι)) p (μ.map f) := by
  rw [hf.eLpNorm_map_measure]
  apply eLpNorm_congr_ae
  have he := ae_all_iff.mpr (fun i : ι => ScalarFormEmbedding.pullback_ae μ f hf (v i).val)
  filter_upwards [he] with x hx
  exact congrArg (WithLp.toLp 2) (funext hx)

/-- See the proof of Lemma 6.4 and Lemma 6.4 of the paper: all five auxiliary
estimates transport on one scalar form with exactly the same constants.
In particular the mean gradient and the vector supremum are retained. -/
theorem auxiliary_estimates_embedding_iff_internal {ι : Type} [Fintype ι]
    (v : ι → Q'.1) (χ : Lp ℝ 2 (μ.map f)) (D A G V : ℝ) (profile : ι → ℝ) :
    ((∀ j, ‖(v j).val‖ ≤ profile j*‖χ‖) ∧
      (∑ j, ‖(v j).val‖) ≤ D*‖χ‖ ∧
      ‖(∑ j, v j : Q'.1).val‖ ≤ A*‖χ‖ ∧
      Real.sqrt (Q'.2 (∑ j, v j) (∑ j, v j)) ≤ G*‖χ‖ ∧
      eLpNorm (fun x => (WithLp.toLp 2 (fun i => (v i).val x) : EuclideanSpace ℝ ι)) ∞ (μ.map f) ≤
        ENNReal.ofReal V*eLpNorm χ ∞ (μ.map f)) ↔
    ((∀ j, ‖(e (v j)).val‖ ≤ profile j*‖T χ‖) ∧
      (∑ j, ‖(e (v j)).val‖) ≤ D*‖T χ‖ ∧
      ‖(∑ j, e (v j) : Q.1).val‖ ≤ A*‖T χ‖ ∧
      Real.sqrt (Q.2 (∑ j, e (v j)) (∑ j, e (v j))) ≤ G*‖T χ‖ ∧
      eLpNorm (fun x => (WithLp.toLp 2 (fun i => (e (v i)).val x) : EuclideanSpace ℝ ι)) ∞ μ ≤
        ENNReal.ofReal V*eLpNorm (T χ) ∞ μ) := by
  have hn (u : Q'.1) : ‖(e u).val‖ = ‖u.val‖ := (T).norm_map u.val
  have hs : (∑ j, e (v j) : Q.1) = e (∑ j, v j) := (map_sum e _ _).symm
  rw [hs, ScalarFormEmbedding.pullback_eLpNorm,
    tuple_eLpNorm_embedding_internal μ f hf Q v ∞]
  simp only [hn, (T).norm_map]
  rfl

end AuxiliaryTransport

section PhysicalSolution

/-- See Lemma 6.4 of the paper: the actual ambient physical Hessian has a
unique tangent weak solution on every included fixed-length law and closed
scalar form. The all-size curvature yields both direct coordinate bounds. This includes every size below the size threshold and both exponent regimes. -/
theorem physical_tangent_solution_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (d e a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1)) (L : ℝ)
    (hyL : ((d+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((e+a : ℕ)+1 : ℝ)-∑ k, z.val k = L) :
    let Y := RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val
    let Z := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (d+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (e+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ x (hx : x ∈ Dy), Ky x = physicalAmbientGapEnergy p (d+a).succPNat ⟨Y x,hx⟩) ∧
      (∀ x (hx : x ∈ Dz), Kz x = physicalAmbientGapEnergy p (e+a).succPNat ⟨Z x,hx⟩) ∧
    ∀ (hLN : L < ((d+a : ℕ)+1 : ℝ)) (ρ : Measure (AffineSimplex.massSimplex a L)),
    let ν := ρ.map (InterpolationTransport.inclusion a L ((d+a : ℕ)+1) hLN)
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
        (1-t)*Ky u+t*Kz u)
    let H := fun x : AffineSimplex.chartDomain (a+1) ((d+a : ℕ)+1) => hessianMatrix Ht x.val
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
      (i₀ : Fin (a+1)) (χ : Lp ℝ 2 ν),
    (∃! ψ : Fin (a+1) → Q.1, WeightedWeakSolution Q H
      (zeroSumComponents (Fin (a+1))) (fun i => if i = i₀ then χ else 0) ψ) ∧
    ∀ ψ : Fin (a+1) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (a+1))) (fun i => if i = i₀ then χ else 0) ψ →
      (∑ j, InteractionDifferential.boundaryWeight p.val.2 a.succPNat j*‖(ψ j).val‖) ≤
        Real.sqrt (a+1 : ℝ)*((p.val.1*min 1 (p.val.2*(p.val.2+1)))⁻¹*
          (a+1 : ℝ)^((p.val.2+2)*ε)*‖χ‖) ∧
      (∑ j, ‖(ψ j).val‖) ≤
        Real.sqrt (a+1 : ℝ)*((p.val.1*min 1 (p.val.2*(p.val.2+1)))⁻¹*
          (a+1 : ℝ)^((p.val.2+2)*ε)*‖χ‖) := by
  intro Y Z Dy Dz
  obtain ⟨hc,Ky,Kz,hKy,hKz,hky,hkz,hcurv⟩ :=
    InterpolationCoercivity.physical_interpolant_coercivity p θ ε hε d e a ha y z L hyL hzL
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro hLN ρ ν t ht Ht H Q hQ i₀ χ
  let a0 := p.val.1*min 1 (p.val.2*(p.val.2+1))
  let c := a0*(a+1 : ℝ)^(-(p.val.2+2)*ε)
  have ha0 : 0 < a0 := mul_pos p.property.1 hc
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hsupp : ∀ᵐ x ∂ν, x.val ∈ AffineSimplex.massSimplex a L := by
    rw [(InterpolationTransport.measurableEmbedding_inclusion a L _ hLN).ae_map_iff]
    exact ae_of_all _ (fun x => x.property)
  have hdata : ∀ᵐ x ∂ν, (H x).PosSemidef ∧ ∀ v : Fin (a+1) → ℝ,
      c*(∑ i, v i^2) ≤ ∑ i, ∑ j, v i*H x i j*v j := by
    filter_upwards [hsupp] with x hx
    obtain ⟨hs,hl⟩ := hcurv t ht x.val hx
    have hβs : ContDiffAt ℝ ∞ Ht x.val := contDiffAt_const.mul hs
    have hscale : hessianMatrix Ht x.val = p.val.1 • hessianMatrix
        (fun u : EuclideanSpace ℝ (Fin (a+1)) =>
          (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
            (1-t)*Ky u+t*Kz u) x.val := by
      ext i j
      rw [Intrinsic.hessianMatrix_eq_second hβs,
        PhysicalCollision.internal_hessian_const_mul (hs.of_le (by simp)),
        ← Intrinsic.hessianMatrix_eq_second hs]
      rfl
    have hl' (v : Fin (a+1) → ℝ) : c*(∑ i, v i^2) ≤ ∑ i, ∑ j, v i*H x i j*v j := by
      have hh := mul_le_mul_of_nonneg_left (hl (WithLp.toLp 2 v)) p.property.1.le
      dsimp only [H]
      rw [hscale]
      simpa only [c,a0, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc,
        mul_comm, mul_left_comm] using hh
    refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩,hl'⟩
    · ext i j
      simp only [H, Matrix.conjTranspose_apply, star_trivial,
        Intrinsic.hessianMatrix_eq_second hβs]
      exact hβs.isSymmSndFDerivAt (by simp) _ _
    · intro v
      have hh := (show 0 ≤ c*(∑ i, v i^2) by positivity).trans (hl' v)
      simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using hh
  have hHp := hdata.mono fun _ hx => hx.1
  have hl := hdata.mono fun _ hx v (_ : v ∈ zeroSumComponents (Fin (a+1))) => hx.2 v
  have hHm (i j : Fin (a+1)) : Measurable (fun x => H x i j) :=
    (DifferentiatedPoisson.measurable_hessian_entries (V := Ht) i j).comp measurable_subtype_coe
  refine ⟨MatrixEnergy.weightedWeakSolution_existsUnique Q hQ H
    (zeroSumComponents (Fin (a+1))) hHp c hc0 hl hHm _ , ?_⟩
  intro ψ hψ
  have he := tangent_coercivity_sums_internal Q hQ a.succPNat H hHm hHp c hc0 hl
    p.val.2 p.property.2.1 i₀ χ ψ hψ
  have heq : c⁻¹ = a0⁻¹*(a+1 : ℝ)^((p.val.2+2)*ε) := by
    dsimp only [c]
    rw [mul_inv, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ a+1)]
    congr 1
    congr 1
    ring
  simpa only [heq,a0,Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using he.2

/-- See Subsection 6.1 and Lemma 6.4 of the paper: choose the normalized physical
law and its intrinsic scalar form, together with the unique tangent solution
for the literal ambient physical Hessian. Compatibility alone suffices. No typicality, upper coefficient bound or size threshold is required. -/
theorem normalized_physical_tangent_solution_internal
    (p : Parameters) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε)
    (a d e : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (he : 1 ≤ e) (L : ℝ)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (hyL : (∑ i, y.val i)+L = ((d+a : ℕ)+1 : ℝ))
    (hzL : (∑ i, z.val i)+L = ((e+a : ℕ)+1 : ℝ)) :
    let hLN := InterpolationTransport.compatible_mass_lt a d hd L y hyL
    let Y := RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val
    let Z := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (d+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (e+a).succPNat
    let S := AffineSimplex.massSimplex a L
    let μ : Measure S := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let Ey := fun u : S => physicalAmbientGapEnergy p (d+a).succPNat
      ⟨Y u.val, ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d a y u.val
        (by have hr : ((d+a : ℕ)+1 : ℝ)-∑ i, y.val i = L := by linarith
            rw [hr]; exact u.property))⟩
    let Ez := fun u : S => physicalAmbientGapEnergy p (e+a).succPNat
      ⟨Z u.val, ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e a z u.val
        (by have hr : ((e+a : ℕ)+1 : ℝ)-∑ i, z.val i = L := by linarith
            rw [hr]; exact u.property))⟩
    let P := fun x : EuclideanSpace ℝ (Fin (a+1)) => ∑ i,
      (θ.val (((a+1 : ℕ) : ℝ)^(-ε)*x i) + θ.val (((a+1 : ℕ) : ℝ)^(-ε)*(x i)⁻¹))
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy p (d+a).succPNat ⟨Y u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy p (e+a).succPNat ⟨Z u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let w := fun u : S => ENNReal.ofReal (Real.exp (-p.val.1*(P u.val+(1-t)*Ey u+t*Ez u)))
    ∃ h0 ht,
    let ρ := AffineFibre.normalizedMeasure μ w h0 ht
    let ν := ρ.map (InterpolationTransport.inclusion a L ((d+a : ℕ)+1) hLN)
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*(P u+(1-t)*Ky u+t*Kz u)
    let H := fun x : AffineSimplex.chartDomain (a+1) ((d+a : ℕ)+1) => hessianMatrix Ht x.val
    ∀ _frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (a+1)) (χ : Lp ℝ 2 ν),
        ∃! ψ : Fin (a+1) → Q.1, WeightedWeakSolution Q H
          (zeroSumComponents (Fin (a+1))) (fun i => if i = i₀ then χ else 0) ψ := by
  intro hLN Y Z Dy Dz S μ Ey Ez P
  obtain ⟨Ky,Kz,hKy,hKz,hky,hkz,hsol⟩ := physical_tangent_solution_internal p θ ε hε
    d e a ha y z L (by linarith) (by linarith)
  obtain ⟨Ay,Az,_hAy,_hAz,_hay,_haz,hscalar⟩ :=
    InterpolationTransport.physical_scalar_transport p a d e hd he θ ε L y z hyL hzL
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht w
  obtain ⟨h0,htop,hscalar⟩ := hscalar t ht
  refine ⟨h0,htop,?_⟩
  intro ρ ν Ht H frame
  obtain ⟨_ν,_hV,_hlaw,Q,hQ,hcons⟩ := hscalar frame
  refine ⟨Q,hQ,hcons,?_⟩
  intro i₀ χ
  dsimp only [H,Ht,P]
  simpa only [Nat.cast_add,Nat.cast_one] using (hsol hLN ρ t ht Q hQ i₀ χ).1

end PhysicalSolution

section LongRates

/-- See Lemma 6.4 of the paper: inserting the actual auxiliary mean and
mean-gradient bounds into the explicit long-range comparison gives a
uniform squared-error estimate. The common loss is chosen before all
size, source and form parameters. -/
theorem long_comparison_square_uniform_internal (s : Riesz1.RieszExponent)
    (loss a0 L0 K0 D0 V0 E0 c δ : ℝ)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hL0 : 0 ≤ L0)
    (hK0 : 0 ≤ K0) (hD0 : 0 ≤ D0) (hV0 : 0 ≤ V0) (hE0 : 0 ≤ E0) :
    ∀ (X : Type*) [MeasurableSpace X] (ν : Measure X)
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n : ℕ+) (S : Q.1) (F B E L τ R : ℝ),
      0 ≤ F → 0 ≤ B → 0 ≤ E → 0 ≤ L → 0 ≤ τ → 0 ≤ R →
      ‖S.val‖ ≤ D0*(n : ℝ)^(loss-(1-s.val))*F →
      Real.sqrt (Q.2 S S) ≤ D0*(n : ℝ)^(loss-(1-s.val)/2)*F →
      L ≤ L0*(n : ℝ)^(2*loss-1/2)*F →
      τ ≤ 3*(n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ)*
        ((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B)) →
      R ≤ (n : ℝ)⁻¹*Q.2 S S +
        K0*(n : ℝ)^loss*(n : ℝ)^(-s.val)*‖S.val‖^2 +
          (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 →
      E ≤ 2*L/(a0*(n : ℝ)^(-loss)) +
        Real.sqrt ((2*τ+R)/(a0*(n : ℝ)^(-loss))) +
          (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ →
      E^2 ≤
        (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*F^2 +
        (9*(3*E0*(2*V0+a0⁻¹)*V0+E0*V0^2)/a0)*
          (n : ℝ)^(2+4*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
  intro X _ ν Q hQ n S F B E L τ R hF hB hE hL hτ hR hm hg hLb hτb hRb hcomp
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let T0 := 3*E0*(2*V0+a0⁻¹)*V0+E0*V0^2
  have ht0 : 0 ≤ T0 := by dsimp only [T0]; positivity
  have hτshape : τ ≤ T0*(n : ℝ)^(2+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
    have heq : 3*(n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ)*
        ((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B)) =
        (3*E0*(2*V0+a0⁻¹)*V0)*(n : ℝ)^(2+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
      rw [show 2+2*loss = (2+loss)+loss by ring, Real.rpow_add hn, Real.rpow_add hn,
        Real.rpow_two]
      ring
    apply (hτb.trans_eq heq).trans
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity))
      (sq_nonneg B)
    dsimp only [T0]
    linarith [mul_nonneg hE0 (sq_nonneg V0)]
  have hRs := long_mean_energy_rate_internal Q hQ s n S D0 F loss
    (K0*(n : ℝ)^loss)
    ((n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2) R
    hD0 hF (by positivity) hm hg hRb
  have hRshape : R ≤ (1+K0)*D0^2*(n : ℝ)^(4*loss-1)*F^2 +
      T0*(n : ℝ)^(2+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
    have hdet : (1+K0*(n : ℝ)^loss)*D0^2*(n : ℝ)^(2*loss-2+s.val)*F^2 ≤
        (1+K0)*D0^2*(n : ℝ)^(4*loss-1)*F^2 := by
      have hcoef : 1+K0*(n : ℝ)^loss ≤ (1+K0)*(n : ℝ)^loss := by
        nlinarith only [Real.one_le_rpow hn1 hloss]
      calc
        _ ≤ ((1+K0)*(n : ℝ)^loss)*D0^2*(n : ℝ)^(2*loss-2+s.val)*F^2 := by
          gcongr
        _ = (1+K0)*D0^2*(n : ℝ)^(3*loss-2+s.val)*F^2 := by
          rw [show 3*loss-2+s.val = loss+(2*loss-2+s.val) by ring,
            Real.rpow_add hn loss (2*loss-2+s.val)]
          ring
        _ ≤ _ := by gcongr; linarith [s.property.2]
    have htail : (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 ≤
        T0*(n : ℝ)^(2+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
      have heq : (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 =
          (E0*V0^2)*(n : ℝ)^(2+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
        rw [show 2+2*loss = 2+(loss+loss) by ring,
          Real.rpow_add hn, Real.rpow_add hn, Real.rpow_two]
        ring
      rw [heq]
      gcongr
      dsimp only [T0]
      have : 0 ≤ 3*E0*(2*V0+a0⁻¹)*V0 := by positivity
      linarith
    exact hRs.trans (add_le_add hdet htail)
  have hrshape : (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ ≤ D0*(n : ℝ)^(2*loss-1/2)*F := by
    calc
      _ ≤ (n : ℝ)^(-(1 : ℝ)/2)*(D0*(n : ℝ)^(loss-(1-s.val))*F) := by gcongr
      _ = D0*(n : ℝ)^(loss-(1-s.val)-1/2)*F := by
        rw [show loss-(1-s.val)-1/2 = (-(1 : ℝ)/2)+(loss-(1-s.val)) by ring,
          Real.rpow_add hn]
        ring
      _ ≤ _ := by gcongr; linarith [s.property.2]
  have hc : E ≤ 2*L/(a0*(n : ℝ)^(-(2*loss))) +
      Real.sqrt ((2*τ+R)/(a0*(n : ℝ)^(-(2*loss)))) + (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ := by
    apply hcomp.trans
    apply add_le_add _ le_rfl
    apply add_le_add
    · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
      linarith
    · apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
      linarith
  have hh := comparison_square_scaled_internal (n : ℝ) (2*loss) (2+2*loss) c δ
    a0 L0 ((1+K0)*D0^2) T0 D0 F B E L τ R ((n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖)
    hn1 (by positivity) ha0 hL0 (by positivity) hD0 hF hE hL hτ hR (by positivity)
    hLb hτshape (by simpa only [show 2*(2*loss)-1 = 4*loss-1 by ring] using hRshape) hrshape hc
  dsimp only [T0] at hh
  simpa only [show 4*(2*loss)-1 = 8*loss-1 by ring,
    show (2+2*loss)+2*loss = 2+4*loss by ring] using hh

end LongRates

section ShortRates

/-- See Lemma 6.4 of the paper: the short-range normal energy and actual
coefficient-defect comparison yield a uniform squared error, retaining
both auxiliary mean estimates and every exceptional polynomial factor. -/
theorem short_comparison_square_uniform_internal
    (loss a0 K0 D0 V0 E0 c δ : ℝ)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0)
    (hK0 : 0 ≤ K0) (hD0 : 0 ≤ D0) (hV0 : 0 ≤ V0) (hE0 : 0 ≤ E0) :
    ∀ (X : Type*) [MeasurableSpace X] (ν : Measure X)
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n : ℕ+) (S : Q.1) (F B E τ R : ℝ),
      0 ≤ F → 0 ≤ B → 0 ≤ E → 0 ≤ τ → 0 ≤ R →
      ‖S.val‖ ≤ D0*(n : ℝ)^loss*F →
      Real.sqrt (Q.2 S S) ≤ D0*(n : ℝ)^loss*F →
      τ ≤ (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ)*
        ((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B)) →
      R ≤ (n : ℝ)⁻¹*Q.2 S S +
        K0*(n : ℝ)^(loss-1)*‖S.val‖^2 +
          (n : ℝ)^4*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 →
      E ≤ Real.sqrt ((2*τ+R)/(a0*(n : ℝ)^(-loss))) +
          (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ →
      E^2 ≤
        (3*((1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*F^2 +
        (9*(E0*(2*V0+a0⁻¹)*V0+E0*V0^2)/a0)*
          (n : ℝ)^(4+4*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
  intro X _ ν Q hQ n S F B E τ R hF hB hE hτ hR hm hg hτb hRb hcomp
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let T0 := E0*(2*V0+a0⁻¹)*V0+E0*V0^2
  have hT0 : 0 ≤ T0 := by dsimp only [T0]; positivity
  have hpow (q r : ℝ) : (n : ℝ)^q*(D0*(n : ℝ)^r*F)^2 =
      D0^2*(n : ℝ)^(q+2*r)*F^2 := by
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hn.le]
    norm_num only [Nat.cast_ofNat]
    rw [show r*(2 : ℝ) = 2*r by ring, Real.rpow_add hn q (2*r)]
    ring
  have hm2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hm
  have hg2 := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hg
  rw [Real.sq_sqrt (hQ.2.2.1 S)] at hg2
  have hdet : (n : ℝ)⁻¹*Q.2 S S + K0*(n : ℝ)^(loss-1)*‖S.val‖^2 ≤
      (1+K0)*D0^2*(n : ℝ)^(4*loss-1)*F^2 := by
    calc
      _ ≤ (n : ℝ)⁻¹*(D0*(n : ℝ)^loss*F)^2 +
          K0*(n : ℝ)^(loss-1)*(D0*(n : ℝ)^loss*F)^2 := by gcongr
      _ = D0^2*(n : ℝ)^(2*loss-1)*F^2 + K0*D0^2*(n : ℝ)^(3*loss-1)*F^2 := by
        rw [← Real.rpow_neg_one, hpow, mul_assoc K0, hpow,
          show -1+2*loss = 2*loss-1 by ring,
          show loss-1+2*loss = 3*loss-1 by ring]
        ring
      _ ≤ D0^2*(n : ℝ)^(4*loss-1)*F^2 + K0*D0^2*(n : ℝ)^(4*loss-1)*F^2 := by
        apply add_le_add <;> gcongr <;> linarith
      _ = _ := by ring
  have htail : (n : ℝ)^4*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 ≤
      T0*(n : ℝ)^(4+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
    have heq : (n : ℝ)^4*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 =
        (E0*V0^2)*(n : ℝ)^(4+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
      rw [show 4+2*loss = 4+(loss+loss) by ring,
        Real.rpow_add hn 4 (loss+loss), Real.rpow_add hn loss loss,
        show (n : ℝ)^(4 : ℝ) = (n : ℝ)^4 by exact Real.rpow_natCast _ 4]
      ring
    rw [heq]
    gcongr
    dsimp only [T0]
    have : 0 ≤ E0*(2*V0+a0⁻¹)*V0 := by positivity
    linarith
  have hτshape : τ ≤ T0*(n : ℝ)^(4+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
    have heq : (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ)*
        ((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B)) =
        (E0*(2*V0+a0⁻¹)*V0)*(n : ℝ)^(2+2*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
      rw [show 2+2*loss = 2+(loss+loss) by ring,
        Real.rpow_add hn 2 (loss+loss), Real.rpow_add hn loss loss, Real.rpow_two]
      ring
    apply (hτb.trans_eq heq).trans
    gcongr
    · dsimp only [T0]
      linarith [mul_nonneg hE0 (sq_nonneg V0)]
    · linarith
  have hRshape := hRb.trans (add_le_add hdet htail)
  have hrshape : (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ ≤ D0*(n : ℝ)^(2*loss-1/2)*F := by
    calc
      _ ≤ (n : ℝ)^(-(1 : ℝ)/2)*(D0*(n : ℝ)^loss*F) := by gcongr
      _ = D0*(n : ℝ)^(loss-1/2)*F := by
        rw [show loss-1/2 = (-(1 : ℝ)/2)+loss by ring, Real.rpow_add hn (-(1 : ℝ)/2) loss]
        ring
      _ ≤ _ := by gcongr; linarith
  have hc : E ≤ 2*0/(a0*(n : ℝ)^(-(2*loss))) +
      Real.sqrt ((2*τ+R)/(a0*(n : ℝ)^(-(2*loss)))) + (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ := by
    simp only [mul_zero,zero_div,zero_add]
    apply hcomp.trans
    gcongr
    linarith
  have hh := comparison_square_scaled_internal (n : ℝ) (2*loss) (4+2*loss) c δ
    a0 0 ((1+K0)*D0^2) T0 D0 F B E 0 τ R ((n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖)
    hn1 (by positivity) ha0 le_rfl (by positivity) hD0 hF hE le_rfl hτ hR (by positivity)
    (by simp) hτshape
    (by simpa only [show 2*(2*loss)-1 = 4*loss-1 by ring] using hRshape) hrshape hc
  dsimp only [T0] at hh
  simpa only [mul_zero,zero_div,zero_pow (by omega : 2 ≠ 0),zero_add,
    show 4*(2*loss)-1 = 8*loss-1 by ring,
    show (4+2*loss)+2*loss = 4+4*loss by ring] using hh

end ShortRates

section BothRegimes

variable {H : Type*} [NormedAddCommGroup H]

/-- See Lemma 6.4 of the paper: both coordinate conclusions in both regimes,
from one common squared comparison. All constants precede the size and
source, and the literal source boundary weight is used throughout. -/
theorem rates_both_regimes_from_square_internal (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (D0 A T q loss c δ : ℝ) (hD0 : 0 ≤ D0)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (i₀ : Fin (n : ℕ)),
      |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
      ∀ (F B : ℝ) (ψ v : Fin (n : ℕ) → H), 0 ≤ F → 0 ≤ B →
      (∀ j, ‖v j‖ ≤ D0*(n : ℝ)^loss *
        (1+(Nat.dist j.val i₀.val : ℝ))^(if s < 1 then s-2 else -s)*F) →
      (∑ j, ‖v j‖) ≤ D0*(n : ℝ)^loss*F →
      ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
        A*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ)*B^2 →
      (∑ j, InteractionDifferential.boundaryWeight s n j*‖ψ j‖) ≤
        C*(n : ℝ)^(loss-min s 1/2)*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) ∧
      (∑ j, ‖ψ j‖) ≤ C*(n : ℝ)^loss*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) := by
  by_cases h : s < 1
  · simpa only [h,↓reduceIte,min_eq_left h.le] using
      (long_rates_from_square_internal (H := H) ⟨s,hs,h⟩ D0 A T q loss c δ
        hD0 hA hT hc hδ)
  · have hs' : 1 < s := lt_of_le_of_ne (le_of_not_gt h) hs1.symm
    simpa only [h,↓reduceIte,min_eq_right hs'.le] using
      (short_rates_from_square_internal (H := H) s hs' D0 A T q loss c δ
        hD0 hA hT hc hδ)

/-- See Lemma 6.4 of the paper: the all-size two-regime composition.
This theorem assumes the uniform large-size auxiliary profile and squared
vector comparison. Its small-size premise
is discharged from the actual physical tangent equation and lower curvature,
and no upper physical bound is used below the threshold. -/
theorem fixed_length_decay_from_comparison_internal
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (κ0 κ1 ε : ℝ) (hε : 0 ≤ ε)
    (n0 : ℕ) (a0 D0 A T q c δ : ℝ) (ha0 : 0 < a0)
    (hD0 : 0 ≤ D0) (hA : 0 ≤ A) (hT : 0 ≤ T) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ+) (X : Type u) [MeasurableSpace X] (ν : Measure X)
      (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
      (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ),
      (∀ i j, Measurable (fun x => M x i j)) →
      ∀ _hM : ∀ᵐ x ∂ν, (M x).PosSemidef,
      (∀ᵐ x ∂ν, ∀ z ∈ zeroSumComponents (Fin (n : ℕ)),
        (a0*(n : ℝ)^(-(κ0*ε)))*(∑ i, z i^2) ≤
          ∑ i, ∑ j, z i*M x i j*z j) →
      ∀ (i₀ : Fin (n : ℕ)), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
      ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q M (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ.val else 0) ψ →
      let B := (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal
      ((n0 : ℝ) ≤ (n : ℝ) → ∃ v : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ j, ‖v j‖ ≤ D0*(n : ℝ)^(κ1*ε)*
          (1+(Nat.dist j.val i₀.val : ℝ))^(if s < 1 then s-2 else -s)*‖χ.val‖) ∧
        (∑ j, ‖v j‖) ≤ D0*(n : ℝ)^(κ1*ε)*‖χ.val‖ ∧
        ‖WithLp.toLp 2 (fun j => (ψ j).val-v j)‖^2 ≤
          A*(n : ℝ)^(2*(κ1*ε)-1)*‖χ.val‖^2 +
            T*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ)*B^2) →
      (∑ j, InteractionDifferential.boundaryWeight s n j*‖(ψ j).val‖) ≤
        C*(n : ℝ)^((max κ0 κ1)*ε-min s 1/2)*
          (‖χ.val‖+Real.exp (-(c/4)*(n : ℝ)^δ)*B) ∧
      (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^((max κ0 κ1)*ε)*
          (‖χ.val‖+Real.exp (-(c/4)*(n : ℝ)^δ)*B) := by
  obtain ⟨Cbig,hCbig,hlarge⟩ := rates_both_regimes_from_square_internal
    (H := ℝ) s hs hs1 D0 A T q (κ1*ε) c δ hD0 hA hT hc hδ
  -- Component norms reduce the arbitrary L² target to the same real
  -- estimate, with the reverse triangle inequality controlling the error.
  have hgeneral : ∃ Cbig : ℝ, 0 < Cbig ∧
      ∀ (n : ℕ+) (X : Type u) [MeasurableSpace X] (ν : Measure X)
        (i₀ : Fin (n : ℕ)),
        |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
        ∀ (F B : ℝ) (ψ v : Fin (n : ℕ) → Lp ℝ 2 ν), 0 ≤ F → 0 ≤ B →
        (∀ j, ‖v j‖ ≤ D0*(n : ℝ)^(κ1*ε)*
          (1+(Nat.dist j.val i₀.val : ℝ))^(if s < 1 then s-2 else -s)*F) →
        (∑ j, ‖v j‖) ≤ D0*(n : ℝ)^(κ1*ε)*F →
        ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
          A*(n : ℝ)^(2*(κ1*ε)-1)*F^2 + T*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ)*B^2 →
        (∑ j, InteractionDifferential.boundaryWeight s n j*‖ψ j‖) ≤
          Cbig*(n : ℝ)^(κ1*ε-min s 1/2)*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) ∧
        (∑ j, ‖ψ j‖) ≤ Cbig*(n : ℝ)^(κ1*ε)*(F+Real.exp (-(c/4)*(n : ℝ)^δ)*B) := by
    refine ⟨Cbig,hCbig,?_⟩
    intro n X _ ν i₀ hi₀ F B ψ v hF hB hp ht he
    let ψ' : Fin (n : ℕ) → ℝ := fun j => ‖ψ j‖
    let v' : Fin (n : ℕ) → ℝ := fun j => ‖v j‖
    have hd : ‖WithLp.toLp 2 (fun j => ψ' j-v' j)‖ ≤
        ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ := by
      rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (by
        simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (ψ j) (v j)) 2
    have he' : ‖WithLp.toLp 2 (fun j => ψ' j-v' j)‖^2 ≤
        A*(n : ℝ)^(2*(κ1*ε)-1)*F^2 + T*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ)*B^2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hd 2).trans he
    have hh := hlarge n i₀ hi₀ F B ψ' v' hF hB
      (by simpa only [ψ',v',norm_norm] using hp)
      (by simpa only [v',norm_norm] using ht) he'
    simpa only [ψ',norm_norm] using hh
  obtain ⟨D,hD,hlargeD⟩ := hgeneral
  obtain ⟨C,hC,hjoin⟩ := all_size_join_internal (n0 : ℝ) κ0 (max κ0 κ1) ε
    (min s 1/2) a0⁻¹ D (c/4) δ (Nat.cast_nonneg _) (le_max_left _ _) hε
    (by positivity) (inv_nonneg.mpr ha0.le) hD.le
  refine ⟨C,hC,?_⟩
  intro n X _ ν Q hQ M hMm hM hlower i₀ hi₀ χ ψ hψ B hbig
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  apply hjoin n ‖χ.val‖ B
    (∑ j, InteractionDifferential.boundaryWeight s n j*‖(ψ j).val‖)
    (∑ j, ‖(ψ j).val‖) hn1 (norm_nonneg _) hB
  · intro _
    have hh := (tangent_coercivity_sums_internal Q hQ n M hMm hM
      (a0*(n : ℝ)^(-(κ0*ε))) (by positivity) hlower s hs i₀ χ.val ψ hψ).2
    have heq : (a0*(n : ℝ)^(-(κ0*ε)))⁻¹ = a0⁻¹*(n : ℝ)^(κ0*ε) := by
      rw [mul_inv,← Real.rpow_neg hn.le,neg_neg]
    simpa only [heq] using hh
  · intro hsize
    obtain ⟨v,hp,ht,he⟩ := hbig hsize
    have hh := hlargeD n X ν i₀ hi₀ ‖χ.val‖ B (fun j => (ψ j).val) v
      (norm_nonneg _) hB hp ht he
    have hloss : κ1*ε ≤ (max κ0 κ1)*ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε
    have hG : 0 ≤ ‖χ.val‖+Real.exp (-(c/4)*(n : ℝ)^δ)*B := by positivity
    constructor
    · apply hh.1.trans
      gcongr
    · apply hh.2.trans
      gcongr

end BothRegimes

end Riesz2.FixedLengthDecay
