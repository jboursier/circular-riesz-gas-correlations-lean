/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityShortDecay

/-!
# Joint physical time families

Strengthened interfaces for Proposition 6.6: the same structural choice retains
original-law exterior typicality throughout the analytic chain.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
open Riesz2.JointAdmissibility

namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem long_range_decay_time_family_internal_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) (Areq : ℝ) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ Areq ≤ A ∧
    OriginalTypicality s.val A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a), d ≤ e →
      4*(a+1) ≤ (a+1+d)+1 →
      (a+1 : ℝ)^(2/s.val) ≤ ((a+1+d : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
      InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a (by omega) θ ε A K z →
    let N : ℝ := ((a+1+d : ℕ)+1 : ℝ)
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ hLN : L < N,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => β.val*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame (ν t) (Q t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ (i : Fin (a+1)) (χ : Lp ℝ 2 (ν t)), ∃! ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ else 0) ψ) ∧
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t), ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-s.val/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hAA,htyp,hdec⟩ :=
    FixedLengthDecay.long_range_fixed_length_decay_joint hzeta hRig s Areq
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hAA,htyp,?_⟩
  intro ε hε hsmall
  obtain ⟨δ,hδ,hdec⟩ := hdec ε hε hsmall
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz N
  obtain ⟨Ky,Kz,_hKys,_hKzs,hKy,hKz,hdec⟩ :=
    hdec β hβ a d e ha hde hsize (by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hpower) y z L hyL hzL hy hz
  have hL : 0 < L := by linarith only [y.property.2,hyL]
  have hLN : L < N := by
    have h := InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y (by linarith only [hyL])
    dsimp only [N]
    simp only [Nat.cast_add,Nat.cast_one] at h ⊢
    linarith only [h]
  refine ⟨Ky,Kz,hKy,hKz,hLN,?_⟩
  intro frame H U g j
  let P := (fun (t : ℝ) (ν : Measure (AffineSimplex.chartDomain (a+1) N))
      (Q : ScalarFormData ν) =>
      (∀ (i : Fin (a+1)) (χ : Lp ℝ 2 ν), ∃! ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ else 0) ψ) ∧
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule ν, ∀ ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-s.val/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal))
  refine physical_certificate_time_family_internal (ofLong β s) a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz N hLN frame
    P ?_
  intro t ht
  obtain ⟨h0,htop,hLN',_hprob,hforms⟩ := hdec t ht
  obtain ⟨Q,hclosed,_hcons,hintr,hsol,hbound⟩ := hforms frame
  let σ : Measure (AffineSimplex.massSimplex a L) :=
    (AffineSimplex.simplexVolume a L).comap Subtype.val
  let w₀ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
    (Real.exp (-β.val*((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+
      θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹)))+(1-t)*Ky u.val+t*Kz u.val)))
  let w₁ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-H t u.val))
  have hw : w₁ = w₀ := by funext u; simp only [w₁,w₀,H,neg_mul]
  have h01 : (∫⁻ u,w₁ u ∂σ) ≠ 0 := by rw [hw]; exact h0
  have ht1 : (∫⁻ u,w₁ u ∂σ) ≠ ⊤ := by rw [hw]; exact htop
  refine ⟨h01,ht1,?_⟩
  have he : AffineFibre.normalizedMeasure σ w₁ h01 ht1 =
      AffineFibre.normalizedMeasure σ w₀ h0 htop := by congr 1
  have heν := congrArg (Measure.map (InterpolationTransport.inclusion a L N hLN)) he
  let R := fun ν : Measure (AffineSimplex.chartDomain (a+1) N) =>
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q ∧ P t ν Q
  have hf : R ((AffineFibre.normalizedMeasure σ w₀ h0 htop).map
      (InterpolationTransport.inclusion a L N hLN)) := by
    refine ⟨Q,hclosed,hintr,?_⟩
    simpa only [P,H,Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using And.intro hsol hbound
  exact (congrArg R heν).mpr hf

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem short_range_decay_time_family_internal_joint (hRig : External.LongRangeRigidityLocallyUniform) (s : ShortExponent) (Areq : ℝ) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ Areq ≤ A ∧
    OriginalTypicality s.val A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a), d ≤ e →
      4*(a+1) ≤ (d+1+a)+1 →
      (a+1 : ℝ)^(2/s.val) ≤ ((d+1+a : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
      InterpolantLocalLaws.admissibleExterior (ofShort β s) (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior (ofShort β s) (e+1) a (by omega) θ ε A K z →
    let N : ℝ := ((d+1+a : ℕ)+1 : ℝ)
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy (ofShort β s) (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy (ofShort β s) (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ hLN : L < N,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) =>
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (fun x => β.val*H t (g x))) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame (ν t) (Q t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t),
      (∃! ψ : Fin (a+1) → (Q t).1, WeightedWeakSolution (Q t)
        (fun x => hessianMatrix (fun v => β.val*H t v) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (fun v => β.val*H t v) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-1/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hAA,htyp,hdec⟩ :=
    FixedLengthDecay.short_fixed_length_decay_joint hRig s Areq
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hAA,htyp,?_⟩
  intro ε hε hsmall
  obtain ⟨δ,hδ,hdec⟩ := hdec ε hε hsmall
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz N
  obtain ⟨Ky,Kz,_hKys,_hKzs,hKy,hKz,hdec⟩ :=
    hdec β hβ a (d+1) (e+1) ha (by omega) (by omega) (by omega) hsize
      (by simpa only [Nat.cast_add,Nat.cast_one] using hpower) y z L hyL hzL hy hz
  have hL : 0 < L := by linarith only [y.property.2,hyL]
  have hLN : L < N := by
    have h := InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y (by linarith only [hyL])
    dsimp only [N]
    simp only [Nat.cast_add,Nat.cast_one] at h ⊢
    linarith only [h]
  refine ⟨Ky,Kz,hKy,hKz,hLN,?_⟩
  intro frame H U g j
  let P := (fun (t : ℝ) (ν : Measure (AffineSimplex.chartDomain (a+1) N))
      (Q : ScalarFormData ν) =>
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
      (∃! ψ : Fin (a+1) → Q.1, WeightedWeakSolution Q
        (fun x => hessianMatrix (fun v => β.val*H t v) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q (fun x => hessianMatrix (fun v => β.val*H t v) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-1/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal))
  refine physical_certificate_time_family_internal (ofShort β s) a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz N hLN frame
    P ?_
  intro t ht
  obtain ⟨h0,htop,_hprob,hforms⟩ := hdec t ht
  obtain ⟨Q,hclosed,_hcons,hintr,hbound⟩ := hforms frame
  let σ : Measure (AffineSimplex.massSimplex a L) :=
    (AffineSimplex.simplexVolume a L).comap Subtype.val
  let w₀ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
    (Real.exp (-β.val*((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+
      θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹)))+(1-t)*Ky u.val+t*Kz u.val)))
  let w₁ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(β.val*H t u.val)))
  have hw : w₁ = w₀ := by funext u; simp only [w₁,w₀,H,neg_mul]
  have h01 : (∫⁻ u,w₁ u ∂σ) ≠ 0 := by rw [hw]; exact h0
  have ht1 : (∫⁻ u,w₁ u ∂σ) ≠ ⊤ := by rw [hw]; exact htop
  refine ⟨h01,ht1,?_⟩
  have he : AffineFibre.normalizedMeasure σ w₁ h01 ht1 =
      AffineFibre.normalizedMeasure σ w₀ h0 htop := by congr 1
  have heν := congrArg (Measure.map (InterpolationTransport.inclusion a L N hLN)) he
  let R := fun ν : Measure (AffineSimplex.chartDomain (a+1) N) =>
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q ∧ P t ν Q
  have hf : R ((AffineFibre.normalizedMeasure σ w₀ h0 htop).map
      (InterpolationTransport.inclusion a L N hLN)) := by
    refine ⟨Q,hclosed,hintr,?_⟩
    let ν := (AffineFibre.normalizedMeasure σ w₀ h0 htop).map
      (InterpolationTransport.inclusion a L N hLN)
    have hscale : (fun x : AffineSimplex.chartDomain (a+1) N =>
        hessianMatrix (fun v => β.val*H t v) x.val) =ᵐ[ν]
        (fun x => β.val • hessianMatrix (H t) x.val) := by
      apply (InterpolationTransport.measurableEmbedding_inclusion a L N hLN).ae_map_iff.mpr
      exact ae_of_all _ (fun u => physical_interpolant_hessian_scale_internal
        (ofShort β s) a d e θ ε L y z hyL hzL Ky Kz _hKys _hKzs t u.val u.property)
    intro i hi χ
    obtain ⟨hsol,hest⟩ := hbound i hi χ
    have heq (ψ : Fin (a+1) → Q.1) := MatrixFieldTransport.weak_congr Q hscale
      (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ
    refine ⟨?_,fun ψ hψ => hest ψ ((heq ψ).mp hψ)⟩
    obtain ⟨ψ,hψ,huniq⟩ := hsol
    exact ⟨ψ,(heq ψ).mpr hψ,fun u hu => huniq u ((heq u).mp hu)⟩
  exact (congrArg R heν).mpr hf

end Riesz2.CompatibleComparison
