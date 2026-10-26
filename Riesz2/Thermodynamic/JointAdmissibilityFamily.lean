/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityChoice

/-!
# Joint comparison families

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
theorem long_common_physical_family_internal_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1) (hsl : s < 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ Ct ct Cd cd : ℝ, 0 < Ct ∧ 0 < ct ∧ 0 < Cd ∧ 0 < cd ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ Bcarrier : ℝ, ∃ hLN : L < Bcarrier,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
      (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L _ hLN frame (ν t) (Q t)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∫⁻ x in {x | WithLp.ofLp (g x) ∉ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)},
        ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
          (WithLp.ofLp (g x))) ∂μ t) ≤ ENNReal.ofReal (Ct*Real.exp (-ct*(a+1 : ℝ)^δ))) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin (a+1),
      |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t),
      (∃ ψ : Fin (a+1) → (Q t).1, WeightedWeakSolution (Q t)
        (fun x => hessianMatrix (H t) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s a.succPNat l*‖(ψ l).val‖) ≤
          Cd*(a+1 : ℝ)^(κ*ε-min s 1/2)*
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ Cd*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  let s₀ : Riesz1.RieszExponent := ⟨s,hs,hsl⟩
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,_,hj,hd⟩ :=
    long_range_common_choice_internal_joint hzeta hRig s₀
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,?_⟩
  intro ε hε hε₀'
  obtain ⟨δj,hδj,hj'⟩ := hj ε hε hε₀'
  obtain ⟨δd,hδd,hd'⟩ := hd ε hε hε₀'
  refine ⟨min δj δd,lt_min hδj hδd,?_⟩
  intro βlo βhi hβlo hβorder θ
  obtain ⟨Ct,ct,hCt,hct,hjet⟩ := hj' βlo βhi hβlo hβorder θ
  obtain ⟨Cd,cd,hCd,hcd,hdec⟩ := hd' βlo βhi hβlo hβorder θ
  refine ⟨Ct,ct,Cd,cd,hCt,hct,hCd,hcd,?_⟩
  intro p hps hβ hβhi a d e ha hsize hde hpower L hL y z hy hz hyL hzL
  let β : InverseTemperature := ⟨p.val.1,p.property.1⟩
  have hp : ofLong β s₀ = p := by
    apply Subtype.ext
    exact Prod.ext rfl hps.symm
  have hy' := hy
  have hz' := hz
  rw [← hp] at hy' hz'
  obtain ⟨Ky,Kz,hKy,hKz,hLN,hfam⟩ := hdec β ⟨hβ,hβhi⟩ a d e ha hde (by omega)
    (by simpa only [s₀,Nat.cast_add,Nat.cast_one,add_comm,add_left_comm,add_assoc] using hpower)
    y z L hyL hzL hy' hz'
  rw [hp] at hKy hKz
  refine ⟨Ky,Kz,hKy,hKz,_,hLN,?_⟩
  intro frame H U g
  obtain ⟨μ,hμ,hV,Q,hν,hQ,hform,hest⟩ := hfam frame
  let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
    (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
  refine ⟨μ,hμ,hV,Q,hν,hQ,hform,?_,?_⟩
  · intro t ht
    obtain ⟨M,_,_,hM⟩ := frame_matrix_internal a frame
    have hh := (hjet p hps hβ hβhi a d e ha hsize hde hpower L hL y z
      hy hz hyL hzL Ky Kz hKy hKz t ht frame M hM (μ t) (hV t ht)).1
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hCt.le
    exact exponential_tail_power_mono_internal (a+1) _ _ ct (by exact_mod_cast Nat.le_add_left 1 a)
      (min_le_left _ _) hct.le
  · intro t ht i hi χ
    refine ⟨(hest t ht).1 i χ.val |>.exists,?_⟩
    intro ψ hψ
    have hh := (hest t ht).2 i hi χ ψ hψ
    rw [min_eq_left hsl.le]
    have he := exponential_tail_power_mono_internal (a+1) (min δj δd) δd cd
      (by exact_mod_cast Nat.le_add_left 1 a) (min_le_right _ _) hcd.le
    have hr := add_le_add (le_refl ‖χ.val‖) (mul_le_mul_of_nonneg_right he (show 0 ≤ (eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal from ENNReal.toReal_nonneg))
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left hr (by positivity)),
      hh.2.trans (mul_le_mul_of_nonneg_left hr (by positivity))⟩

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem short_common_physical_family_internal_joint (_hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (_hs : 0 < s) (hs1 : s ≠ 1) (hsl : ¬ s < 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ Ct ct Cd cd : ℝ, 0 < Ct ∧ 0 < ct ∧ 0 < Cd ∧ 0 < cd ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ Bcarrier : ℝ, ∃ hLN : L < Bcarrier,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
      (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L _ hLN frame (ν t) (Q t)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∫⁻ x in {x | WithLp.ofLp (g x) ∉ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)},
        ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
          (WithLp.ofLp (g x))) ∂μ t) ≤ ENNReal.ofReal (Ct*Real.exp (-ct*(a+1 : ℝ)^δ))) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin (a+1),
      |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t),
      (∃ ψ : Fin (a+1) → (Q t).1, WeightedWeakSolution (Q t)
        (fun x => hessianMatrix (H t) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s a.succPNat l*‖(ψ l).val‖) ≤
          Cd*(a+1 : ℝ)^(κ*ε-min s 1/2)*
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ Cd*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  have hsg : 1 < s := lt_of_le_of_ne (le_of_not_gt hsl) (Ne.symm hs1)
  let s₀ : ShortExponent := ⟨s,hsg⟩
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,_,hj,hd⟩ :=
    short_range_common_choice_internal_joint hRig s₀
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,?_⟩
  intro ε hε hε₀'
  obtain ⟨δj,hδj,hj'⟩ := hj ε hε hε₀'
  obtain ⟨δd,hδd,hd'⟩ := hd ε hε hε₀'
  refine ⟨min δj δd,lt_min hδj hδd,?_⟩
  intro βlo βhi hβlo hβorder θ
  obtain ⟨Ct,ct,hCt,hct,hjet⟩ := hj' βlo βhi hβlo hβorder θ
  obtain ⟨Cd,cd,hCd,hcd,hdec⟩ := hd' βlo βhi hβlo hβorder θ
  refine ⟨Ct,ct,Cd,cd,hCt,hct,hCd,hcd,?_⟩
  intro p hps hβ hβhi a d e ha hsize hde hpower L hL y z hy hz hyL hzL
  let β : InverseTemperature := ⟨p.val.1,p.property.1⟩
  have hp : ofShort β s₀ = p := by
    apply Subtype.ext
    exact Prod.ext rfl hps.symm
  have hy' := hy
  have hz' := hz
  rw [← hp] at hy' hz'
  obtain ⟨Ky,Kz,hKy,hKz,hLN,hfam⟩ := hdec β ⟨hβ,hβhi⟩ a d e ha hde hsize
    (by simpa only [Nat.cast_add,Nat.cast_one] using hpower) y z L hyL hzL hy' hz'
  rw [hp] at hKy hKz
  refine ⟨Ky,Kz,hKy,hKz,_,hLN,?_⟩
  intro frame H U g
  obtain ⟨μ,hμ,hV,Q,hν,hQ,hform,hest⟩ := hfam frame
  let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
    (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
  refine ⟨μ,hμ,hV,Q,hν,hQ,hform,?_,?_⟩
  · intro t ht
    obtain ⟨M,_,_,hM⟩ := frame_matrix_internal a frame
    have hh := (hjet p hps hβ hβhi a d e ha hsize hde hpower L hL y z
      hy hz hyL hzL Ky Kz hKy hKz t ht frame M hM (μ t) (hV t ht)).1
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hCt.le
    exact exponential_tail_power_mono_internal (a+1) _ _ ct (by exact_mod_cast Nat.le_add_left 1 a)
      (min_le_left _ _) hct.le
  · intro t ht i hi χ
    refine ⟨((hest t ht) i hi χ).1.exists,?_⟩
    intro ψ hψ
    have hh := ((hest t ht) i hi χ).2 ψ hψ
    rw [min_eq_right hsg.le]
    have he := exponential_tail_power_mono_internal (a+1) (min δj δd) δd cd
      (by exact_mod_cast Nat.le_add_left 1 a) (min_le_right _ _) hcd.le
    have hr := add_le_add (le_refl ‖χ.val‖) (mul_le_mul_of_nonneg_right he (show 0 ≤ (eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal from ENNReal.toReal_nonneg))
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left hr (by positivity)),
      hh.2.trans (mul_le_mul_of_nonneg_left hr (by positivity))⟩

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem common_physical_family_internal_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ Ct ct Cd cd : ℝ, 0 < Ct ∧ 0 < ct ∧ 0 < Cd ∧ 0 < cd ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ Bcarrier : ℝ, ∃ hLN : L < Bcarrier,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
      (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L _ hLN frame (ν t) (Q t)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∫⁻ x in {x | WithLp.ofLp (g x) ∉ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)},
        ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
          (WithLp.ofLp (g x))) ∂μ t) ≤ ENNReal.ofReal (Ct*Real.exp (-ct*(a+1 : ℝ)^δ))) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin (a+1),
      |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t),
      (∃ ψ : Fin (a+1) → (Q t).1, WeightedWeakSolution (Q t)
        (fun x => hessianMatrix (H t) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s a.succPNat l*‖(ψ l).val‖) ≤
          Cd*(a+1 : ℝ)^(κ*ε-min s 1/2)*
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ Cd*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  by_cases hsl : s < 1
  · exact long_common_physical_family_internal_joint hzeta hRig s hs hs1 hsl
  · exact short_common_physical_family_internal_joint hzeta hRig s hs hs1 hsl

end Riesz2.CompatibleComparison
