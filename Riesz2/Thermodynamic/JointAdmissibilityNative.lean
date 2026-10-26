/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityLongBounds

/-!
# Joint native physical inputs

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

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem long_range_native_physical_inputs_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) (Areq : ℝ) :
    ∀ h : ℕ,
    ∃ A K ε₀ κ γ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧ Areq ≤ A ∧
    OriginalTypicality s.val A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (n₀ : ℕ) (δ : ℝ), 2 ≤ n₀ ∧ 0 < δ ∧
      (128 : ℝ) ≤ (n₀ : ℝ)^(1-s.val/2-2*ε) ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let m := PhysicalCore.properReferencePeriod s n N
    let k := ⌊(n : ℝ)^(K*ε)⌋₊^h
    ∃ (hm : 2 ≤ (m : ℕ)) (hnm : (n : ℕ) ≤ (m : ℕ))
      (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4),
      (∀ μ : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
        PeriodizedMatrixBounds (ν := μ) s n m hm k C κ γ ε
          (InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε (K*ε) t)) ∧
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : EuclideanSpace ℝ (Fin (a+1)),
        C⁻¹*(n : ℝ)^(-κ*ε)*(∑ i, (v i)^2) ≤ ∑ i,∑ j, v i*hessianMatrix H x i j*v j) ∧
    (n₀ ≤ (n : ℕ) →
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ i j : Fin (a+1),
        |(1-t)*hessianMatrix Ky x i j+t*hessianMatrix Kz x i j|^2+
          |InterpolationMatrix.penaltyHessian n θ ε x i j|^2 ≤
          C*(n : ℝ)^C*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x)) ∧
      let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
      let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*H u.val))
      ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
      ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
      let ρ := AffineFibre.normalizedMeasure μ w h0 htop
      let ν := ρ.map (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
      IsProbabilityMeasure ν ∧
      ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
      ∃ Q : ScalarFormData ν, ∃ hQ : IsClosedScalarDirichletForm Q,
      IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε (K*ε) t P
      (∀ i j : Fin (n : ℕ), Integrable
        (fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
          β.val*(InterpolationMatrix.penaltyHessian n θ ε x.val i j+P x i j)) ν) ∧
      (∀ i j : Fin (n : ℕ), Integrable (fun x => Y x i j) ν) ∧
      (∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (j i : Fin (n : ℕ)),
        |(∫ x, φ.val x*Y x j i*ψ.val x ∂ν)+
          InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
            (j.castLE hnm) (i.castLE hnm)| ≤
          (C*(n : ℝ)^(κ*ε))*InteractionDifferential.boundaryWeight s.val n j*InteractionDifferential.boundaryWeight s.val n i*‖φ.val‖*‖ψ.val‖+
            (C*Real.exp (-c*(n : ℝ)^δ))*
              (eLpNorm (fun x => φ.val x) ∞ ν).toReal*(eLpNorm (fun x => ψ.val x) ∞ ν).toReal) ∧
      (∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (j i l : Fin (n : ℕ)),
        |(∫ x, φ.val x*ψ.val x*(Y x j i-Y x j l) ∂ν)+
          InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
            (j.castLE hnm) (i.castLE hnm) (l.castLE hnm)| ≤
          (C*(n : ℝ)^(κ*ε))*InteractionDifferential.boundaryWeight s.val n j*
            (Nat.dist i.val l.val : ℝ)*
              (min ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)
                ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ))^(-1-s.val/2)*‖φ.val‖*‖ψ.val‖+
            (C*Real.exp (-c*(n : ℝ)^δ))*
              (eLpNorm (fun x => φ.val x) ∞ ν).toReal*(eLpNorm (fun x => ψ.val x) ∞ ν).toReal)) := by
  intro h
  obtain ⟨A,K,ε₀,κ,γ,hA,hK,hε₀,hκ,hγ,hAA,htyp,hbounds⟩ :=
    InterpolationCoefficientBounds.long_range_bounds_joint hzeta hRig s Areq h
  refine ⟨A,K,ε₀,κ,γ,hA,hK,hε₀,hκ,hγ,hAA,htyp,?_⟩
  intro ε hε hsmall
  obtain ⟨n₀,δ,hn₀,hδ,hthreshold,hboundsNext⟩ := hbounds ε hε hsmall
  clear hbounds
  rename' hboundsNext => hbounds
  refine ⟨n₀,δ,hn₀,hδ,hthreshold,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,c,hC,hc,hboundsNext⟩ := hbounds βlo βhi hlo hle θ
  clear hbounds
  rename' hboundsNext => hbounds
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ a d e ha hde n N hN hNpower y z L hyL hzL hy hz Dy Dz
  obtain ⟨Ky,Kz,hKy,hKz,hky,hkz,hboundsNext⟩ :=
    hbounds β hβ a d e ha hde hN hNpower y z L hyL hzL hy hz
  clear hbounds
  rename' hboundsNext => hbounds
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht H m k
  obtain ⟨hm,hnm,hk,hkm,hmat,hcoerc,hlarge⟩ := hbounds t ht
  refine ⟨hm,hnm,hk,hkm,hmat,hcoerc,?_⟩
  intro hnlarge
  obtain ⟨hsquare,hlarge⟩ := hlarge hnlarge
  refine ⟨hsquare,?_⟩
  intro μ w
  obtain ⟨h0,htop,hLN,hprob,hforms⟩ := hlarge
  refine ⟨h0,htop,hLN,hprob,?_⟩
  intro frame
  obtain ⟨Q,hQ,hcons,hIntrinsic,hperts⟩ := hforms frame
  refine ⟨Q,hQ,hcons,hIntrinsic,?_⟩
  intro P Y
  let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
    (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
  let : IsProbabilityMeasure ν := hprob
  have htests (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i j l : Fin (n : ℕ)) :=
    hperts φ.val ψ.val (BoundedL2Pairings.memLp_top φ) (BoundedL2Pairings.memLp_top ψ) i j l
  have hHiYi := physical_entries_of_native_tests_internal β s n d e hde m hm hnm
    k θ ε (K*ε) t ν P C κ γ ε (hmat ν)
      (fun φ ψ hφ hψ i j => (hperts φ ψ hφ hψ i j i).choose)
  have hperm (a wi wj f g e p q : ℝ) :
      a*wi*wj*f*g+e*(p*q) = a*wj*wi*f*g+e*p*q := by ring
  have hiperm (a dist w r f g e p q : ℝ) :
      a*(dist*w*r)*f*g+e*(p*q) = a*w*dist*r*f*g+e*p*q := by ring
  have hrows := native_row_bounds_internal β s n d e hde m hm hnm
    k hk hkm θ ε (K*ε) t ν Q hQ P (C*(n : ℝ)^(κ*ε)) (C*Real.exp (-c*(n : ℝ)^δ))
      (by
        intro φ ψ i j l
        obtain ⟨hp,hd,hpbound,hdbound⟩ := htests φ ψ i j l
        refine ⟨hp,hd,hpbound.trans_eq ?_,hdbound.trans_eq ?_⟩
        · simp only [InteractionDifferential.boundaryWeight_long s.property.2]
          apply hperm
        · simp only [InteractionDifferential.boundaryWeight_long s.property.2,Nat.cast_min]
          apply hiperm)
  refine ⟨?_,hHiYi.2,?_,?_⟩
  · intro i j
    simpa only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul] using hHiYi.1 i j
  · exact hrows.1
  · exact hrows.2

end Riesz2.FixedLengthDecay
