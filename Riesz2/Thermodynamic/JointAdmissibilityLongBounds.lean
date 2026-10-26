/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibility

/-!
# Joint long-range coefficient bounds

Strengthened interfaces for Proposition 6.6: the same structural choice retains
original-law exterior typicality throughout the analytic chain.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
open Riesz2.JointAdmissibility

namespace Riesz2.InterpolationCoefficientBounds

/-- See Subsection 6.1 of the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem long_range_bounds_joint (hzeta : External.PeriodicZeta)
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
      IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε (K*ε) t P
      let wgt : Fin (n : ℕ) → ℝ := fun i => (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)
      let inc : Fin (n : ℕ) → Fin (n : ℕ) → Fin (n : ℕ) → ℝ := fun j i l =>
        (Nat.dist i.val l.val : ℝ)*wgt j*
          (min (min (i.val+1) ((n : ℕ)-i.val)) (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2)
      ∀ φ ψ : Lp ℝ 2 ν, MemLp (φ : _ → ℝ) ∞ ν → MemLp (ψ : _ → ℝ) ∞ ν →
      ∀ i j l : Fin (n : ℕ),
      ∃ hp : Integrable (matrixFieldPair Y (Pi.single j φ) (Pi.single i ψ)) ν,
      ∃ hd : Integrable (matrixFieldPair Y (Pi.single j φ)
        (fun q => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q-(Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε (K*ε) t
        ν Q hQ P (Pi.single j φ) (Pi.single i ψ) hp| ≤
        C*(n : ℝ)^(κ*ε)*wgt i*wgt j*‖φ‖*‖ψ‖+
          C*Real.exp (-c*(n : ℝ)^δ)*
            ((eLpNorm (φ : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ : _ → ℝ) ∞ ν).toReal) ∧
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε (K*ε) t
        ν Q hQ P (Pi.single j φ)
        (fun q => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q-(Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q) hd| ≤
        C*(n : ℝ)^(κ*ε)*inc j i l*‖φ‖*‖ψ‖+
          C*Real.exp (-c*(n : ℝ)^δ)*
            ((eLpNorm (φ : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ : _ → ℝ) ∞ ν).toReal)) := by
  intro h
  obtain ⟨A,K,εbase,hA,hK,hεbase,hAA,htyp,hlocal⟩ :=
    InterpolantLocalLaws.joint_local_laws hRig s.val s.property.1 (ne_of_lt s.property.2) Areq
  obtain ⟨ρ,hρ,hprofiles⟩ := InterpolationBoundaryBridge.physical_good_profiles_ae_internal s K (by linarith)
  obtain ⟨κT,hκT,hpert⟩ := InterpolationPerturbation.perturbation_bounds_from_profiles_internal hzeta s h K ρ hρ
  let κM := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
  let κ := max (κM*K) (max κT (s.val+2))
  let γ := ((h : ℝ)+1)*K
  let ε₀ := min εbase (min (4*K*((h : ℝ)+1))⁻¹ ((1-s.val/2)/4))
  have hK0 : 0 < K := by linarith
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hgap : 0 < 1-s.val/2 := by linarith [s.property.2]
  have hε₀ : 0 < ε₀ := lt_min hεbase (lt_min (by positivity) (by positivity))
  have hκ : 0 < κ := lt_of_lt_of_le hκT ((le_max_left _ _).trans (le_max_right _ _))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨A,K,ε₀,κ,γ,hA,hK,hε₀,hκ,hγ,hAA,htyp.restrict (min_le_left _ _),fun ε hε hεsmall => ?_⟩
  have hεbase' : ε < εbase := hεsmall.trans_le (min_le_left _ _)
  have hεcut : ε ≤ (4*K*((h : ℝ)+1))⁻¹ :=
    (hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεgap : ε < (1-s.val/2)/4 :=
    hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hσε : s.val/2+2*ε < 1 := by linarith
  have hσε' : min s.val 1/2+2*ε < 1 := by rw [min_eq_left s.property.2.le]; exact hσε
  obtain ⟨δ,hδ,hlocalNext⟩ := hlocal ε hε hεbase'
  clear hlocal
  rename' hlocalNext => hlocal
  obtain ⟨ng,hng,hprofilesNext⟩ := hprofiles ε hε hσε
  clear hprofiles
  rename' hprofilesNext => hprofiles
  obtain ⟨ns,hns,hsquare⟩ := whole_simplex_bound s.val ε s.property.1 hε.le hσε'
  obtain ⟨nc,hnc,hC5⟩ := InterpolationCoefficients.complement_threshold (s.val/2) ε hσε
  let n₀ := max ng (max ns nc)
  refine ⟨n₀,δ,hng.trans (le_max_left _ _),hδ,hC5 n₀ ((le_max_right _ _).trans (le_max_right _ _)),?_⟩
  intro βlo βhi hlo hle θ
  have hhi : 0 < βhi := hlo.trans_le hle
  obtain ⟨D,hD,hsq⟩ := hsquare θ
  obtain ⟨Ag,hAg,hprofilesNext⟩ := hprofiles βhi hhi
  clear hprofiles
  rename' hprofilesNext => hprofiles
  obtain ⟨Cl,cl,hCl,hcl,hlocalNext⟩ := hlocal βlo βhi hlo hle θ
  clear hlocal
  rename' hlocalNext => hlocal
  obtain ⟨Cp,hCp,hpertNext⟩ := hpert ε δ hε.le hδ βhi Ag D Cl cl hhi hAg hD hCl hcl
  clear hpert
  rename' hpertNext => hpert
  obtain ⟨Cm,hCm,hmat⟩ := InterpolationMatrix.matrix_bounds s θ h
  let b := min 1 (s.val*(s.val+1))
  have hb : 0 < b := lt_min zero_lt_one (by have := s.property.1; positivity)
  let C := 1+Cm+Cp+D+b⁻¹
  have hC : 0 < C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCmC : Cm ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCpC : Cp ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hDC : D ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCb : C⁻¹ ≤ b := (inv_le_comm₀ hC hb).mpr (by dsimp [C]; linarith [inv_pos.mpr hb])
  refine ⟨C,cl/4,hC,by positivity,?_⟩
  intro β hβ a d e ha hde n N hN hNpower y z L hyL hzL hy hz Dy Dz
  have hycompat : (∑ k,y.val k)+L = ((d+1+a : ℕ)+1 : ℝ) := by linarith
  have hzcompat : (∑ k,z.val k)+L = ((e+1+a : ℕ)+1 : ℝ) := by linarith
  obtain ⟨Ky,hKy,hky,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofLong β s) (d+1) a (by omega) y
  obtain ⟨Kz,hKz,hkz,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofLong β s) (e+1) a (by omega) z
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht H m k
  have hm : 2 ≤ (m : ℕ) := by
    have hh := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
    change 2 ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
    have := n.pos
    omega
  have hnm : (n : ℕ) ≤ (m : ℕ) := by
    have hh := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
    change (n : ℕ) ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
    omega
  have hperiod : (d+1+a).succPNat = N := by apply PNat.eq; dsimp [N,n]; omega
  have hperiodR : ((d+1+a : ℕ)+1 : ℝ) = ((n+d : ℕ)+1 : ℝ) := by
    exact_mod_cast (show d+1+a+1 = (n : ℕ)+d+1 by dsimp [n]; omega)
  have hn2 : 2 ≤ (n : ℕ) := by dsimp [n]; omega
  have hmn : 2*(n : ℕ) ≤ (m : ℕ) := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
  have hη : 0 ≤ K*ε := by positivity
  have hsmall : ((h : ℝ)+1)*(K*ε) ≤ 1/4 := by
    have hpos : 0 < 4*K*((h : ℝ)+1) := by positivity
    have hh := mul_le_mul_of_nonneg_right hεcut hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at hh
    nlinarith only [hh]
  have hηa : K*ε ≤ 1-s.val/2 := by nlinarith only [hsmall,mul_nonneg hh0 hη,s.property.2]
  obtain ⟨hk,hkm4⟩ := AuxiliaryMean.interpolation_cutoff_bounds_internal n m hn2 hmn (K*ε) h hη (by nlinarith only [hsmall,hη])
  have hkm : k ≤ (m : ℕ)/4 := by dsimp [k]; omega
  refine ⟨hm,hnm,hk,hkm,?_,?_,?_⟩
  · intro μ
    apply PeriodizedMatrixBoundsMonotone.of_losses_le s n m hm k (by linarith : 0 < Cm) hCmC
      (show κM*(K*ε) ≤ κ*ε from by
        have hh : κM*K ≤ κ := le_max_left _ _
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hε.le)
      (show ((h : ℝ)+1)*(K*ε) ≤ γ*ε from by dsimp [γ]; ring_nf; exact le_rfl)
    exact hmat β n d e hde hN m hm hmn
      (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).2.1
      (InterpolationMatrix.properReferencePeriod_scale s n N (by omega) hNpower)
      ε (K*ε) t hε.le hη hηa ht.1 ht.2 hkm μ
  · intro x hx v
    have hbnd := coercivity_internal (ofLong β s) θ ε hε.le (d+1) (e+1) a ha y z L hyL hzL Ky Kz hky hkz t ht x hx v
    have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast n.pos)
      (show -κ*ε ≤ -(s.val+2)*ε by
        have hle := (le_max_right κT (s.val+2)).trans (le_max_right (κM*K) (max κT (s.val+2)))
        nlinarith only [mul_le_mul_of_nonneg_right hle hε.le])
    have hl := mul_le_mul hCb hp (by positivity) hb.le
    exact (mul_le_mul_of_nonneg_right hl (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))).trans
      (by simpa only [ofLong,n,Nat.succPNat_coe,Nat.cast_succ] using hbnd)
  · intro hlarge
    have hng' : ng ≤ a+1 := (le_max_left _ _).trans hlarge
    have hns' : ns ≤ a+1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
    have hNy : 4*(a+1) ≤ d+1+a+1 := by dsimp [N,n] at hN; omega
    have hNz : 4*(a+1) ≤ e+1+a+1 := by omega
    have hbnd := hsq (ofLong β s) rfl (d+1) (e+1) a hns' hNy hNz y z hy.1 hz.1 L hyL hzL Ky Kz hky hkz t ht
    have hsquare' (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
        (hx : x.val ∈ AffineSimplex.massSimplex a L) (i j : Fin (n : ℕ)) :
        |(1-t)*hessianMatrix Ky x.val i j+t*hessianMatrix Kz x.val i j|^2+
          |InterpolationMatrix.penaltyHessian n θ ε x.val i j|^2 ≤
          D*(n : ℝ)^D*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x.val) := by
      simpa only [InterpolationMatrix.penaltyHessian,n,Nat.succPNat_coe,Nat.cast_succ] using hbnd x.val hx i j
    refine ⟨?_,?_⟩
    · intro x hx i j
      let q : AffineSimplex.chartDomain n ((n+d : ℕ)+1) :=
        ⟨x,hx.1,hx.2.trans_lt (by rw [← hperiodR]; exact InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y hycompat)⟩
      exact (hsquare' q hx i j).trans (by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
        have hw : 0 ≤ InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x) :=
          zero_le_one.trans (InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun i => (hx.1 i).le))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hDC (Real.rpow_le_rpow_of_exponent_le hn1 hDC) (by positivity) hC.le) hw)
    · intro μ w
      have hLN : L < ((n+d : ℕ)+1 : ℝ) := by
        rw [←hperiodR]
        exact InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y hycompat
      obtain ⟨h0,htop,hprob,hforms⟩ := physical_form_internal (ofLong β s) θ ε (d+1) (e+1) a
        (by omega) (by omega) y z L hyL hzL Ky Kz hky hkz _ hperiodR hLN t ht
      refine ⟨h0,htop,hLN,?_⟩
      let ρlaw := AffineFibre.normalizedMeasure μ w h0 htop
      let ν := ρlaw.map (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
      have : IsProbabilityMeasure ν := hprob
      refine ⟨hprob,?_⟩
      intro frame
      obtain ⟨Q,hQ,hcons,hIntrinsic⟩ := hforms frame
      refine ⟨Q,hQ,hcons,hIntrinsic,?_⟩
      intro P Y wgt inc φ ψ hφ hψ i j l
      have hsupport := common_fibre_support_internal a d e L y z hyL hzL hLN ρlaw
      have hg := hprofiles β hβ.2 a d e (d+1) (e+1) hde (by omega) (by omega) hng' hNy
        m hm hnm k hmn θ t ht y z hy.1 hz.1 Ky Kz hky hkz ν hsupport
      have hsquareAE : ∀ᵐ x ∂ν.restrict (InterpolationMatrix.goodSet s n d (K*ε))ᶜ,
          ∀ i j, |P x i j|^2+|InterpolationMatrix.penaltyHessian n θ ε x.val i j|^2 ≤
            D*(n : ℝ)^D*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x.val) := by
        filter_upwards [ae_restrict_of_ae hsupport] with x hx i j
        exact hsquare' x (hyL ▸ hx.1) i j
      have hpowerY : ((a+1 : ℕ) : ℝ)^(2/s.val) ≤ ((d+1+a : ℕ)+1 : ℝ) := by
        rw [hperiodR]
        simpa only [N,n,Nat.succPNat_coe,Nat.cast_succ] using hNpower
      obtain ⟨_,hlocal'⟩ := hlocal (ofLong β s) rfl hβ.1 hβ.2 (d+1) (e+1) a (by omega) (by omega) ha hNy
        (by omega) hpowerY
      obtain ⟨h0',htop',_,hbad,_,_⟩ := hlocal' L y z hycompat hzcompat hy hz t ht.1 ht.2
      have htail : (∫⁻ x in (InterpolationMatrix.goodSet s n d (K*ε))ᶜ,
          ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x.val)) ∂ν) ≤
          ENNReal.ofReal (Cl*Real.exp (-cl*(n : ℝ)^δ)) := by
        dsimp only [ν]
        erw [InterpolationTransport.weighted_tail_eq s a d L (K*ε) hLN ρlaw]
        simp only [AffineFibre.normalizedMeasure_eq_smul] at hbad ⊢
        simp_rw [←hky,←hkz] at hbad
        have hperiodEvent : (d+1+a).succPNat = (a+1+d).succPNat := by
          apply PNat.eq
          simp only [Nat.succPNat_coe]
          omega
        simpa only [ρlaw,w,H,μ,n,Nat.succPNat_coe,Nat.cast_succ,ofLong,
          AffineFibre.normalizedMeasure_eq_smul,hperiodEvent] using hbad
      have hP (i j) : Measurable (fun x => P x i j) :=
        (((DifferentiatedPoisson.measurable_hessian_entries (V := Ky) i j).comp measurable_subtype_coe).const_mul (1-t)).add
          (((DifferentiatedPoisson.measurable_hessian_entries (V := Kz) i j).comp measurable_subtype_coe).const_mul t)
      obtain ⟨hp,hd,hpoint,hinc⟩ := hpert β hβ.2 n d e hde m hm hnm hk hkm θ t ν Q hQ P hP hg hsquareAE htail
        φ ψ (eLpNorm (φ : _ → ℝ) ∞ ν).toReal (eLpNorm (ψ : _ → ℝ) ∞ ν).toReal
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        (InterpolationPerturbation.essential_scalar_bound_internal φ hφ)
        (InterpolationPerturbation.essential_scalar_bound_internal ψ hψ) i j l
      refine ⟨hp,hd,hpoint.trans ?_,hinc.trans ?_⟩ <;>
        dsimp only [κ] <;> gcongr <;> first
        | exact_mod_cast n.pos
        | exact (le_max_left κT (s.val+2)).trans (le_max_right (κM*K) (max κT (s.val+2)))

end Riesz2.InterpolationCoefficientBounds
