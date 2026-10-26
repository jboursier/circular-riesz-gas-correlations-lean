/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityLongDecay

/-!
# Joint short-range fixed-length decay

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
theorem short_fixed_length_decay_joint (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ShortExponent) (Areq : ℝ) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ Areq ≤ A ∧
    OriginalTypicality s.val A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a e f : ℕ) (_ha : 1 ≤ a) (he : 1 ≤ e) (hf : 1 ≤ f),
      e ≤ f → 4*(a+1) ≤ e+a+1 → (a+1 : ℝ)^(2/s.val) ≤ ((e+a : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
      (z : AffineSimplex.chartDomain f ((f+a : ℕ)+1)) (L : ℝ),
    ∀ (hyL : ((e+a : ℕ)+1 : ℝ)-∑ k,y.val k = L)
      (_hzL : ((f+a : ℕ)+1 : ℝ)-∑ k,z.val k = L),
    InterpolantLocalLaws.admissibleExterior (ofShort β s) e a he θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofShort β s) f a hf θ ε A K z →
    let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
    let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (e+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (f+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy),Ky u = physicalAmbientGapEnergy (ofShort β s) (e+a).succPNat ⟨Y u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz),Kz u = physicalAmbientGapEnergy (ofShort β s) (f+a).succPNat ⟨Z u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k,(θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*Ht u.val))
    ∃ (h0 : (∫⁻ u,w u ∂μ) ≠ 0) (htop : (∫⁻ u,w u ∂μ) ≠ ⊤),
    let hLN := InterpolationTransport.compatible_mass_lt a e he L y (by linarith only [hyL])
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map (InterpolationTransport.inclusion a L ((e+a : ℕ)+1) hLN)
    let H := fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) => β.val • hessianMatrix Ht x.val
    IsProbabilityMeasure ν ∧
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L _ hLN frame ν Q ∧
    ∀ i₀ : Fin (a+1), |(i₀.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
    ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
      (∃! ψ : Fin (a+1) → Q.1,WeightedWeakSolution Q H (zeroSumComponents (Fin (a+1)))
        (fun i => if i = i₀ then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q H (zeroSumComponents (Fin (a+1)))
          (fun i => if i = i₀ then χ.val else 0) ψ →
        let B := (eLpNorm (χ.val : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) → ℝ) ∞ ν).toReal
        (∑ j,InteractionDifferential.boundaryWeight s.val a.succPNat j*‖(ψ j).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-1/2)*(‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*B) ∧
        (∑ j,‖(ψ j).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*(‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*B) := by
  obtain ⟨A,K,εbase,hA,hK,hεbase,hAA,htyp,hlocal⟩ := InterpolantLocalLaws.joint_local_laws hRig s.val
    (by linarith [s.property]) (ne_of_gt s.property) Areq
  obtain ⟨Ce,κe,hCe,hκe,hentry⟩ := InterpolationCoefficientBounds.interaction_entry_internal s.val K
    (by linarith [s.property]) (by linarith)
  let q := max (s.val+2) (max (4*K) κe)
  have hq : 0 ≤ q := by dsimp only [q]; have := s.property; positivity
  obtain ⟨κ,hκ,hdec⟩ := short_fixed_length_from_coefficients_internal s q hq
  refine ⟨A,K,min εbase (1/16),κ+1,hA,hK,lt_min hεbase (by norm_num),by linarith,hAA,htyp.restrict (min_le_left _ _),?_⟩
  intro ε hε hεsmall
  have hsmall := hεsmall.trans_le (min_le_left εbase (1/16))
  have hσε : min s.val 1/2+2*ε < 1 := by
    rw [min_eq_right s.property.le]
    have hh := hεsmall.trans_le (min_le_right εbase (1/16))
    linarith
  obtain ⟨δ,hδ,hlocal⟩ := hlocal ε hε hsmall
  obtain ⟨ne,hne,hentry⟩ := hentry ε hε.le hσε
  obtain ⟨ns,Cs,hns,hCs,hsquare⟩ := InterpolationCoefficientBounds.interaction_square_internal s.val ε
    (by linarith [s.property]) hε.le hσε
  let n0 := max ne ns
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨T0,c,hT0,hc,hlocal⟩ := hlocal βlo βhi hlo hle θ
  obtain ⟨F,hF,hshort⟩ := InterpolationCoercivity.short_range_entry_internal θ
  obtain ⟨Fs,hFs,hforcing⟩ := InterpolationCoercivity.forcing_sq_le_weight θ s.val (by linarith [s.property])
  let P0 := 2+βlo⁻¹+βhi*(1+F+Ce)
  have hpos : 0 ≤ βhi*(1+F+Ce) := by have := hlo.trans_le hle; positivity
  have hP0 : 1 ≤ P0 := by dsimp only [P0]; linarith [inv_pos.mpr hlo]
  have hPlo : P0⁻¹ ≤ βlo := (inv_le_comm₀ (by linarith : 0 < P0) hlo).mpr (by
    dsimp only [P0]; linarith)
  have hPhi : βhi*(1+F+Ce) ≤ P0 := by dsimp only [P0]; linarith [inv_pos.mpr hlo]
  let E0 := 2*βhi^2*(Cs+Fs)
  have hE0 : 0 ≤ E0 := by dsimp only [E0]; positivity
  obtain ⟨C,hC,hdec⟩ := hdec ε hε P0 E0 T0 Cs c δ hP0 hE0 hT0.le hc hδ n0
  refine ⟨C,c/16,hC,by positivity,?_⟩
  intro β hβ a e f ha he hf hef hsize hpower y z L hyL hzL hy hz Y Z Dy Dz
  obtain ⟨Ky,hKy,hky,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofShort β s) e a (by omega) y
  obtain ⟨Kz,hKz,hkz,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofShort β s) f a (by omega) z
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht Ht μ w
  let hLN := InterpolationTransport.compatible_mass_lt a e he L y (by linarith only [hyL])
  obtain ⟨h0,htop,hprob,hforms⟩ := InterpolationCoefficientBounds.physical_form_internal (ofShort β s) θ ε
    e f a he hf y z L hyL hzL Ky Kz hky hkz ((e+a : ℕ)+1) rfl hLN t ht
  refine ⟨h0,htop,?_⟩
  intro _ ν H
  refine ⟨hprob,?_⟩
  let : IsProbabilityMeasure ν := hprob
  have hn : (0 : ℝ) < a+1 := by positivity
  have hn1 : (1 : ℝ) ≤ a+1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hsupp : ∀ᵐ x ∂ν,x.val ∈ AffineSimplex.massSimplex a L := by
    rw [(InterpolationTransport.measurableEmbedding_inclusion a L _ hLN).ae_map_iff]
    exact ae_of_all _ (fun u => u.property)
  have hsm (u) (hu : u ∈ AffineSimplex.massSimplex a L) :
      ContDiffAt ℝ ∞ Ky u ∧ ContDiffAt ℝ ∞ Kz u := by
    exact ⟨hKy.contDiffAt (((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
      (RetainedSimplex.continuous_assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val)).mem_nhds
        (InterpolationCoefficientBounds.fibre_mem_internal e a y L hyL hu)),
      hKz.contDiffAt (((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
      (RetainedSimplex.continuous_assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val)).mem_nhds
        (InterpolationCoefficientBounds.fibre_mem_internal f a z L hzL hu))⟩
  have hHt (u) (hu : u ∈ AffineSimplex.massSimplex a L) : ContDiffAt ℝ ∞ Ht u :=
    ((InterpolationCoercivity.forcing_smooth θ (Real.rpow_pos_of_pos hn (-ε)) hu.1).add
      (contDiffAt_const.mul (hsm u hu).1)).add (contDiffAt_const.mul (hsm u hu).2)
  have hsym (u) (hu : u ∈ AffineSimplex.massSimplex a L) (i j : Fin (a+1)) :
      hessianMatrix Ht u i j = hessianMatrix Ht u j i := by
    simp only [Intrinsic.hessianMatrix_eq_second (hHt u hu)]
    exact (hHt u hu).isSymmSndFDerivAt (by simp) _ _
  have hcurv := InterpolationCoefficientBounds.coercivity_internal (ofShort β s) θ ε hε.le e f a ha y z L
    hyL hzL Ky Kz hky hkz t ht
  have hb : min 1 (s.val*(s.val+1)) = 1 := min_eq_left (by nlinarith only [s.property])
  change ∀ u ∈ AffineSimplex.massSimplex a L,∀ v : EuclideanSpace ℝ (Fin (a+1)),
    min 1 (s.val*(s.val+1))*(a+1 : ℝ)^(-(s.val+2)*ε)*(∑ i,(v i)^2) ≤
      ∑ i,∑ j,v i*hessianMatrix Ht u i j*v j at hcurv
  rw [hb,one_mul] at hcurv
  have hHm (i j : Fin (a+1)) : Measurable (fun x => H x i j) :=
    ((DifferentiatedPoisson.measurable_hessian_entries (V := Ht) i j).comp measurable_subtype_coe).const_mul β.val
  obtain ⟨hHp,hlow⟩ := short_mass_curvature_internal s a L _ ν hsupp Ht β.val P0 q ε
    β.property hP0 (hPlo.trans hβ.1) hε.le (le_max_left _ _) hsym hcurv
  have hcoeff : (n0 : ℝ) ≤ (a+1 : ℝ) →
      ∃ (M : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) → Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
        (G : Set (AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1)))
        (W : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) → ℝ),
        SummableCoerciveMatrix (ρ := ν) s a.succPNat ε P0 q
          (Sum.inl ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩) M ∧
        MeasurableSet G ∧ (∀ᵐ x ∂ν,x ∈ G → H x = M x) ∧ IntegrableOn W Gᶜ ν ∧
        (∀ᵐ x ∂ν.restrict Gᶜ,1 ≤ W x) ∧
        (∀ᵐ x ∂ν.restrict Gᶜ,∀ i j,H x i j^2 ≤ E0*(a+1 : ℝ)^Cs*W x) ∧
        (∫ x in Gᶜ,W x ∂ν) ≤ T0*Real.exp (-c*(a+1 : ℝ)^δ) := by
    intro hlarge
    have hn0 : n0 ≤ a+1 := by exact_mod_cast hlarge
    have hne' : ne ≤ a+1 := (le_max_left _ _).trans hn0
    have hns' : ns ≤ a+1 := (le_max_right _ _).trans hn0
    let GA := {u : EuclideanSpace ℝ (Fin (a+1)) |
      WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat (e+a).succPNat (K*ε)}
    let G : Set (AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1)) := Subtype.val ⁻¹' GA
    let W := fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) =>
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp x.val)
    let M := fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) =>
      β.val • (if x.val ∈ GA then hessianMatrix Ht x.val else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ))
    have hGA : MeasurableSet GA := (InterpolantLocalLaws.measurableSet_goodBlockEvent _ _ _ _).preimage
      (WithLp.measurable_ofLp 2 _)
    have hG : MeasurableSet G := hGA.preimage measurable_subtype_coe
    let Gf := AffineSimplex.massSimplex a L ∩ GA
    have hpentry := hshort a ε (K*ε) (κe*ε) s.val Ce t hε.le (by have := hK; positivity)
      (by positivity) s.property hCe.le Gf Ky Kz
      (fun u hu i => by simpa only [Nat.succPNat_coe,Nat.cast_succ] using (hu.2.2.1 i).1)
      (fun u hu => hsm u hu.1)
      (fun u hu i j => hentry (ofShort β s) rfl e f a hef hne' hsize y z hy.1 hz.1 u
        (hyL ▸ hu.1) (hzL ▸ hu.1) hu.2 Ky Kz hky hkz t ht i j)
    have hq1 : max (4*(K*ε)) (κe*ε) ≤ q*ε := by
      apply max_le
      · have h := (le_max_left (4*K) κe).trans (le_max_right (s.val+2) (max (4*K) κe)); nlinarith only [h,hε]
      · have h := (le_max_right (4*K) κe).trans (le_max_right (s.val+2) (max (4*K) κe)); nlinarith only [h,hε]
    have hentries := short_cutoff_entry_enlarge_internal a L GA Gf rfl Ht β.val P0 (1+F+Ce)
      (max (4*(K*ε)) (κe*ε)) (q*ε) s.val β.property.le (by positivity)
      ((mul_le_mul_of_nonneg_right hβ.2 (by positivity : 0 ≤ 1+F+Ce)).trans hPhi) hq1 hpentry
    have hMbound : SummableCoerciveMatrix (ρ := ν) s a.succPNat ε P0 q
        (Sum.inl ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩) M :=
      short_scaled_cutoff_matrix_internal s a L _ ν hsupp Ht GA hGA β.val P0 q ε hP0
        (mul_nonneg hq hε.le) (hPlo.trans hβ.1) hsym hlow
        (hsupp.mono fun x hx i j => hentries x.val hx i j)
    have heq : ∀ᵐ x ∂ν,x ∈ G → H x = M x := ae_of_all _ (fun x hx => by
      change x.val ∈ GA at hx
      dsimp only [M,H]; rw [ite_eq_left hx])
    have hWmeas : Measurable W := InterpolantLocalLaws.measurable_exceptionalWeight s.val (n := a.succPNat)
      (fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) => WithLp.ofLp x.val) (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp measurable_subtype_coe)
    have hW1 : ∀ x,1 ≤ W x := fun x => InterpolantLocalLaws.one_le_exceptionalWeight s.val _
      (fun i => (x.property.1 i).le)
    obtain ⟨h0',ht',_hprob',htail,_⟩ :=
      (hlocal (ofShort β s) rfl hβ.1 hβ.2 e f a he hf ha hsize hef (by simpa only [Nat.cast_succ] using hpower)).2 L y z
        (by linarith) (by linarith) hy hz t ht.1 ht.2
    have hw : w = (fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*
        ((∑ k,(θ.val ((a+1 : ℝ)^(-ε)*u.val k)+θ.val ((a+1 : ℝ)^(-ε)*(u.val k)⁻¹)))+
          (1-t)*physicalAmbientGapEnergy (ofShort β s) (e+a).succPNat
            ⟨Y u.val,InterpolationCoefficientBounds.fibre_mem_internal e a y L hyL u.property⟩+
          t*physicalAmbientGapEnergy (ofShort β s) (f+a).succPNat
            ⟨Z u.val,InterpolationCoefficientBounds.fibre_mem_internal f a z L hzL u.property⟩)))) := by
      funext u
      dsimp only [w,Ht]
      rw [hky u.val (InterpolationCoefficientBounds.fibre_mem_internal e a y L hyL u.property),
        hkz u.val (InterpolationCoefficientBounds.fibre_mem_internal f a z L hzL u.property)]
    have htail' : (∫⁻ x in Gᶜ,ENNReal.ofReal (W x) ∂ν) ≤
        ENNReal.ofReal (T0*Real.exp (-c*(a+1 : ℝ)^δ)) := by
      change (∫⁻ x in {x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) | x.val ∈ GAᶜ},
        ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp x.val))
        ∂(AffineFibre.normalizedMeasure μ w h0 htop).map (InterpolationTransport.inclusion a L _ hLN)) ≤ _
      rw [InterpolationTransport.lintegral_inclusion a L _ hLN
        (AffineFibre.normalizedMeasure μ w h0 htop) GAᶜ
        (fun u : EuclideanSpace ℝ (Fin (a+1)) => ENNReal.ofReal
          (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp u)))]
      simpa only [AffineFibre.normalizedMeasure_eq_smul,hw,Nat.cast_succ,ofShort,μ,Y,Z,GA,compl_ofPred] using htail
    have hWi : IntegrableOn W Gᶜ ν := ⟨hWmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => zero_le_one.trans (hW1 x))).mpr
        (htail'.trans_lt ENNReal.ofReal_lt_top)⟩
    have htailR : (∫ x in Gᶜ,W x ∂ν) ≤ T0*Real.exp (-c*(a+1 : ℝ)^δ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hWi (ae_of_all _ fun x => zero_le_one.trans (hW1 x))] at htail'
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htail'
    refine ⟨M,G,W,hMbound,hG,heq,hWi,ae_of_all _ hW1,?_,htailR⟩
    filter_upwards [ae_restrict_of_ae hsupp] with x hx i j
    have hi := hsquare (ofShort β s) rfl e f a hns' hsize (by omega) y z hy.1 hz.1 L hyL hzL
      Ky Kz hky hkz t ht x.val hx i j
    have hp := hforcing a ε hε.le x.val hx.1 i j
    have hW0 : 0 ≤ W x := zero_le_one.trans (hW1 x)
    have hpow : 1 ≤ (a+1 : ℝ)^Cs := Real.one_le_rpow hn1 hCs.le
    have hsplit := InterpolationCoercivity.interpolant_hessian_internal θ
      (Real.rpow_pos_of_pos hn (-ε)) hx.1 (hsm x.val hx).1 (hsm x.val hx).2 (t := t) i j
    change (β.val*hessianMatrix Ht x.val i j)^2 ≤ _
    rw [hsplit]
    simpa only [E0,add_comm Cs Fs] using short_add_square_envelope_internal β.val βhi
      _ _ Fs Cs ((a+1 : ℝ)^Cs) (W x) β.property.le hβ.2 hFs.le hCs.le hpow hW0
        (by simpa only [sq_abs] using hp) (by simpa only [sq_abs] using hi)
  intro frame
  obtain ⟨Q,hQ,hcons,hcert⟩ := hforms frame
  refine ⟨Q,hQ,hcons,hcert,?_⟩
  intro i₀ hi₀ χ
  have ha0 : 0 < P0⁻¹*(a+1 : ℝ)^(-(q*ε)) := by positivity
  refine ⟨MatrixEnergy.weightedWeakSolution_existsUnique Q hQ H (zeroSumComponents (Fin (a+1))) hHp
    _ ha0 (hlow.mono fun x hx v _ => hx v) hHm _,?_⟩
  intro ψ hψ B
  have hh := hdec a.succPNat _ ν Q hQ hcons H hHm hHp
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ] using hlow) i₀
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ] using hi₀) χ ψ hψ
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ] using hcoeff)
  simp only [Nat.succPNat_coe,Nat.cast_succ] at hh
  constructor
  · apply hh.1.trans
    gcongr
    nlinarith only [hε]
  · apply hh.2.trans
    gcongr
    nlinarith only [hε]

end Riesz2.FixedLengthDecay
