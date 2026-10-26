/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.AuxiliaryMean
public import Riesz2.Thermodynamic.IntegratedCovariancePart2
public import Riesz2.DecayLong.PhysicalMeanPart2
public import Riesz2.DecayLong.FullCycleComparisonPart2
public import Riesz2.Frozen.GoodBlockEvent
public import Riesz2.DecayLong.PaperCutoffDegree

/-!
# Physical scalar forms for the fixed-exterior auxiliary equation

Specialization of the proof of Lemma 6.4 to the common-length simplex. The matrix
hypothesis is the internal matrix clause of Subsection 6.1. The physical law, its
intrinsic metric, the scalar form and the Schur lift use this simplex. The five
estimates hold on this law.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal ContDiff

namespace Riesz2.AuxiliaryMean

/-- See the proof of Lemma 6.4 in the paper: all scalar hypotheses of the analytic
estimate hold for the actual fixed-length Gibbs form in every orthonormal
chart. In particular the gradient metric is intrinsic Hausdorff geometry. -/
theorem orthonormal_scalar_internal (a : ℕ) {L : ℝ} (hL : 0 < L)
    (ρ : Measure (AffineSimplex.Tangent a)) (V : AffineSimplex.Tangent a → ℝ)
    (hV : IsEuclideanGibbsPotential volume ρ
      (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L) V)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let U := e '' Ω
    let ν := ρ.map e
    IsOpen U ∧ Convex ℝ U ∧ Bornology.IsBounded U ∧ U.Nonempty ∧
      IsProbabilityMeasure ν ∧
    ∃ _hW : IsEuclideanGibbsPotential volume ν U (V ∘ e.symm),
    ∃ Q : ScalarFormData ν,
      IsNeumannRealization U Q ∧ IsClosedScalarDirichletForm Q ∧
        IsConservativeScalarForm Q := by
  intro Ω U ν
  have hU := e.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
  have hB := e.isometry.lipschitzWith.isBounded_image
    (ConditionalWellPosedness.fibre_isBounded a L)
  have hW := IntrinsicScalarPoisson.gibbs_isometry e hV
  have hne : Ω.Nonempty := by
    refine ⟨0, ?_⟩
    change AffineSimplex.centredChart a L 0 ∈ AffineSimplex.massSimplex a L
    simpa only [AffineSimplex.centredChart, Submodule.coe_zero, zero_add] using
      AffineSimplex.centre_mem_simplex a hL
  exact ⟨hU, (ConditionalWellPosedness.fibre_convex a L).linear_image
      e.toLinearEquiv.toLinearMap, hB, hne.image e,
    IntrinsicScalarCore.probability hW, hW, IntrinsicScalarCore.form hU hB hW,
    IntrinsicScalarCore.realization hU hB hW,
    IntrinsicScalarCore.closed_dirichlet hU hB hW,
    IntrinsicScalarCore.conservative hU hB hW⟩

/-- See Subsection 6.1 of the paper, used by the proof of Lemma 6.4: a Gibbs law in the
orthonormal chart pushes forward to the normalized Hausdorff simplex law
with the same density on the whole physical carrier. The normalizer is
proved positive and finite. No totalized inverse is used. -/
theorem simplex_density_internal (a : ℕ) (L : ℝ)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ρ : Measure (EuclideanSpace ℝ (Fin a)))
    (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ρ
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (w : EuclideanSpace ℝ (Fin (a + 1)) → ℝ≥0∞) (hw : Measurable w)
    (he : ∀ x ∈ e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      w (AffineSimplex.centredChart a L (e.symm x)) = ENNReal.ofReal (Real.exp (-V x))) :
    ∃ h0 ht, ρ.map (fun x => AffineSimplex.centredChart a L (e.symm x)) =
      AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume a L) w h0 ht := by
  let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
  let U := e '' Ω
  let f := fun x => AffineSimplex.centredChart a L (e.symm x)
  have hf : MeasurableEmbedding f :=
    ((AffineSimplex.isometry_centredChart a L).comp e.symm.isometry).isClosedEmbedding.measurableEmbedding
  have hU : MeasurableSet U :=
    (e.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)).measurableSet
  have hvol : (volume.restrict U).map f = AffineSimplex.simplexVolume a L := by
    have hmap : (volume.restrict U).map e.symm = volume.restrict Ω := by
      have hpre : e.symm ⁻¹' Ω = U := by
        exact (e.image_eq_preimage_symm Ω).symm
      rw [← hpre]
      have hemb : MeasurableEmbedding (fun x => e.symm x) :=
        e.symm.toHomeomorph.measurableEmbedding
      exact (hemb.restrict_map volume Ω).symm.trans
        (by rw [e.symm.measurePreserving.map_eq])
    change (volume.restrict U).map (AffineSimplex.centredChart a L ∘ e.symm) = _
    rw [← Measure.map_map (AffineSimplex.isometry_centredChart a L).continuous.measurable
      e.symm.continuous.measurable, hmap, ← AffineSimplex.simplexVolume_eq_centredChart_map]
  have hae : (fun x => w (f x)) =ᵐ[volume.restrict U]
      (fun x => ENNReal.ofReal (Real.exp (-V x))) :=
    (ae_restrict_mem hU).mono (fun x hx => he x hx)
  have h0 : (∫⁻ x, w (f x) ∂volume.restrict U) ≠ 0 := by
    rw [lintegral_congr_ae hae]
    exact hV.2.1.ne'
  have ht : (∫⁻ x, w (f x) ∂volume.restrict U) ≠ ⊤ := by
    rw [lintegral_congr_ae hae]
    exact hV.2.2.1.ne
  have hn : ρ = AffineFibre.normalizedMeasure (volume.restrict U)
      (fun x => w (f x)) h0 ht := by
    rw [AffineFibre.normalizedMeasure_eq_smul, lintegral_congr_ae hae,
      withDensity_congr_ae hae]
    exact hV.2.2.2
  have hm := AffineFibre.normalizedMeasure_map (volume.restrict U) hf hw h0 ht
  have h0' : (∫⁻ x, w x ∂AffineSimplex.simplexVolume a L) ≠ 0 := by
    rw [← hvol, hf.lintegral_map]; exact h0
  have ht' : (∫⁻ x, w x ∂AffineSimplex.simplexVolume a L) ≠ ⊤ := by
    rw [← hvol, hf.lintegral_map]; exact ht
  refine ⟨h0', ht', ?_⟩
  rw [hn]
  simpa only [hvol] using hm.symm

/-- See the proof of Lemma 6.4 in the paper: the square root of the scalar form energy
is the norm of the unique intrinsic weak gradient, on the entire form
domain. This applies to the active sum without any smoothness premise. -/
theorem simplex_mean_gradient_internal (a : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (U : Set (EuclideanSpace ℝ (Fin a)))
    (Q : ScalarFormData ν) (hreal : IsNeumannRealization U Q) (S : Q.1) :
    ∃! g : Lp (EuclideanSpace ℝ (Fin a)) 2 ν,
      (S.val, g) ∈ neumannSobolevGraph ν U ∧ Real.sqrt (Q.2 S S) = ‖g‖ := by
  obtain ⟨g, hg⟩ := (hreal.1 S.val).mp S.property
  refine ⟨g, ⟨hg, ?_⟩, fun k hk => hreal.2.1 S.val k g hk.1 hg⟩
  rw [hreal.2.2 S S g g hg hg, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg g)]

/-- See Subsection 6.1 and the proof of Lemma 6.4 of the paper: the physical matrix clause
on the Hausdorff simplex law pulls back to the orthonormal scalar chart,
including its measurable interval-coefficient witnesses. This uses the
pullback theorem rather than a second encoding of matrix bounds. -/
theorem simplex_matrix_bounds_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ η : ℝ)
    (a : ℕ) (L : ℝ)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a)))
    (M : EuclideanSpace ℝ (Fin (a + 1)) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds
      (ν := ν.map (fun x => AffineSimplex.centredChart a L (e.symm x)))
      s n m hm K C κ γ η M) :
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ η
      (M ∘ (fun x => AffineSimplex.centredChart a L (e.symm x))) :=
  FullCycleComparison.matrix_bounds_pullback_internal ν
    (fun x => AffineSimplex.centredChart a L (e.symm x))
    ((AffineSimplex.isometry_centredChart a L).continuous.measurable.comp
      e.symm.continuous.measurable) s n m hm K C κ γ η M hM

/-- Physical composition in the proof of Lemma 6.4.

The hypothesis `hMphys` states the all-size internal matrix conclusion of
Subsection 6.1 on the fixed-exterior matrix and physical simplex law.
All scalar-form hypotheses hold for the normalized common-simplex
interpolation at every size. The loss exponent precedes the tolerance and
the compact temperature interval. The five estimates hold for every L² source.

Here `a+1` is the active size and `b+1,c+1` are the exterior sizes.
The matrices `Py,Pz` retain the internal short intervals with their
physical coefficients and antipodal factors. The degree is the least
integer of Lemma 5.4, as used in Lemma 6.4. -/
theorem fixed_exterior_auxiliary_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar Ks : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (hKs : 0 < Ks) :
    let h : ℕ+ := paperReferenceCutoffExponent s
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, ∀ _hε : 0 < ε,
    ∀ _hsmall : ε ≤ (4 * Ks * ((h : ℝ) + 1))⁻¹,
    ∀ Cstar : ℝ, ∀ hCstar : 1 ≤ Cstar,
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, ∀ _hβ : β.val ∈ Icc βlo βhi,
    ∀ a b c : ℕ, ∀ _ha : 1 ≤ a, ∀ _hbc : b ≤ c,
    let n := a.succPNat
    let N := (a + 1 + b).succPNat
    let N' := (a + 1 + c).succPNat
    ∀ hN : 4 * (n : ℕ) ≤ (N : ℕ),
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
    ∀ (L : ℝ), ∀ _hL : 0 < L,
    ∀ (y : EuclideanSpace ℝ (Fin (b + 1))) (z : EuclideanSpace ℝ (Fin (c + 1))),
    ∀ hy : (∀ j, 0 < y j), ∀ hz : (∀ j, 0 < z j),
    ∀ hmassY : L + ∑ j, y j = (N : ℝ), ∀ hmassZ : L + ∑ j, z j = (N' : ℝ),
    ∀ θ : PhysicalCutoff,
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let P := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => ∑ i,
      (θ.val ((n : ℝ) ^ (-ε) * x i) + θ.val ((n : ℝ) ^ (-ε) * (x i)⁻¹))
    ∃ Ky Kz : AffineSimplex.Tangent a → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy (ofLong β s) N
        ⟨RetainedSimplex.assemble (a + 1) b (Equiv.refl _)
          (AffineSimplex.centredChart a L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem a b
              (Equiv.refl _) y hy (by
                simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hmassY) hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy (ofLong β s) N'
        ⟨RetainedSimplex.assemble (a + 1) c (Equiv.refl _)
          (AffineSimplex.centredChart a L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem a c
              (Equiv.refl _) z hz (by
                simpa only [N', Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hmassZ) hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
    ∀ t : ℝ, ∀ _ht : t ∈ Icc (0 : ℝ) 1,
    let V := fun w => β.val * (P (AffineSimplex.centredChart a L w) +
      (1 - t) * Ky w + t * Kz w)
    ∃ ρ : Measure (AffineSimplex.Tangent a),
      IsEuclideanGibbsPotential volume ρ Ω V ∧
    ∀ e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let U := e '' Ω
    let ν := ρ.map e
    ∃ _hW : IsEuclideanGibbsPotential volume ν U (V ∘ e.symm),
    ∃ Q : ScalarFormData ν, IsNeumannRealization U Q ∧ IsConservativeScalarForm Q ∧
    ∃ hQ : IsClosedScalarDirichletForm Q,
    let m := PhysicalCore.properReferencePeriod s n N
    let hm : 2 ≤ (m : ℕ) := by
      change 2 ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
      have := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
      have := n.pos
      omega
    let hnm : (n : ℕ) ≤ (m : ℕ) := by
      change (n : ℕ) ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
      have := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
      omega
    let η := Ks * ε
    let K := ⌊(n : ℝ) ^ η⌋₊ ^ (h : ℕ)
    let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
    let Py := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      IntervalBoundary.internalMatrix N n (by omega) (fun ir =>
        BoundaryEntries.intervalWeight s N ir.2 ir.1
          (RetainedSimplex.assemble (a + 1) b (Equiv.refl _) x y))
    let Pz := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      IntervalBoundary.internalMatrix N' n (by
        simp only [N', n, Nat.succPNat_coe]
        omega) (fun ir =>
        BoundaryEntries.intervalWeight s N' ir.2 ir.1
          (RetainedSimplex.assemble (a + 1) c (Equiv.refl _) x z))
    let A0 := fun x =>
      (if WithLp.ofLp x ∈ goodBlockEvent s.val n N η then
        hessianMatrix P x + (1 - t) • Py x + t • Pz x
      else BoundaryEntries.referenceInternal s m hm K n hnm) +
        BoundaryEntries.referenceCrossing s m hm K n hnm
    let Mphys := fun x : EuclideanSpace ℝ (Fin (a + 1)) =>
      fun i j : Fin (m : ℕ) => if hi : i.val < (n : ℕ) then
        if hj : j.val < (n : ℕ) then
          A0 x ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else H i j
      else H i j
    let chart := fun w => AffineSimplex.centredChart a L (e.symm w)
    let M := Mphys ∘ chart
    ∀ hMphys : PeriodizedMatrixBounds (ν := ν.map chart)
      s n m hm K Cstar κstar γstar η Mphys,
    let hM := simplex_matrix_bounds_internal s n m hm K Cstar κstar γstar η
      a L e ν Mphys hMphys
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ χ : Lp ℝ 2 ν,
    let f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n m hnm s hm K
      Cstar κstar γstar η β.val hCstar β.property M hM
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let S : Q.1 := ∑ i : Fin (n : ℕ), v' i
    (∀ j : Fin (n : ℕ), ‖(v' j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v' j).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
    ‖S.val‖ ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) * ‖χ‖ ∧
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => (v' i).val x) :
      EuclideanSpace ℝ (Fin (n : ℕ)))) ∞ ν ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (κ * ε)) * eLpNorm χ ∞ ν := by
  intro h
  obtain ⟨κ, hκ, hbounds⟩ := schur_auxiliary_estimates_internal hzeta s κstar γstar h
    hκstar hγstar
  refine ⟨κ * Ks, mul_pos hκ hKs, ?_⟩
  intro ε hε hsmall Cstar hCstar βlo βhi hβlo hβhi
  obtain ⟨C, hC, hbounds⟩ := hbounds (Ks * ε) (mul_pos hKs hε)
    Cstar hCstar βlo βhi hβlo hβhi
  refine ⟨C, hC, ?_⟩
  intro β hβ a b c ha hbc n N N' hN _hNpow L hL y z hy hz hmassY hmassZ θ Ω P
  obtain ⟨Ky, Kz, hKy, hKz, B, _hB, hphysical⟩ :=
    IntegratedCovariance.conditional_intrinsic_equations (ofLong β s) a b c ha
      (Equiv.refl _) (Equiv.refl _) hL y hy z hz
      (by simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hmassY)
      (by simpa only [N', Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hmassZ) θ ε hε
  refine ⟨Ky, Kz, hKy, hKz, ?_⟩
  intro t ht V
  obtain ⟨ρ, hV, _hH, _hbar, _hwell⟩ := hphysical t ht
  refine ⟨ρ, hV, ?_⟩
  intro e U ν
  obtain ⟨hU, hc, hB, hne, hp, hW, Q, hr, hQ, hcon⟩ :=
    orthonormal_scalar_internal a hL ρ V hV e
  refine ⟨hW, Q, hr, hcon, hQ, ?_⟩
  intro m hm hnm η K H Py Pz A0 Mphys chart M hMphys hM i₀ hi₀ χ
  have hn : 2 ≤ (n : ℕ) := by simp only [n, Nat.succPNat_coe]; omega
  have hnm2 : 2 * (n : ℕ) ≤ (m : ℕ) :=
    (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
  have hupper : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) :=
    PhysicalMean.proper_period_upper_internal s n N
  have hprod : (h : ℝ) * η ≤ 1 / 4 := by
    have hd : 0 < 4 * Ks * ((h : ℝ) + 1) := by positivity
    have hh : ε * (4 * Ks * ((h : ℝ) + 1)) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hsmall hd.le).trans_eq (inv_mul_cancel₀ hd.ne')
    dsimp only [η]
    have hη : 0 ≤ Ks * ε := (mul_pos hKs hε).le
    nlinarith
  have hcut := interpolation_cutoff_bounds_internal n m hn hnm2 η
    (h : ℕ) (mul_pos hKs hε).le hprod
  obtain ⟨hex, hest⟩ := hbounds β hβ n m hn hm hnm2 hupper hcut.1 hcut.2
    a U ν hU hc hB hne hp ⟨V ∘ e.symm, hW.1.of_le (by norm_num), hW.2⟩
    _ hr hQ hcon M hM i₀ hi₀ χ
  intro f Abar
  refine ⟨hex, ?_⟩
  intro v hv v' S
  have he := hest v hv
  simpa only [mul_assoc] using he

end Riesz2.AuxiliaryMean
