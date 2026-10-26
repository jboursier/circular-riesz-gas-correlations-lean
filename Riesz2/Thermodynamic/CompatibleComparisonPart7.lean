/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart5
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart11

/-!
# Physical interaction coefficients and their Sobolev jet

The differential estimates in the proof of Proposition 6.6 and the weighted local law
give the envelope bounds for the interaction jet on the specified physical orthonormal
chart.
-/

public section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See Subsection 6.1 and Lemma 6.4 of the paper: two physical realizations agree
near each point of the physical fibre, so their ambient derivatives agree.
No equality away from the physical ambient domain is required. -/
theorem physical_realization_fderiv_internal (p : Parameters) (a d : ℕ) (L : ℝ)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L)
    (K : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (W : EuclideanSpace ℝ (Fin (d+1+a+1)) → ℝ)
    (hK : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      K u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩)
    (hW : ∀ x : {x : EuclideanSpace ℝ (Fin (d+1+a+1)) //
        x ∈ gapAmbientDomain (d+1+a).succPNat},
      W x.val = physicalAmbientGapEnergy p (d+1+a).succPNat x)
    (u : EuclideanSpace ℝ (Fin (a+1))) (hu : u ∈ AffineSimplex.massSimplex a L) :
    fderiv ℝ K u = fderiv ℝ (fun v => W (RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val v)) u := by
  apply EventuallyEq.fderiv_eq
  have hmem := InterpolationCoefficientBounds.fibre_mem_internal (d+1) a y L hyL hu
  have hopen := (PhysicalEnergy.isOpen_gapAmbientDomain (d+1+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val)
  filter_upwards [hopen.mem_nhds hmem] with v hv
  exact (hK v hv).trans (hW ⟨_,hv⟩).symm

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: every ambient
realization of the physical endpoint is smooth on its whole physical domain.
Thus smoothness is a conclusion of the realization equations, rather than
an extra hypothesis in the final interaction-jet theorem. -/
theorem physical_realization_smooth_internal (p : Parameters) (a d : ℕ)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (K : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hK : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      K u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) :
    ContDiffOn ℝ ∞ K (RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
        gapAmbientDomain (d+1+a).succPNat) := by
  obtain ⟨K₀,hKs,hK₀,_⟩ := InterpolationCoercivity.assembled_energy_realization
    p (d+1) a (by omega) y
  exact hKs.congr fun u hu => (hK u hu).trans (hK₀ u hu).symm

/-- See the proof of Proposition 6.6 in the paper:
the differential bounds hold for every specified pair of physical
endpoint realizations. The constants precede sizes, temperature and exteriors.
The smaller system is the first endpoint, and no sign change is introduced. -/
theorem physical_differential_bounds_internal (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (K : ℝ) (hK : 1 < K) (ε : ℝ) (hε : 0 < ε)
    (hεs : ε < min (1-min s 1/2) (s-min s 1/2)/4) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d e : ℕ, 1 ≤ a →
      4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (p : Parameters), p.val.2 = s →
    ∀ (θ : PhysicalCutoff) (A L : ℝ), 1 < A →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ),
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) →
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) →
    ∀ u ∈ AffineSimplex.massSimplex a L,
    let b := InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ (fun v => Ky v-Kz v) u
        (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1)))
    ; (WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) →
        ∀ j, |b j| ≤ C*(a+1 : ℝ)^(κ*ε)*
          (InteractionDifferential.boundaryWeight s a.succPNat j+
            (a+1 : ℝ)*(d+1+a+1 : ℝ)^(-s))) ∧
      (∀ j, b j^2 ≤ C*(a+1 : ℝ)^C*
        InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)) := by
  obtain ⟨C,κ,hC,hκ,hmain⟩ := InterpolantLocalLaws.admissible_interaction_differential
    s hs hs1 K hK ε hε hεs
  refine ⟨C,κ,hC,hκ,?_⟩
  intro a d e ha hsize hde hpower p hps
  obtain ⟨WN,WM,hWN,hWM,hvN,hvM,hbound⟩ :=
    hmain a (d+1) (e+1) ha hsize (by omega) (by simpa only [Nat.cast_add,Nat.cast_one] using hpower) p hps
  intro θ A L hA y z hy hz hyL hzL Ky Kz hKy hKz u hu b
  have hcy : (∑ i, y.val i)+L = (↑(d+1)+a+1 : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one] at hyL ⊢
    linarith only [hyL]
  have hcz : (∑ i, z.val i)+L = (↑(e+1)+a+1 : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one] at hzL ⊢
    linarith only [hzL]
  have hbound' := hbound (by omega) (by omega) θ A hA L y z hy hz
    hcy hcz u hu.1 hu.2
  have hdiff : (fun v => Ky v-Kz v) =ᶠ[𝓝 u]
      (fun v => WN (RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val v)-
        WM (RetainedSimplex.assemble (e+1) a
          (InterpolatingDensities.exteriorPermutation (e+1) a) z.val v)) := by
    have hyOpen := (PhysicalEnergy.isOpen_gapAmbientDomain (d+1+a).succPNat).preimage
      (RetainedSimplex.continuous_assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val)
    have hzOpen := (PhysicalEnergy.isOpen_gapAmbientDomain (e+1+a).succPNat).preimage
      (RetainedSimplex.continuous_assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val)
    filter_upwards [hyOpen.mem_nhds
      (InterpolationCoefficientBounds.fibre_mem_internal (d+1) a y L hyL hu),
      hzOpen.mem_nhds
      (InterpolationCoefficientBounds.fibre_mem_internal (e+1) a z L hzL hu)] with v hv hw
    exact congrArg₂ (fun x y : ℝ => x-y)
      ((hKy v hv).trans (hvN ⟨_,hv⟩).symm)
      ((hKz v hw).trans (hvM ⟨_,hw⟩).symm)
  have he := hdiff.fderiv_eq (𝕜 := ℝ)
  refine ⟨?_,?_⟩
  · simpa only [b,he,Nat.cast_add,Nat.cast_one] using hbound'.2.2.1
  · intro j
    have hsum := hbound'.2.2.2.1
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] at hsum
    apply (Finset.single_le_sum (fun i _ => sq_nonneg
      (InteractionDifferential.pinnedRepresentative _ i)) (Finset.mem_univ j)).trans
    simpa only [b,he] using hsum

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the ambient
image of an orthonormal Gibbs realization is the literal normalized
Hausdorff law. This internal bridge applies to its actual density. -/
theorem chart_normalized_image_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (H : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hw : Measurable (fun u : AffineSimplex.massSimplex a L =>
      ENNReal.ofReal (Real.exp (-H u.val)))) :
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-H u.val))
    ∀ (h0 : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
      (htop : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤),
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (_hV : IsEuclideanGibbsPotential volume μ U (H ∘ g)),
      μ.map g = (AffineFibre.normalizedMeasure
        ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0 htop).map Subtype.val := by
  intro U g w h0 htop μ hV
  obtain ⟨h0',htop',hlaw⟩ := InterpolationTransport.normalized_intrinsic_law_internal
    a L N hLN frame μ (H ∘ g) hV w hw (fun _ _ _ => rfl)
  have hh := congrArg (Measure.map (Subtype.val : AffineSimplex.chartDomain (a+1) N →
    EuclideanSpace ℝ (Fin (a+1)))) hlaw
  rw [(InterpolationTransport.orthonormal_law a L N hLN frame μ (H ∘ g) hV).2,
    InterpolationTransport.map_inclusion_val] at hh
  exact hh

/-- See the proof of Proposition 6.6 in the paper: transfer a physical extended
weighted tail through its actual chart image, obtaining integrability.
This is an internal measure-transport step. The estimate is supplied by
the physical local law in the final theorem. -/
theorem chart_envelope_of_tail_internal (a : ℕ) (L s η T : ℝ) (hT : 0 ≤ T)
    (N : ℕ+)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let good := {x | WithLp.ofLp (g x) ∈ goodBlockEvent s a.succPNat N η}
    let W := fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp (g x))
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a))) [IsProbabilityMeasure μ]
      (ν : Measure (EuclideanSpace ℝ (Fin (a+1)))),
      μ.map g = ν → (∀ᵐ x ∂μ, x ∈ U) →
      (∫⁻ u in {u : EuclideanSpace ℝ (Fin (a+1)) |
          WithLp.ofLp u ∉ goodBlockEvent s a.succPNat N η},
        ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
          (WithLp.ofLp u)) ∂ν) ≤ ENNReal.ofReal T →
      IntegrableOn W goodᶜ μ := by
  intro U g good W μ _ ν heq hsupport hbad
  have hg : Continuous g := (AffineSimplex.isometry_centredChart a L).continuous.comp
    frame.symm.continuous
  have hw : Measurable W := InterpolantLocalLaws.measurable_exceptionalWeight (n := a.succPNat) s
    (fun x : EuclideanSpace ℝ (Fin a) => WithLp.ofLp (g x))
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hg.measurable)
  have htail : (∫⁻ x in goodᶜ, ENNReal.ofReal (W x) ∂μ) ≤ ENNReal.ofReal T := by
    rw [← heq, setLIntegral_map] at hbad
    · exact hbad
    · exact ((InterpolantLocalLaws.measurableSet_goodBlockEvent s a.succPNat
        N η).preimage (WithLp.measurable_ofLp 2 _)).compl
    · exact (InterpolantLocalLaws.measurable_exceptionalWeight (n := a.succPNat) s
        (fun u : EuclideanSpace ℝ (Fin (a+1)) => WithLp.ofLp u)
        (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)).ennreal_ofReal
    · exact hg.measurable
  have hgs (x) (hx : x ∈ U) : g x ∈ AffineSimplex.massSimplex a L := by
    obtain ⟨v,hv,rfl⟩ := hx
    simpa only [g,frame.symm_apply_apply,mem_preimage] using hv
  have hone : ∀ᵐ x ∂μ.restrict goodᶜ, 1 ≤ W x := by
    filter_upwards [ae_restrict_of_ae hsupport] with x hx
    exact InterpolantLocalLaws.one_le_exceptionalWeight (n := a.succPNat) s _ (fun i => ((hgs x hx).1 i).le)
  exact (GoodSetL2Comparison.tail_data (ν := μ) W hw.aestronglyMeasurable
    (E := goodᶜ) (T := T) hT hone htail).1


/-- See the proof of Proposition 6.6 and Lemma 6.4 of the paper: the literal
physical interaction has its Sobolev jet on every specified orthonormal
Gibbs law for admissible compatible exteriors. Only physical data and the
locally uniform rigidity predicate are inputs. The bad-set envelope
is integrable, and the coefficient classes represent the exact differential.
In particular no
coefficient estimate, tail bound, or integrability premise is assumed.
The structural admissibility constants precede the tolerance and temperature. -/
theorem physical_interaction_jet_from_admissibility_internal
    (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ (p : Parameters), p.val.2 = s →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (θ : PhysicalCutoff) (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ),
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) →
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) →
    ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    ∀ (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
      (M : Matrix (Fin (a+1)) (Fin a) ℝ),
      (∀ v : Fin a → ℝ, M *ᵥ v = (frame.symm (WithLp.toLp 2 v)).val) →
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let U := frame '' Ω
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let V := fun x => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*g x i)+θ.val ((a+1 : ℝ)^(-ε)*(g x i)⁻¹)))+
        (1-t)*Ky (g x)+t*Kz (g x))
    let D := fun u => Ky u-Kz u
    let b := fun j x => InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D (g x) (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (hV : IsEuclideanGibbsPotential volume μ U V),
    let hU := frame.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp (g x)))
      {x | WithLp.ofLp (g x) ∉ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)} μ ∧
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap M.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  obtain ⟨A,K,εbase,hA,hK,hεbase,hlocal⟩ :=
    InterpolantLocalLaws.local_laws hRig s hs hs1
  let margin := min (1-min s 1/2) (s-min s 1/2)/4
  have hmargin : 0 < margin := by
    have hσ : min s 1/2 < 1 := by have := min_le_right s 1; linarith
    have hsσ : min s 1/2 < s := by
      rcases le_total s 1 with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    exact div_pos (lt_min (sub_pos.mpr hσ) (sub_pos.mpr hsσ)) (by norm_num)
  refine ⟨A,K,min εbase margin,hA,hK,lt_min hεbase hmargin,?_⟩
  intro ε hε hεsmall p hps a d e ha hsize hde hpower θ L hL y z hy hz hyL hzL
    Ky Kz hKy hKz t ht frame M hM Ω U g V D b μ hV hU hB
  have hKys := physical_realization_smooth_internal p a d y Ky hKy
  have hKzs := physical_realization_smooth_internal p a e z Kz hKz
  obtain ⟨Cb,κ,hCb,_hκ,hcoeff⟩ := physical_differential_bounds_internal s hs hs1 K hK ε hε
    (hεsmall.trans_le (min_le_right _ _))
  have hc := hcoeff a d e ha hsize hde hpower p hps θ A L hA y z hy hz hyL hzL Ky Kz hKy hKz
  obtain ⟨δ,_hδ,hlocal⟩ := hlocal ε hε (hεsmall.trans_le (min_le_left _ _))
  obtain ⟨Cl,cl,hCl,_hcl,hlocal⟩ := hlocal p.val.1 p.val.1 p.property.1 le_rfl θ
  obtain ⟨_,hlocal⟩ := hlocal p hps le_rfl le_rfl (d+1) (e+1) a (by omega) (by omega)
    ha hsize (by omega) (by simpa only [Nat.cast_add,Nat.cast_one] using hpower)
  have hcy : (∑ i, y.val i)+L = ((d+1+a : ℕ)+1 : ℝ) := by linarith only [hyL]
  have hcz : (∑ i, z.val i)+L = ((e+1+a : ℕ)+1 : ℝ) := by linarith only [hzL]
  obtain ⟨h0,htop,_hprob,hbad,_hcoords,_hblocks⟩ :=
    hlocal L y z hcy hcz hy hz t ht.1 ht.2
  simp only [← hKy,← hKz] at h0 htop hbad
  let H := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
    ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
      (1-t)*Ky u+t*Kz u)
  let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-H u.val))
  have h0w : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0 := by
    simpa only [w,H,neg_mul,Nat.cast_add,Nat.cast_one] using h0
  have htopw : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤ := by
    simpa only [w,H,neg_mul,Nat.cast_add,Nat.cast_one] using htop
  let ρ := AffineFibre.normalizedMeasure
    ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0w htopw
  have hbadρ : (∫⁻ u in {u : EuclideanSpace ℝ (Fin (a+1)) |
      WithLp.ofLp u ∉ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
        (WithLp.ofLp u)) ∂ρ.map Subtype.val) ≤
      ENNReal.ofReal (Cl*Real.exp (-cl*(a+1 : ℝ)^δ)) := by
    simpa only [ρ,w,H,neg_mul,Nat.cast_add,Nat.cast_one] using hbad
  let good := {x | WithLp.ofLp (g x) ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)}
  let W := fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp (g x))
  have hcyN := InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y hcy
  have hw : Measurable w := by
    have hcH : Continuous (fun u : AffineSimplex.massSimplex a L => H u.val) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz
        hKys hKzs t u.val u.property).continuousAt.comp continuous_subtype_val.continuousAt
    exact hcH.neg.measurable.exp.ennreal_ofReal
  have hmap : μ.map g = ρ.map Subtype.val :=
    chart_normalized_image_internal a L _ hcyN frame H hw h0w htopw μ hV
  have : IsProbabilityMeasure μ := IntrinsicScalarCore.probability hV
  have hW : IntegrableOn W goodᶜ μ := chart_envelope_of_tail_internal a L s (K*ε)
    (Cl*Real.exp (-cl*(a+1 : ℝ)^δ)) (by positivity) (d+1+a).succPNat frame μ
    (ρ.map Subtype.val) hmap (IntrinsicScalarCore.supported hU hV) hbadρ
  have hg : Continuous g := (AffineSimplex.isometry_centredChart a L).continuous.comp
    frame.symm.continuous
  have hgood : MeasurableSet good := (InterpolantLocalLaws.measurableSet_goodBlockEvent
    s a.succPNat (d+1+a).succPNat (K*ε)).preimage
      ((WithLp.measurable_ofLp 2 _).comp hg.measurable)
  have hsupport := IntrinsicScalarCore.supported hU hV
  have hgs (x) (hx : x ∈ U) : g x ∈ AffineSimplex.massSimplex a L := by
    obtain ⟨v,hv,rfl⟩ := hx
    simpa only [g,Ω,frame.symm_apply_apply,mem_preimage] using hv
  let B := ∑ j : Fin (a+1), Cb*(a+1 : ℝ)^(κ*ε)*
    (InteractionDifferential.boundaryWeight s a.succPNat j+(a+1 : ℝ)*(d+1+a+1 : ℝ)^(-s))
  have hbGood : ∀ j, ∀ᵐ x ∂μ.restrict good, |b j x| ≤ B := by
    intro j
    filter_upwards [ae_restrict_of_ae hsupport,ae_restrict_mem hgood] with x hx hxg
    apply ((hc (g x) (hgs x hx)).1 hxg j).trans
    dsimp only [B]
    exact Finset.single_le_sum
      (f := fun k : Fin (a+1) => Cb*(a+1 : ℝ)^(κ*ε)*
        (InteractionDifferential.boundaryWeight s a.succPNat k+
          (a+1 : ℝ)*(d+1+a+1 : ℝ)^(-s)))
      (fun k _ => by
        have hw := (InteractionDifferential.boundaryWeight_pos s a.succPNat k).le
        positivity) (Finset.mem_univ j)
  have hbBad : ∀ j, ∀ᵐ x ∂μ.restrict goodᶜ, b j x^2 ≤ Cb*(a+1 : ℝ)^Cb*W x := by
    intro j
    exact (ae_restrict_of_ae hsupport).mono fun x hx => (hc (g x) (hgs x hx)).2 j
  let G : BlockObservable a.succPNat := ⟨fun _ => 0,⟨0,by intro x y; simp⟩⟩
  refine ⟨hW,?_⟩
  exact physical_interaction_jet_internal p a d e ha θ ε L hL y z hyL hzL Ky Kz hKy hKz
    hKys hKzs hε G t ht frame M hM μ hV good W B (Cb*(a+1 : ℝ)^Cb) hbGood hW hbBad

end Riesz2.CompatibleComparison
