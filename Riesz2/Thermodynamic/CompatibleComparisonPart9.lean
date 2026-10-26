/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart8

/-!
# A common fine event for compatible conditional comparison

The endpoint tail is transferred at the chosen tolerance.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory Matrix
open Riesz2.InterpolantLocalLaws
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See Appendix C and the proof of Proposition 6.6 in the paper:
weighted exceptional mass and both local laws for any prescribed fine-event
parameter K, provided the endpoint admissibility uses that same K. The
threshold A₀ and the tolerance range depend only on the exponent. -/
theorem chosen_fine_event_local_laws_internal
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A₀ ε₀ : ℝ, 1 < A₀ ∧ 0 < ε₀ ∧
    ∀ A : ℝ, A₀ ≤ A → ∀ K : ℝ,
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
      1 ≤ m → 4*(m+1) ≤ d+m+1 → d ≤ e →
      (m+1 : ℝ)^(2/s) ≤ ((d+m : ℕ)+1 : ℝ) →
    let R := ENNReal.ofReal (C*Real.exp (-c*(m+1 : ℝ)^δ))
    ∀ L : ℝ,
    ∀ y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1),
    ∀ z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1),
    ∀ hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ),
    ∀ hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ),
    admissibleExterior p d m hd θ ε A K y →
    admissibleExterior p e m he θ ε A K z →
        let S := AffineSimplex.massSimplex m L
        let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
          ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
            ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
              (by
                have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
                rw [hr]; exact u.property))⟩
        let Kz := fun u : S => physicalAmbientGapEnergy p (e + m).succPNat
          ⟨RetainedSimplex.assemble e m (InterpolatingDensities.exteriorPermutation e m) z.val u.val,
            ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val
              (by
                have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
                rw [hr]; exact u.property))⟩
        let μ : Measure S := (AffineSimplex.simplexVolume m L).comap Subtype.val
        let P := fun u : S => ∑ i, (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * u.val i) +
          θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (u.val i)⁻¹))
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ h0 ht,
          let ν := (AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
            (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht).map Subtype.val
          IsProbabilityMeasure ν ∧
          (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
              WithLp.ofLp u ∉ goodBlockEvent s m.succPNat (d + m).succPNat (K * ε)},
            ENNReal.ofReal (exceptionalWeight s (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤ R ∧
          (∀ i : Fin (m + 1),
            1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u i ∧
              u i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
          ∀ a b : ℕ, a < b → b ≤ m + 1 →
            ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s 1 / 2) <
              |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u i) -
                (b - a : ℕ)|} ≤ R := by
  obtain ⟨A₀,hA₀,hosc⟩ := InterpolantLocalLaws.physical_coarse_oscillation s hs hs1
  let margin := min (1-min s 1/2) (s-min s 1/2)/4
  have hmargin : 0 < margin := by
    apply div_pos _ (by norm_num)
    exact lt_min (by linarith [min_le_right s 1]) (by linarith [min_le_left s 1])
  refine ⟨A₀,margin,hA₀,hmargin,?_⟩
  intro A hA K ε hε hεsmall
  obtain ⟨n₀,hosc⟩ := hosc ε hε hεsmall
  choose B hBp hBl hBphys using (fun m : ℕ+ => hosc (m : ℕ) m.pos)
  let δ := A₀*ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,hC,htail⟩ := InterpolantLocalLaws.internal_all_size_interpolation_tail
    (A₀*ε) δ βhi (1/2) hδ hδ (by dsimp [δ]; linarith) (by linarith)
    (by norm_num) le_rfl n₀ B hBp (fun m hm => by
      simpa only [Nat.cast_add,Nat.cast_one] using hBl m hm)
  refine ⟨C,1/2,hC,by norm_num,?_⟩
  intro p hps hpl hph d e m hd he hm hsize hde hpower R L y z hcy hcz hy hz
    S Ky Kz μ P t ht0 ht1
  let mpos : ℕ+ := ⟨m,by omega⟩
  have hgy := hy.1
  have hgz := hz.1
  rw [hps] at hgy hgz
  have hphysical := hBphys mpos d e hd he hsize hde
    (by simpa only [mpos,PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hpower) p hps L y z hcy hcz hgy hgz
  have hy₀ := admissible_exterior_mono_internal p d m hd θ ε hε.le hA le_rfl y hy
  have hz₀ := admissible_exterior_mono_internal p e m he θ ε hε.le hA le_rfl z hz
  obtain ⟨h0,htop,hprob,hbad⟩ := InterpolantLocalLaws.Internal.physical_interpolant_transfer
    p d e m hd he θ ε A₀ K L y z hcy hcz hy₀ hz₀ (B mpos) (hBp mpos).le
    (fun u v hu hv => hphysical u v
      (by simpa only [hps,mpos,PNat.mk_coe] using hu)
      (by simpa only [hps,mpos,PNat.mk_coe] using hv)) t ht0 ht1
  refine ⟨h0,htop,hprob,?_⟩
  let ρ := AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
    (Real.exp (-p.val.1*(P u+(1-t)*Ky u+t*Kz u)))) h0 htop
  let ν := ρ.map Subtype.val
  let : IsProbabilityMeasure ν := hprob
  rw [hps] at hbad
  have hnum := htail p.val.1 p.property.1.le hph mpos
  have hbad' : (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m+1)) |
      WithLp.ofLp u ∉ goodBlockEvent s m.succPNat (d+m).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := m.succPNat) s
        (WithLp.ofLp u)) ∂ν) ≤ R := by
    apply hbad.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [δ,mpos,PNat.mk_coe,Nat.cast_add,Nat.cast_one,
      show 2*A₀*ε = 2*(A₀*ε) by ring] using hnum
  refine ⟨hbad',?_⟩
  have hnonneg : ∀ᵐ u ∂ν, ∀ i, 0 ≤ u i := by
    apply (MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex m L)).ae_map_iff.mpr
    exact ae_of_all _ (fun u i => (u.property.1 i).le)
  exact InterpolantLocalLaws.Internal.block_events_of_weighted_failure
    s (K*ε) m.succPNat (d+m).succPNat ν hnonneg hbad'

/-- See the proof of Proposition 6.6 and Lemma 6.4 of the paper: at any chosen
fine-event parameter, the actual chart Gibbs law has a quantitative weighted
tail, an integrable exceptional envelope, and the literal interaction jet.
All parameters refer to the same endpoint admissibility and the same event.
 -/
theorem chosen_fine_event_jet_internal
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A₀ ε₀ : ℝ, 1 < A₀ ∧ 0 < ε₀ ∧
    ∀ A : ℝ, A₀ ≤ A → ∀ K : ℝ, 1 < K →
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
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
    (∫⁻ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
        (WithLp.ofLp (g x))) ∂μ) ≤
      ENNReal.ofReal (C*Real.exp (-c*(a+1 : ℝ)^δ)) ∧
    (∫ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)},
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
        (WithLp.ofLp (g x)) ∂μ) ≤ C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    μ.real {x | WithLp.ofLp (g x) ∉
      goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)} ≤
      C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp (g x)))
      {x | WithLp.ofLp (g x) ∉ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)} μ ∧
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap M.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  obtain ⟨A₀,εbase,hA₀,hεbase,hlocal⟩ :=
    chosen_fine_event_local_laws_internal s hs hs1
  let margin := min (1-min s 1/2) (s-min s 1/2)/4
  have hmargin : 0 < margin := by
    have hσ : min s 1/2 < 1 := by have := min_le_right s 1; linarith
    have hsσ : min s 1/2 < s := by
      rcases le_total s 1 with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    exact div_pos (lt_min (sub_pos.mpr hσ) (sub_pos.mpr hsσ)) (by norm_num)
  refine ⟨A₀,min εbase margin,hA₀,lt_min hεbase hmargin,?_⟩
  intro A hA K hK ε hε hεsmall
  obtain ⟨δ,hδ,hlocal⟩ := hlocal A hA K ε hε (hεsmall.trans_le (min_le_left _ _))
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨Cl,cl,hCl,hcl,hlocal⟩ := hlocal βlo βhi hlo hle θ
  refine ⟨Cl,cl,hCl,hcl,?_⟩
  intro p hps hpl hph a d e ha hsize hde hpower L hL y z hy hz hyL hzL
    Ky Kz hKy hKz t ht frame M hM Ω U g V D b μ hV hU hB
  have hKys := physical_realization_smooth_internal p a d y Ky hKy
  have hKzs := physical_realization_smooth_internal p a e z Kz hKz
  obtain ⟨Cb,κ,hCb,_hκ,hcoeff⟩ := physical_differential_bounds_internal s hs hs1 K hK ε hε
    (hεsmall.trans_le (min_le_right _ _))
  have hc := hcoeff a d e ha hsize hde hpower p hps θ A L (hA₀.trans_le hA) y z hy hz hyL hzL Ky Kz hKy hKz
  have hlocal := hlocal p hps hpl hph (d+1) (e+1) a (by omega) (by omega)
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
  have htail : (∫⁻ x in goodᶜ, ENNReal.ofReal (W x) ∂μ) ≤
      ENNReal.ofReal (Cl*Real.exp (-cl*(a+1 : ℝ)^δ)) := by
    rw [← hmap, setLIntegral_map] at hbadρ
    · exact hbadρ
    · exact ((InterpolantLocalLaws.measurableSet_goodBlockEvent s a.succPNat
        (d+1+a).succPNat (K*ε)).preimage (WithLp.measurable_ofLp 2 _)).compl
    · exact (InterpolantLocalLaws.measurable_exceptionalWeight (n := a.succPNat) s
        (fun u : EuclideanSpace ℝ (Fin (a+1)) => WithLp.ofLp u)
        (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)).ennreal_ofReal
    · exact ((AffineSimplex.isometry_centredChart a L).continuous.comp
        frame.symm.continuous).measurable
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
  have hWone : ∀ᵐ x ∂μ.restrict goodᶜ, 1 ≤ W x := by
    filter_upwards [ae_restrict_of_ae hsupport] with x hx
    exact InterpolantLocalLaws.one_le_exceptionalWeight (n := a.succPNat) s _
      (fun i => ((hgs x hx).1 i).le)
  have hWmeas : Measurable W := InterpolantLocalLaws.measurable_exceptionalWeight
    (n := a.succPNat) s (fun x => WithLp.ofLp (g x))
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hg.measurable)
  have hdata := GoodSetL2Comparison.tail_data W hWmeas.aestronglyMeasurable
    (by positivity) hWone htail
  let G : BlockObservable a.succPNat := ⟨fun _ => 0,⟨0,by intro x y; simp⟩⟩
  refine ⟨htail,hdata.2.1,hdata.2.2,hW,?_⟩
  exact physical_interaction_jet_internal p a d e ha θ ε L hL y z hyL hzL Ky Kz hKy hKz
    hKys hKzs hε G t ht frame M hM μ hV good W B (Cb*(a+1 : ℝ)^Cb) hbGood hW hbBad


/-- See the proof of Proposition 6.6 in the paper: one long-range
admissibility choice for the coordinate and interval local laws, the chart tail and
interaction jet, and the physical decay time family. Every exceptional integral
uses the complement of the very same fine event with parameter K*ε. The three
tail powers are chosen before the compact temperature interval. -/
theorem long_range_common_choice_internal (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
      1 ≤ m → 4*(m+1) ≤ d+m+1 → d ≤ e →
      (m+1 : ℝ)^(2/s.val) ≤ ((d+m : ℕ)+1 : ℝ) →
    let R := ENNReal.ofReal (C*Real.exp (-c*(m+1 : ℝ)^δ))
    ∀ L : ℝ,
    ∀ y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1),
    ∀ z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1),
    ∀ hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ),
    ∀ hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ),
    admissibleExterior p d m hd θ ε A K y →
    admissibleExterior p e m he θ ε A K z →
        let S := AffineSimplex.massSimplex m L
        let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
          ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
            ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
              (by
                have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
                rw [hr]; exact u.property))⟩
        let Kz := fun u : S => physicalAmbientGapEnergy p (e + m).succPNat
          ⟨RetainedSimplex.assemble e m (InterpolatingDensities.exteriorPermutation e m) z.val u.val,
            ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val
              (by
                have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
                rw [hr]; exact u.property))⟩
        let μ : Measure S := (AffineSimplex.simplexVolume m L).comap Subtype.val
        let P := fun u : S => ∑ i, (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * u.val i) +
          θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (u.val i)⁻¹))
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ h0 ht,
          let ν := (AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
            (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht).map Subtype.val
          IsProbabilityMeasure ν ∧
          (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
              WithLp.ofLp u ∉ goodBlockEvent s.val m.succPNat (d + m).succPNat (K * ε)},
            ENNReal.ofReal (exceptionalWeight s.val (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤ R ∧
          (∀ i : Fin (m + 1),
            1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u i ∧
              u i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
          ∀ a b : ℕ, a < b → b ≤ m + 1 →
            ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s.val 1 / 2) <
              |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u i) -
                (b - a : ℕ)|} ≤ R) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (p : Parameters), p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s.val) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
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
    (∫⁻ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x))) ∂μ) ≤
      ENNReal.ofReal (C*Real.exp (-c*(a+1 : ℝ)^δ)) ∧
    (∫ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x)) ∂μ) ≤ C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    μ.real {x | WithLp.ofLp (g x) ∉
      goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} ≤
      C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp (g x)))
      {x | WithLp.ofLp (g x) ∉ goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} μ ∧
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap M.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F)) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
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
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  obtain ⟨Ad,K,εd,κ,hAd,hK,hεd,hκ,hdec⟩ :=
    long_range_decay_time_family_internal hzeta hRig s
  obtain ⟨Al,εl,hAl,hεl,hlocal⟩ :=
    chosen_fine_event_local_laws_internal s.val s.property.1 (ne_of_lt s.property.2)
  obtain ⟨Aj,εj,hAj,hεj,hjet⟩ :=
    chosen_fine_event_jet_internal s.val s.property.1 (ne_of_lt s.property.2)
  let A := max Ad (max Al Aj)
  let ε₀ := min εd (min εl εj)
  have hAdA : Ad ≤ A := le_max_left _ _
  have hAlA : Al ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAjA : Aj ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεl hεj)
  refine ⟨A,K,ε₀,κ,hAd.trans_le hAdA,hK,hε₀,hκ,?_,?_,?_⟩
  · intro ε hε hsmall
    exact hlocal A hAlA K ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  · intro ε hε hsmall
    exact hjet A hAjA K hK ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  · intro ε hε hsmall
    obtain ⟨δ,hδ,hdec⟩ := hdec ε hε (hsmall.trans_le (min_le_left _ _))
    refine ⟨δ,hδ,?_⟩
    intro βlo βhi hlo hle θ
    obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
    refine ⟨C,c,hC,hc,?_⟩
    intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz
    have hy₀ := admissible_exterior_mono_internal (ofLong β s)
      (d+1) a (by omega) θ ε hε.le hAdA le_rfl y hy
    have hz₀ := admissible_exterior_mono_internal (ofLong β s)
      (e+1) a (by omega) θ ε hε.le hAdA le_rfl z hz
    exact hdec β hβ a d e ha hde hsize hpower y z L hyL hzL hy₀ hz₀

/-- See the proof of Proposition 6.6 in the paper: one short-range
admissibility choice for the coordinate and interval local laws, the chart tail and
interaction jet, and the physical decay time family. Every exceptional integral
uses the complement of the very same fine event with parameter K*ε. The three
tail powers are chosen before the compact temperature interval. -/
theorem short_range_common_choice_internal (hRig : External.LongRangeRigidityLocallyUniform) (s : ShortExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
      1 ≤ m → 4*(m+1) ≤ d+m+1 → d ≤ e →
      (m+1 : ℝ)^(2/s.val) ≤ ((d+m : ℕ)+1 : ℝ) →
    let R := ENNReal.ofReal (C*Real.exp (-c*(m+1 : ℝ)^δ))
    ∀ L : ℝ,
    ∀ y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1),
    ∀ z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1),
    ∀ hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ),
    ∀ hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ),
    admissibleExterior p d m hd θ ε A K y →
    admissibleExterior p e m he θ ε A K z →
        let S := AffineSimplex.massSimplex m L
        let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
          ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
            ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
              (by
                have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
                rw [hr]; exact u.property))⟩
        let Kz := fun u : S => physicalAmbientGapEnergy p (e + m).succPNat
          ⟨RetainedSimplex.assemble e m (InterpolatingDensities.exteriorPermutation e m) z.val u.val,
            ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val
              (by
                have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
                rw [hr]; exact u.property))⟩
        let μ : Measure S := (AffineSimplex.simplexVolume m L).comap Subtype.val
        let P := fun u : S => ∑ i, (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * u.val i) +
          θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (u.val i)⁻¹))
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ h0 ht,
          let ν := (AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
            (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht).map Subtype.val
          IsProbabilityMeasure ν ∧
          (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
              WithLp.ofLp u ∉ goodBlockEvent s.val m.succPNat (d + m).succPNat (K * ε)},
            ENNReal.ofReal (exceptionalWeight s.val (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤ R ∧
          (∀ i : Fin (m + 1),
            1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u i ∧
              u i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
          ∀ a b : ℕ, a < b → b ≤ m + 1 →
            ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s.val 1 / 2) <
              |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u i) -
                (b - a : ℕ)|} ≤ R) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (p : Parameters), p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s.val) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
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
    (∫⁻ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x))) ∂μ) ≤
      ENNReal.ofReal (C*Real.exp (-c*(a+1 : ℝ)^δ)) ∧
    (∫ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x)) ∂μ) ≤ C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    μ.real {x | WithLp.ofLp (g x) ∉
      goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} ≤
      C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp (g x)))
      {x | WithLp.ofLp (g x) ∉ goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} μ ∧
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap M.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F)) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
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
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  obtain ⟨Ad,K,εd,κ,hAd,hK,hεd,hκ,hdec⟩ :=
    short_range_decay_time_family_internal hRig s
  obtain ⟨Al,εl,hAl,hεl,hlocal⟩ :=
    chosen_fine_event_local_laws_internal s.val (zero_lt_one.trans s.property) (ne_of_gt s.property)
  obtain ⟨Aj,εj,hAj,hεj,hjet⟩ :=
    chosen_fine_event_jet_internal s.val (zero_lt_one.trans s.property) (ne_of_gt s.property)
  let A := max Ad (max Al Aj)
  let ε₀ := min εd (min εl εj)
  have hAdA : Ad ≤ A := le_max_left _ _
  have hAlA : Al ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAjA : Aj ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεl hεj)
  refine ⟨A,K,ε₀,κ,hAd.trans_le hAdA,hK,hε₀,hκ,?_,?_,?_⟩
  · intro ε hε hsmall
    exact hlocal A hAlA K ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  · intro ε hε hsmall
    exact hjet A hAjA K hK ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  · intro ε hε hsmall
    obtain ⟨δ,hδ,hdec⟩ := hdec ε hε (hsmall.trans_le (min_le_left _ _))
    refine ⟨δ,hδ,?_⟩
    intro βlo βhi hlo hle θ
    obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
    refine ⟨C,c,hC,hc,?_⟩
    intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz
    have hy₀ := admissible_exterior_mono_internal (ofShort β s)
      (d+1) a (by omega) θ ε hε.le hAdA le_rfl y hy
    have hz₀ := admissible_exterior_mono_internal (ofShort β s)
      (e+1) a (by omega) θ ε hε.le hAdA le_rfl z hz
    exact hdec β hβ a d e ha hde hsize hpower y z L hyL hzL hy₀ hz₀

end Riesz2.CompatibleComparison
