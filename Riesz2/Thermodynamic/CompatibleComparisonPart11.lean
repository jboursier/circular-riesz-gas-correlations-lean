/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart9
public import Riesz2.Thermodynamic.CompatibleComparisonPart4

/-!
# Integration of compatible physical point sources

Composition steps for the proof of Proposition 6.6, assuming the uniform differential
estimate.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper: reduce two stretched exponential
powers to their positive minimum, before the temperature is chosen. -/
theorem exponential_tail_power_mono_internal (n δ δ' c : ℝ)
    (hn : 1 ≤ n) (hδ : δ ≤ δ') (hc : 0 ≤ c) :
    Real.exp (-c*n^δ') ≤ Real.exp (-c*n^δ) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (Real.rpow_le_rpow_of_exponent_le hn hδ) (neg_nonpos.mpr hc)

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the weighted bad
mass on an orthonormal chart is exactly its mass on the included physical
carrier. No conditional law on a null fibre is selected. -/
theorem physical_tail_transport_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (s η : ℝ) (P : ℕ+) :
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let ν := (μ.comap (Subtype.val : U → _)).map
      (InterpolationTransport.orthonormalInclusion a L N hLN frame)
    (∫⁻ x in {x | WithLp.ofLp x.val ∉ goodBlockEvent s a.succPNat P η},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
        (WithLp.ofLp x.val)) ∂ν) =
    ∫⁻ x in {x | WithLp.ofLp (g x) ∉ goodBlockEvent s a.succPNat P η},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s
        (WithLp.ofLp (g x))) ∂μ := by
  intro g U ν
  let E := {x : EuclideanSpace ℝ (Fin (a+1)) |
    WithLp.ofLp x ∉ goodBlockEvent s a.succPNat P η}
  let W := fun x : EuclideanSpace ℝ (Fin (a+1)) =>
    ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp x))
  have hE : MeasurableSet E :=
    ((InterpolantLocalLaws.measurableSet_goodBlockEvent s a.succPNat P η).preimage
      (WithLp.measurable_ofLp 2 _)).compl
  have hW : Measurable W :=
    (InterpolantLocalLaws.measurable_exceptionalWeight (n := a.succPNat) s
      (fun x : EuclideanSpace ℝ (Fin (a+1)) => WithLp.ofLp x)
      (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)).ennreal_ofReal
  have hg : Measurable g := (AffineSimplex.isometry_centredChart a L).continuous.measurable.comp
    frame.symm.continuous.measurable
  have he := (InterpolationTransport.orthonormal_law a L N hLN frame μ V hV).2
  have hh := congrArg (fun ρ => ∫⁻ x in E, W x ∂ρ) he
  rw [setLIntegral_map hE hW measurable_subtype_coe,
    setLIntegral_map hE hW hg] at hh
  exact hh

/-- See the proof of Proposition 6.6 in the paper: actual smooth integration on the
original physical form family. The hypotheses are the pointwise differential
bounds and the two quantitative decay conclusions. This is an internal
composition lemma, with constants selected before any size or exterior. -/
theorem physical_smooth_family_comparison_internal
    (s : ℝ) (hs : 0 < s) (βlo Cb κb Ct ct Cd cd δ κ ε : ℝ)
    (hβlo : 0 < βlo) (hCb : 0 < Cb) (hCt : 0 < Ct) (hct : 0 < ct)
    (hCd : 0 < Cd) (hcd : 0 < cd) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ Cf cf : ℝ, 0 < Cf ∧ 0 < cf ∧
    ∀ (p : Parameters) (a d e : ℕ) (_ha : 1 ≤ a)
      (θ : PhysicalCutoff) (L : ℝ) (_hL : 0 < L)
      (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1))
      (_hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L)
      (_hzL : ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L)
      (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
      (_hKy : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩)
      (_hKz : ∀ u (hu : RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
        gapAmbientDomain (e+1+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a
          (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩)

      (_hps : p.val.2 = s) (_hβ : βlo ≤ p.val.1)
      (_hsize : (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ)),
    ∀ (Bcarrier : ℝ) (hLN : L < Bcarrier)
      (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)),
    let N : ℕ+ := (d+1+a).succPNat
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let b := fun i u => InteractionDifferential.pinnedRepresentative (fun k : Fin a =>
      fderiv ℝ (fun v => Ky v-Kz v) u
        (WithLp.toLp 2 (Pi.single k.castSucc 1-Pi.single k.succ 1))) i
    ∀ (η : ℝ) (_hη : 0 < η) (_hN : a+1 < (N : ℕ)),
    let E := goodBlockEvent s a.succPNat N η
    let W := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)
    (∀ u ∈ AffineSimplex.massSimplex a L,
      (WithLp.ofLp u ∈ E → ∀ i, |b i u| ≤ Cb*(a+1 : ℝ)^(κb*ε)*
        (InteractionDifferential.boundaryWeight s a.succPNat i+
          (a+1 : ℝ)*(N : ℝ)^(-s))) ∧
      (∀ i, b i u^2 ≤ Cb*(a+1 : ℝ)^Cb*W u)) →
    ∀ (μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)))
      (_hμ : ∀ t, IsProbabilityMeasure (μ t))
      (_hV : ∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)),
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
      (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
    ∀ (Q : (t : ℝ) → ScalarFormData (ν t))
      (_hν : ∀ t, IsProbabilityMeasure (ν t))
      (_hQ : ∀ t, IsClosedScalarDirichletForm (Q t))
      (_hform : ∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L _ hLN frame (ν t) (Q t)),
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∫⁻ x in {x | WithLp.ofLp (g x) ∉ E}, ENNReal.ofReal (W (g x)) ∂μ t) ≤
        ENNReal.ofReal (Ct*Real.exp (-ct*(a+1 : ℝ)^δ))) →
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
            (‖χ.val‖+Real.exp (-cd*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) →
    ∀ (G : BlockObservable a.succPNat) (_hsG : ContDiff ℝ ∞ G.val)
      (J : Finset (Fin (a+1))) (_hJ : DependsOnBlockCoordinates G J),
      (∀ i ∈ J, |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4) →
      |(∫ x, G.val (WithLp.ofLp x.val) ∂ν 1)-
        (∫ x, G.val (WithLp.ofLp x.val) ∂ν 0)| ≤
      p.val.1*Cf*(a+1 : ℝ)^((κ+κb)*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G J E+
          Real.exp (-cf*(a+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  let Umax := (βlo*min 1 (s*(s+1)))⁻¹
  have hUmax : 0 ≤ Umax := by dsimp only [Umax]; positivity
  obtain ⟨Cf,cf,hCf,hcf,hcomp⟩ := integrated_comparison_from_decay_internal
    s hs Cb Cb Ct Cd Umax κ κb ε cd ct δ ((s+2)*ε) (Cb/2)
    hCb hCb.le hCt.le hCd hUmax hcd hct hδ
  refine ⟨Cf,cf,hCf,hcf,?_⟩
  intro p a d e ha θ L hL y z hyL hzL Ky Kz hKy hKz hps hβ hsize Bcarrier hLN frame
    N H U g b η hη hN E W hc μ hμ hV ν Q hν hQ hform htail hdec G hsG J hJ hmiddle
  let := hμ
  let := hν
  have hKys := physical_realization_smooth_internal p a d y Ky hKy
  have hKzs := physical_realization_smooth_internal p a e z Kz hKz
  have hg : Continuous g := (AffineSimplex.isometry_centredChart a L).continuous.comp frame.symm.continuous
  have hgs (x) (hx : x ∈ U) : g x ∈ AffineSimplex.massSimplex a L := by
    obtain ⟨w,hw,rfl⟩ := hx
    simpa only [g,frame.symm_apply_apply,mem_preimage] using hw
  have hEs := InterpolantLocalLaws.measurableSet_goodBlockEvent s a.succPNat N η
  have hWm : Measurable W := InterpolantLocalLaws.measurable_exceptionalWeight
    (n := a.succPNat) s (fun u : EuclideanSpace ℝ (Fin (a+1)) => WithLp.ofLp u)
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)
  have hEm : MeasurableSet {x : EuclideanSpace ℝ (Fin (a+1)) | WithLp.ofLp x ∈ E} :=
    hEs.preimage (WithLp.measurable_ofLp 2 _)
  have hsupport (t) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∀ᵐ x ∂μ t, x ∈ U :=
    IntrinsicScalarCore.supported (frame.toHomeomorph.isOpenMap _
      (ConditionalWellPosedness.fibre_isOpen a L)) (hV t ht)
  have hsν (t) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∀ᵐ x ∂ν t, x.val ∈ AffineSimplex.massSimplex a L := by
    rw [(InterpolationTransport.measurableEmbedding_orthonormalInclusion a L _ hLN frame).ae_map_iff]
    exact ae_of_all _ fun x => hgs x.val x.property
  have htailμ (t) (ht : t ∈ Icc (0 : ℝ) 1) :=
    GoodSetL2Comparison.tail_data (fun x => W (g x))
      (hWm.comp hg.measurable).aestronglyMeasurable
      (by positivity : 0 ≤ Ct*Real.exp (-ct*(a+1 : ℝ)^δ))
      ((ae_restrict_of_ae (hsupport t ht)).mono fun x hx =>
        InterpolantLocalLaws.one_le_exceptionalWeight s _ (fun i => ((hgs x hx).1 i).le))
      (htail t ht)
  have htailν (t) (ht : t ∈ Icc (0 : ℝ) 1) :=
    GoodSetL2Comparison.tail_data (fun x : AffineSimplex.chartDomain (a+1) _ => W x.val)
      (hWm.comp measurable_subtype_coe).aestronglyMeasurable
      (by positivity : 0 ≤ Ct*Real.exp (-ct*(a+1 : ℝ)^δ))
      ((ae_restrict_of_ae (hsν t ht)).mono fun x hx =>
        InterpolantLocalLaws.one_le_exceptionalWeight s _ (fun i => (hx.1 i).le))
      ((physical_tail_transport_internal a L _ hLN frame (μ t) _ (hV t ht) s η N).trans_le (htail t ht))
  let B := Cb*(a+1 : ℝ)^(κb*ε)*
    (∑ j, (InteractionDifferential.boundaryWeight s a.succPNat j+(a+1 : ℝ)*(N : ℝ)^(-s)))
  have hbμ (t) (ht : t ∈ Icc (0 : ℝ) 1) (i) :
      ∀ᵐ x ∂(μ t).restrict {x | WithLp.ofLp (g x) ∈ E}, |b i (g x)| ≤ B := by
    filter_upwards [ae_restrict_of_ae (hsupport t ht),ae_restrict_mem (hEm.preimage hg.measurable)] with x hx he
    apply ((hc (g x) (hgs x hx)).1 he i).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (fun j _ => add_nonneg
      (InteractionDifferential.boundaryWeight_pos s a.succPNat j).le (by positivity)) (Finset.mem_univ i)
  have hsqμ (t) (ht : t ∈ Icc (0 : ℝ) 1) (i) :
      ∀ᵐ x ∂(μ t).restrict {x | WithLp.ofLp (g x) ∈ E}ᶜ,
        b i (g x)*b i (g x) ≤ (Cb*(a+1 : ℝ)^Cb)*W (g x) := by
    filter_upwards [ae_restrict_of_ae (hsupport t ht)] with x hx
    simpa only [pow_two] using (hc (g x) (hgs x hx)).2 i
  obtain ⟨hnorm,χ,hχ,hglobal,hlocal,hid⟩ :=
    physical_integrated_point_sources_internal p a d e ha θ ε L hL y z hyL hzL
      Ky Kz hKy hKz hKys hKzs hε G hsG J hJ E
      (InterpolantLocalLaws.convex_goodBlockEvent s a.succPNat N η)
      ⟨_,one_mem_interior_fine_event s η hη a.succPNat N (by change 2 ≤ a+1; omega) hN⟩
      hEs _ hLN frame μ (fun t => inferInstance) hV Q (fun t _ => hform t)
      (fun _ => {x | WithLp.ofLp (g x) ∈ E}) (fun _ x => W (g x)) (fun _ => B)
      (fun _ => Cb*(a+1 : ℝ)^Cb) hbμ (fun t ht => (htailμ t ht).1) hsqμ
  classical
  have hex (t : ℝ) (i : Fin (a+1)) : ∃ ψ : Fin (a+1) → (Q t).1,
      (t ∈ Icc (0 : ℝ) 1 → i ∈ J → WeightedWeakSolution (Q t)
        (fun x => hessianMatrix (H t) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then (χ t i).val else 0) ψ) := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · by_cases hi : i ∈ J
      · obtain ⟨ψ,hψ⟩ := (hdec t ht i (hmiddle i hi) (χ t i)).1
        exact ⟨ψ,fun _ _ => hψ⟩
      · exact ⟨0,fun _ hi' => False.elim (hi hi')⟩
    · exact ⟨0,fun ht' => False.elim (ht ht')⟩
  choose ψ hψ using hex
  have hidentity := (hid ψ (fun t ht i hi => hψ t i ht hi)).2
  have hmax (t) (ht : t ∈ Icc (0 : ℝ) 1) (i) (hi : i ∈ J) (j) :
      ∀ᵐ x ∂ν t, |(ψ t i j).val x| ≤
        (Umax*(a+1 : ℝ)^((s+2)*ε))*(eLpNorm ((χ t i).val : _ → ℝ) ∞ (ν t)).toReal := by
    obtain ⟨h0,htop,he⟩ := hnorm t ht
    have hh := physical_point_source_maximum_internal p a d e ha θ ε L y z hyL hzL
      Ky Kz hKy hKz hKys hKzs hε.le t ht _ hLN
      (AffineFibre.normalizedMeasure _ _ h0 htop)
    rw [← he] at hh
    have hb := hh (Q t) (hQ t) i (χ t i) (ψ t i) (hψ t i ht hi) j
    have hcoef : (p.val.1*min 1 (p.val.2*(p.val.2+1)))*
        (a+1 : ℝ)^(-(p.val.2+2)*ε) ≥
        (βlo*min 1 (s*(s+1)))*(a+1 : ℝ)^(-((s+2)*ε)) := by
      rw [hps]
      rw [show -(s+2)*ε = -((s+2)*ε) by ring]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hβ (by positivity : 0 ≤ min 1 (s*(s+1))))
        (by positivity)
    have hbase : 0 < (βlo*min 1 (s*(s+1)))*(a+1 : ℝ)^(-((s+2)*ε)) := by positivity
    have hci := inv_anti₀ hbase hcoef
    have hinv : ((βlo*min 1 (s*(s+1)))*(a+1 : ℝ)^(-((s+2)*ε)))⁻¹ =
        Umax*(a+1 : ℝ)^((s+2)*ε) := by
      simp only [Umax,_root_.mul_inv_rev,Real.rpow_neg (by positivity : 0 ≤ (a+1 : ℝ)),inv_inv]
      ring
    rw [hinv] at hci
    filter_upwards [hb] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right (by simpa only [Umax,mul_comm] using hci) ENNReal.toReal_nonneg)
  have hpβ : 0 < p.val.1 := p.property.1
  obtain ⟨hA,hB,hsumA,hsumB⟩ := frozen_source_constants_internal G J E
  have hbs : ∀ i, Measurable (fun x : AffineSimplex.chartDomain (a+1) Bcarrier => b i x.val) := by
    intro i
    have hgrad : Measurable (gradient (fun v => Ky v-Kz v)) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (a+1)))).symm.continuous.measurable.comp
        (measurable_fderiv ℝ (fun v => Ky v-Kz v))
    have hv : Measurable (Subtype.val : AffineSimplex.chartDomain (a+1)
        Bcarrier → EuclideanSpace ℝ (Fin (a+1))) := measurable_subtype_coe
    have hp := ((PiLp.continuous_apply 2 (fun _ : Fin (a+1) => ℝ) i).measurable.comp
      (hgrad.comp hv)).sub
        ((PiLp.continuous_apply 2 (fun _ : Fin (a+1) => ℝ)
          (InteractionDifferential.middle a)).measurable.comp (hgrad.comp hv))
    convert hp using 1
    funext x
    exact congrFun (pinned_gradient_internal (fun v => Ky v-Kz v) x.val) i
  have hncast : (a.succPNat : ℝ) = a+1 := by simp
  have hcomp' := hcomp a.succPNat N (by
    simpa only [N,Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using hsize)
  simp only [hncast] at hcomp'
  have hresult := hcomp' _ ν J χ (fun t i j => (ψ t i j).val) (fun _ i x => b i x.val)
    (fun _ x => W x.val) (fun _ => {x | WithLp.ofLp x.val ∈ E})
    (fun i => restrictedBlockDerivativeNorm G {i} E) (fun i => (coordinateDerivativeNorm G i : ℝ))
    p.val.1 p.property.1.le (fun t => ∫ x, G.val (WithLp.ofLp x.val) ∂ν t)
    (fun i _ => hA i) (fun i _ => hB i)
    (fun _ _ => hEm.preimage measurable_subtype_coe)
    (fun _ _ i => (hbs i).aestronglyMeasurable)
    (fun t _ i _ => hlocal t i) (fun t _ i _ => hglobal t i)
    (fun t ht i => ?_) (fun t ht => (htailν t ht).1)
    (fun t ht i => ?_) (fun t ht => (htailν t ht).2.1)
    (fun t ht => (htailν t ht).2.2) hmax
    (fun t ht i hi => (hdec t ht i (hmiddle i hi) (χ t i)).2 _ (hψ t i ht hi)) hidentity
  · rw [hsumA] at hresult
    apply hresult.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity :
      0 ≤ p.val.1*Cf*(a+1 : ℝ)^((κ+κb)*ε-min s 1/2))
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsumB (Real.exp_pos _).le)
  · filter_upwards [ae_restrict_of_ae (hsν t ht),
      ae_restrict_mem (hEm.preimage measurable_subtype_coe)] with x hx he
    exact (hc x.val hx).1 he i
  · filter_upwards [ae_restrict_of_ae (hsν t ht)] with x hx
    have hh := (hc x.val hx).2 i
    have he : ((a+1 : ℝ)^(Cb/2))^2 = (a+1 : ℝ)^Cb := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
      congr 1
      ring
    simpa only [Nat.succPNat_coe,Nat.cast_succ,he] using hh

/-- See the proof of Proposition 6.6 in the paper: the smooth bound on included
physical laws yields the full Lipschitz bound on their literal Hausdorff
endpoint laws, preserving the same constants and derivative norms. -/
theorem included_lipschitz_comparison_internal (s η : ℝ) (hη : 0 < η)
    (a : ℕ) (ha : 1 ≤ a) (N : ℕ+) (hN : a+1 < (N : ℕ))
    (L : ℝ) (hL : 0 < L) (Bcarrier : ℝ) (hLN : L < Bcarrier)
    (w z : AffineSimplex.massSimplex a L → ℝ≥0∞) (hw : Measurable w) (hz : Measurable z)
    (hw0 : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
    (hwt : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤)
    (hz0 : (∫⁻ x, z x ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
    (hzt : (∫⁻ x, z x ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤)
    (C c κ ε δ : ℝ) (hC : 0 ≤ C) :
    let ρ₀ := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) w hw0 hwt
    let ρ₁ := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) z hz0 hzt
    let ν₀ := ρ₀.map (InterpolationTransport.inclusion a L Bcarrier hLN)
    let ν₁ := ρ₁.map (InterpolationTransport.inclusion a L Bcarrier hLN)
    (∀ (G : BlockObservable a.succPNat), ContDiff ℝ ∞ G.val →
      ∀ J : Finset (Fin (a+1)), DependsOnBlockCoordinates G J →
      (∀ i ∈ J, |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4) →
      |(∫ x, G.val (WithLp.ofLp x.val) ∂ν₁)-(∫ x, G.val (WithLp.ofLp x.val) ∂ν₀)| ≤
        C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s a.succPNat N η)+
            Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G)) →
    ∀ (G : BlockObservable a.succPNat) (J : Finset (Fin (a+1))),
      DependsOnBlockCoordinates G J →
      (∀ i ∈ J, |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4) →
      Integrable (fun x => G.val (WithLp.ofLp x.val)) ρ₀ ∧
      Integrable (fun x => G.val (WithLp.ofLp x.val)) ρ₁ ∧
      |(∫ x, G.val (WithLp.ofLp x.val) ∂ρ₀)-(∫ x, G.val (WithLp.ofLp x.val) ∂ρ₁)| ≤
        C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s a.succPNat N η)+
            Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  intro ρ₀ ρ₁ ν₀ ν₁ hsm G J hJ hmiddle
  have hi (G : BlockObservable a.succPNat) (ρ : Measure (AffineSimplex.massSimplex a L)) :
      (∫ x, G.val (WithLp.ofLp x.val) ∂ρ.map (InterpolationTransport.inclusion a L Bcarrier hLN)) =
      ∫ x, G.val (WithLp.ofLp x.val) ∂ρ := by
    obtain ⟨k,hk⟩ := G.property
    exact integral_map (InterpolationTransport.measurableEmbedding_inclusion a L _ hLN).measurable.aemeasurable
      (hk.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hsm' : ∀ F : BlockObservable a.succPNat, ContDiff ℝ ∞ F.val →
      DependsOnBlockCoordinates F J →
      |(∫ x, F.val (WithLp.ofLp x.val) ∂ρ₀)-(∫ x, F.val (WithLp.ofLp x.val) ∂ρ₁)| ≤
        C*((a+1 : ℕ) : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm F J (goodBlockEvent s a.succPNat N η)+
            Real.exp (-c*((a+1 : ℕ) : ℝ)^δ)*blockDerivativeNorm F) := by
    intro F hsF hFJ
    have hh := hsm F hsF J hFJ hmiddle
    rw [hi F ρ₁,hi F ρ₀,abs_sub_comm] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  simpa only [Nat.cast_add,Nat.cast_one] using
    lipschitz_comparison_of_smooth_internal s η hη a N (by omega) hN
      L hL J w z hw hz hw0 hwt hz0 hzt C c κ ε δ hC hsm' G hJ

/-- See the proof of Proposition 6.6 in the paper: synchronized physical family and
quantitative tail in the specified exponent regime. -/
theorem long_common_physical_family_internal (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1) (hsl : s < 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
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
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,_,hj,hd⟩ :=
    long_range_common_choice_internal hzeta hRig s₀
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,?_⟩
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


/-- See the proof of Proposition 6.6 in the paper: synchronized physical family and
quantitative tail in the specified exponent regime. -/
theorem short_common_physical_family_internal (_hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (_hs : 0 < s) (hs1 : s ≠ 1) (hsl : ¬ s < 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
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
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,_,hj,hd⟩ :=
    short_range_common_choice_internal hRig s₀
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,?_⟩
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


/-- See the proof of Proposition 6.6 in the paper: synchronized physical family and
quantitative tail in the specified exponent regime. -/
theorem common_physical_family_internal (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
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
  · exact long_common_physical_family_internal hzeta hRig s hs hs1 hsl
  · exact short_common_physical_family_internal hzeta hRig s hs hs1 hsl

/-- The compatible fixed-length comparison in the proof of Proposition 6.6,
assuming the uniform differential estimate. Every Lipschitz observable is
integrable. The loss precedes the tolerance and the tail power precedes
the compact inverse-temperature interval. -/
theorem compatible_conditional_comparison_internal (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hDiff : ∀ (K : ℝ), 1 < K →
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1-min s 1/2) (s-min s 1/2)/4 →
    ∃ C : ℝ, 0 < C ∧ ∀ a d e : ℕ, 1 ≤ a →
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
        InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u))) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    K*ε+min s 1/2 ≤ 1 ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
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
    (∀ x : Fin (a+1) → ℝ,
      x ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) ↔
      (∀ i, (a+1 : ℝ)^(-(K*ε)) ≤ x i ∧ x i ≤ (a+1 : ℝ)^(K*ε)) ∧
      ∀ l r : ℕ, l < r → r ≤ a+1 →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (a+1) => l ≤ i.val ∧ i.val < r), x i)-
          (r-l : ℕ)| ≤ (a+1 : ℝ)^(K*ε)*(r-l : ℕ)^(min s 1/2)) ∧
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
    let σ := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let P := fun u : AffineSimplex.massSimplex a L =>
      ∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹))
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Ky u.val))))
    let z' := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Kz u.val))))
    ∃ (hw0 : (∫⁻ u, w u ∂σ) ≠ 0) (hwt : (∫⁻ u, w u ∂σ) ≠ ⊤)
      (hz0 : (∫⁻ u, z' u ∂σ) ≠ 0) (hzt : (∫⁻ u, z' u ∂σ) ≠ ⊤),
    let ρy := AffineFibre.normalizedMeasure σ w hw0 hwt
    let ρz := AffineFibre.normalizedMeasure σ z' hz0 hzt
    ∀ (G : BlockObservable a.succPNat) (J : Finset (Fin (a+1))),
      DependsOnBlockCoordinates G J →
      (∀ i ∈ J, |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4) →
      Integrable (fun u => G.val (WithLp.ofLp u.val)) ρy ∧
      Integrable (fun u => G.val (WithLp.ofLp u.val)) ρz ∧
      |(∫ u, G.val (WithLp.ofLp u.val) ∂ρy)-(∫ u, G.val (WithLp.ofLp u.val) ∂ρz)| ≤
        C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε))+
            Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  obtain ⟨A,K,εc,κd,hA,hK,hεc,hκd,hcommon⟩ := common_physical_family_internal hzeta hRig s hs hs1
  obtain ⟨κb,hκb,hcoeff⟩ := hDiff K hK
  have hσ1 : min s 1/2 ≤ (1 : ℝ)/2 := div_le_div_of_nonneg_right (min_le_right s 1) (by norm_num)
  have hσs : min s 1/2 ≤ s/2 := div_le_div_of_nonneg_right (min_le_left s 1) (by norm_num)
  have hthreshold : 0 < min (1-min s 1/2) (s-min s 1/2)/4 := by
    apply div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hcutoff : 0 < (1-min s 1/2)/(2*K) := div_pos (by linarith) (by positivity)
  refine ⟨A,K,min εc (min (min (1-min s 1/2) (s-min s 1/2)/4)
    ((1-min s 1/2)/(2*K))),κd+κb,hA,hK,lt_min hεc (lt_min hthreshold hcutoff),
    add_pos hκd hκb,?_⟩
  intro ε hε hε₀
  have hεc' : ε < εc := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεrest := lt_of_lt_of_le hε₀ (min_le_right _ _)
  have hεdiff := lt_of_lt_of_le hεrest (min_le_left _ _)
  have hεcut := lt_of_lt_of_le hεrest (min_le_right _ _)
  obtain ⟨Cb,hCb,hcb⟩ := hcoeff ε hε hεdiff
  obtain ⟨δ,hδ,hdata⟩ := hcommon ε hε hεc'
  have hεfine : K*ε+min s 1/2 ≤ 1 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*K)).mp hεcut
    nlinarith
  refine ⟨δ,hδ,hεfine,?_⟩
  intro βlo βhi hβlo hβorder θ
  obtain ⟨Ct,ct,Cd,cd,hCt,hct,hCd,hcd,hfamily⟩ := hdata βlo βhi hβlo hβorder θ
  obtain ⟨Cf,cf,hCf,hcf,hcomparison⟩ := physical_smooth_family_comparison_internal
    s hs βlo Cb κb Ct ct Cd cd δ κd ε hβlo hCb hCt hct hCd hcd hδ hε
  have hβhi : 0 < βhi := lt_of_lt_of_le hβlo hβorder
  refine ⟨βhi*Cf,cf,mul_pos hβhi hCf,hcf,?_⟩
  intro p hps hβ hβhi' a d e ha hsize hde hpower L hL y z hy hz hyL hzL
  obtain ⟨Ky,Kz,hKy,hKz,Bcarrier,hLN,hfam⟩ := hfamily p hps hβ hβhi' a d e ha hsize hde hpower
    L hL y z hy hz hyL hzL
  have hfine : ∀ x : Fin (a+1) → ℝ,
      x ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) ↔
      (∀ i, (a+1 : ℝ)^(-(K*ε)) ≤ x i ∧ x i ≤ (a+1 : ℝ)^(K*ε)) ∧
      ∀ l r : ℕ, l < r → r ≤ a+1 →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (a+1) => l ≤ i.val ∧ i.val < r), x i)-
          (r-l : ℕ)| ≤ (a+1 : ℝ)^(K*ε)*(r-l : ℕ)^(min s 1/2) := by
    have h4 : 4*(a+1 : ℝ) ≤ (d+1+a+1 : ℝ) := by exact_mod_cast hsize
    have h2 : 2*(a.succPNat : ℝ) < ((d+1+a).succPNat : ℝ) := by
      simp only [Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add]
      nlinarith [Nat.cast_nonneg (α := ℝ) a]
    intro x
    simpa only [Nat.succPNat_coe,Nat.cast_succ] using
      fine_event_without_volume_cutoff s (K*ε) a.succPNat (d+1+a).succPNat hεfine h2 x
  refine ⟨hfine,Ky,Kz,hKy,hKz,?_⟩
  intro σ P w z'
  let frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a) :=
    ((stdOrthonormalBasis ℝ (AffineSimplex.Tangent a)).reindex
      (finCongr (AffineSimplex.finrank_tangent a))).repr
  obtain ⟨μ,hμ,hV,Q,hν,hQ,hform,htail,hdec⟩ := hfam frame
  let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
    ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
      (1-t)*Ky u+t*Kz u)
  let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
  let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
    (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
  have hKys := physical_realization_smooth_internal p a d y Ky hKy
  have hKzs := physical_realization_smooth_internal p a e z Kz hKz
  obtain ⟨h00,h0t,he0⟩ := physical_normalized_chart_internal p a d e θ ε L y z hyL hzL
    Ky Kz hKys hKzs 0 _ hLN frame (μ 0) (hV 0 (by norm_num))
  obtain ⟨h10,h1t,he1⟩ := physical_normalized_chart_internal p a d e θ ε L y z hyL hzL
    Ky Kz hKys hKzs 1 _ hLN frame (μ 1) (hV 1 (by norm_num))
  simp only [zero_mul,one_mul,sub_zero,sub_self,add_zero] at h00 h0t he0 h10 h1t he1
  refine ⟨h00,h0t,h10,h1t,?_⟩
  have hw : Measurable w := by
    have hc : Continuous (fun u : AffineSimplex.massSimplex a L => H 0 u.val) :=
      continuous_iff_continuousAt.mpr fun u =>
        (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz
          hKys hKzs 0 u.val u.property).continuousAt.comp continuous_subtype_val.continuousAt
    simpa only [H,w,P,Pi.neg_apply,zero_mul,one_mul,sub_zero,add_zero] using hc.neg.measurable.exp.ennreal_ofReal
  have hz' : Measurable z' := by
    have hc : Continuous (fun u : AffineSimplex.massSimplex a L => H 1 u.val) :=
      continuous_iff_continuousAt.mpr fun u =>
        (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz
          hKys hKzs 1 u.val u.property).continuousAt.comp continuous_subtype_val.continuousAt
    simpa only [H,z',P,Pi.neg_apply,zero_mul,one_mul,sub_self,zero_add,add_zero] using hc.neg.measurable.exp.ennreal_ofReal
  apply included_lipschitz_comparison_internal s (K*ε) (mul_pos hKpos hε) a ha
    (d+1+a).succPNat (by simp only [Nat.succPNat_coe]; omega) L hL Bcarrier hLN w z' hw hz'
    h00 h0t h10 h1t (βhi*Cf) cf (κd+κb) ε δ (mul_pos hβhi hCf).le
  intro G hsG J hJ hmiddle
  have hh := hcomparison p a d e ha θ L hL y z hyL hzL Ky Kz hKy hKz hps hβ hpower Bcarrier hLN frame
    (K*ε) (mul_pos hKpos hε) (by simp only [Nat.succPNat_coe]; omega)
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
      hcb a d e ha hsize hde hpower p hps θ A L hA y z hy hz hyL hzL Ky Kz hKy hKz)
    μ hμ hV Q hν hQ hform htail hdec G hsG J hJ hmiddle
  dsimp only at hh
  rw [he0,he1] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hβhi' hCf.le) (by positivity)
  · have hnonneg : 0 ≤ restrictedBlockDerivativeNorm G J
        (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)) := by
      unfold restrictedBlockDerivativeNorm
      exact Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    have hb : 0 ≤ blockDerivativeNorm G := by
      unfold blockDerivativeNorm
      positivity
    exact add_nonneg hnonneg (mul_nonneg (Real.exp_pos _).le hb)
end Riesz2.CompatibleComparison
