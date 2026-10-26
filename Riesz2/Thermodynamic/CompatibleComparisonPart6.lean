/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart5

/-!
# Physical point sources and the integrated compatible comparison

Assembly of the literal physical Hessian, source classes, and covariance representation
for the proof of Proposition 6.6.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See Theorem 4 and the proof of Proposition 6.6 of the paper: the Euclidean
gradient coordinate is the classical partial of the literal observable. -/
theorem block_gradient_partial_internal {n : ℕ+} (G : BlockObservable n)
    (hs : ContDiff ℝ ∞ G.val) (x : EuclideanSpace ℝ (Fin (n : ℕ)))
    (i : Fin (n : ℕ)) :
    gradient (fun y => G.val (WithLp.ofLp y)) x i =
      fderiv ℝ G.val (WithLp.ofLp x) (Pi.single i 1) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n : ℕ) => ℝ)
  have hd := (hs.differentiable (by simp) _).hasFDerivAt.comp x e.hasFDerivAt
  have he := congrArg (fun T : EuclideanSpace ℝ (Fin (n : ℕ)) →L[ℝ] ℝ =>
    T (EuclideanSpace.single i 1)) hd.fderiv
  rw [← inner_gradient_left] at he
  have hb : e.toContinuousLinearMap (EuclideanSpace.single i 1) = Pi.single i 1 := rfl
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    ContinuousLinearMap.comp_apply] at he
  rw [hb] at he
  exact he

/-- See the proof of Proposition 6.6 in the paper: consecutive transport forms
the actual bounded coordinate sources on the physical law. Bounds hold
on the same event, including its boundary, and recover the exact chart
classes. No real essential norm is used before boundedness is proved. -/
theorem transported_block_sources_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ξ : Measure (frame '' (AffineSimplex.centredChart a L ⁻¹'
      AffineSimplex.massSimplex a L)))
    (G : BlockObservable a.succPNat) (hs : ContDiff ℝ ∞ G.val)
    (χ₀ : Fin (a+1) → Lp ℝ 2 (ξ.map Subtype.val))
    (hχ₀ : ∀ i, χ₀ i =ᵐ[ξ.map Subtype.val] fun x =>
      gradient (fun y => G.val (WithLp.ofLp y))
        (AffineSimplex.centredChart a L (frame.symm x)) i)
    (E : Set (Fin (a+1) → ℝ)) (hE : Convex ℝ E) (hne : (interior E).Nonempty)
    (hEm : MeasurableSet E) :
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let hv := MeasurableEmbedding.subtype_coe
      (frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)).measurableSet
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
    let Tf := ScalarFormEmbedding.pullback ξ (Subtype.val : U → _) hv
    let Tj := ScalarFormEmbedding.pullback ξ j hj
    ∃ χ : Fin (a+1) → BoundedL2Pairings.boundedSubmodule (ξ.map j),
      (∀ i, Tf.symm (Tj (χ i).val) = χ₀ i) ∧
      (∀ i, (χ i).val =ᵐ[ξ.map j] fun x => fderiv ℝ G.val
        (WithLp.ofLp x.val) (Pi.single i 1)) ∧
      (∀ i, ∀ᵐ x ∂ξ.map j, |(χ i).val x| ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      (∀ i, ∀ᵐ x ∂(ξ.map j).restrict {x | WithLp.ofLp x.val ∈ E},
        |(χ i).val x| ≤ restrictedBlockDerivativeNorm G {i} E) ∧
      (∀ i p, eLpNorm ((χ i).val : _ → ℝ) p (ξ.map j) =
        eLpNorm (χ₀ i) p (ξ.map Subtype.val)) := by
  intro U hv j hj Tf Tj
  have hrepr (i) : (Tj.symm (Tf (χ₀ i)) : _ → ℝ) =ᵐ[ξ.map j]
      fun x => fderiv ℝ G.val (WithLp.ofLp x.val) (Pi.single i 1) := by
    apply (consecutive_literal_class_internal ξ Subtype.val hv j hj (χ₀ i) _ ?_).1
    filter_upwards [hv.ae_map_iff.mp (hχ₀ i)] with x hx
    exact hx.trans (block_gradient_partial_internal G hs _ i)
  have hglobal (i) : ∀ᵐ x ∂ξ.map j,
      |Tj.symm (Tf (χ₀ i)) x| ≤ (coordinateDerivativeNorm G i : ℝ) := by
    filter_upwards [hrepr i] with x hx
    rw [hx]
    exact coordinate_partial_bound G i (hs.differentiable (by simp) _)
  let χ : Fin (a+1) → BoundedL2Pairings.boundedSubmodule (ξ.map j) :=
    fun i => ⟨Tj.symm (Tf (χ₀ i)), _, hglobal i⟩
  refine ⟨χ,fun i => by simp only [χ,LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply],hrepr,hglobal,?_,?_⟩
  · intro i
    filter_upwards [ae_restrict_of_ae (hrepr i),
      ae_restrict_mem (hEm.preimage (((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).measurable))] with x hx hxe
    rw [hx]
    simpa only [Finset.sum_singleton] using
      smooth_derivative_sum_le_restricted G (hs.of_le (by simp)) {i} E hE hne hxe
  · intro i p
    exact (ScalarFormEmbedding.inverse_eLpNorm ξ j hj _ p).trans
      (ScalarFormEmbedding.pullback_eLpNorm ξ Subtype.val hv _ p)


/-- See the proof of Proposition 6.6 in the paper: covariance depends only on
its two almost-everywhere classes, also for the literal physical values. -/
theorem covariance_ae_internal {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g f' g' : X → ℝ} (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    covariance f g μ = covariance f' g' μ := by
  unfold covariance
  rw [integral_congr_ae hf,integral_congr_ae hg]
  apply integral_congr_ae
  filter_upwards [hf,hg] with x hx hy
  rw [hx,hy]

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the original
intrinsic certificate already gives closedness of its entire scalar form. -/
theorem intrinsic_certificate_closed_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (AffineSimplex.chartDomain (a+1) N)) (Q : ScalarFormData ν)
    (hQ : InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q) :
    IsClosedScalarDirichletForm Q := by
  obtain ⟨μ,V,hV,Q₀,_,hclosed,_,hlaw,hform⟩ := hQ
  cases hlaw
  have he := eq_of_heq hform
  rw [he]
  exact ScalarFormEmbedding.closed_dirichlet _ _ _ _
    (ScalarFormEmbedding.restriction_closed_dirichlet _ _ _ Q₀ hclosed)

/-- See Lemma 6.5 and the proof of Proposition 6.6 of the paper: the singleton
restricted coordinate bounds add to exactly the restricted sum. -/
theorem singleton_restricted_sum_internal {n : ℕ+} (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) (E : Set (Fin (n : ℕ) → ℝ)) :
    (∑ i ∈ J, restrictedBlockDerivativeNorm G {i} E) =
      restrictedBlockDerivativeNorm G J E := by
  simp only [restrictedBlockDerivativeNorm,Finset.sum_singleton]

/-- See the proof of Proposition 6.6 in the paper: actual bounded partial
classes on any finite physical law, with both coordinate bounds.
This also constructs a source family at every time without choosing values
of weak derivatives on exceptional fibres. -/
theorem literal_block_sources_internal (a : ℕ) (N : ℝ)
    (ν : Measure (AffineSimplex.chartDomain (a+1) N)) [IsFiniteMeasure ν]
    (G : BlockObservable a.succPNat) (hs : ContDiff ℝ ∞ G.val)
    (E : Set (Fin (a+1) → ℝ)) (hE : Convex ℝ E)
    (hne : (interior E).Nonempty) (hEm : MeasurableSet E) :
    ∃ χ : Fin (a+1) → BoundedL2Pairings.boundedSubmodule ν,
      (∀ i, (χ i).val =ᵐ[ν] fun x =>
        fderiv ℝ G.val (WithLp.ofLp x.val) (Pi.single i 1)) ∧
      (∀ i, ∀ᵐ x ∂ν, |(χ i).val x| ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      (∀ i, ∀ᵐ x ∂ν.restrict {x | WithLp.ofLp x.val ∈ E},
        |(χ i).val x| ≤ restrictedBlockDerivativeNorm G {i} E) := by
  let f := fun i (x : AffineSimplex.chartDomain (a+1) N) =>
    fderiv ℝ G.val (WithLp.ofLp x.val) (Pi.single i 1)
  have hf (i) : Continuous (f i) :=
    ((hs.continuous_fderiv (by simp)).clm_apply
      continuous_const).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  have hb (i) (x : AffineSimplex.chartDomain (a+1) N) :
      |f i x| ≤ (coordinateDerivativeNorm G i : ℝ) :=
    coordinate_partial_bound G i (hs.differentiable (by simp) _)
  have hm (i) : MemLp (f i) 2 ν :=
    MemLp.of_bound (hf i).aestronglyMeasurable _
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  let χ : Fin (a+1) → BoundedL2Pairings.boundedSubmodule ν := fun i =>
    ⟨(hm i).toLp (f i),_,(hm i).coeFn_toLp.mono (fun x hx => hx ▸ hb i x)⟩
  refine ⟨χ,fun i => (hm i).coeFn_toLp,fun i => (hm i).coeFn_toLp.mono (fun x hx => hx ▸ hb i x),?_⟩
  intro i
  filter_upwards [ae_restrict_of_ae (hm i).coeFn_toLp,
    ae_restrict_mem (hEm.preimage ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).measurable)]
    with x hx hxe
  rw [show (χ i).val x = f i x from hx]
  simpa only [Finset.sum_singleton] using
    smooth_derivative_sum_le_restricted G (hs.of_le (by simp)) {i} E hE hne hxe

/-- See Lemma 6.5 and the proof of Proposition 6.6 of the paper: on the literal
fine event the source classes have the actual coordinate bounds,
with no extra boundary or interior premise. -/
theorem fine_literal_block_sources_internal (s η : ℝ) (hη : 0 < η)
    (a : ℕ) (ha : 1 ≤ a) (N : ℕ+) (hN : a+1 < (N : ℕ))
    (ν : Measure (AffineSimplex.chartDomain (a+1) (N : ℝ))) [IsFiniteMeasure ν]
    (G : BlockObservable a.succPNat) (hs : ContDiff ℝ ∞ G.val) :
    ∃ χ : Fin (a+1) → BoundedL2Pairings.boundedSubmodule ν,
      (∀ i, (χ i).val =ᵐ[ν] fun x =>
        fderiv ℝ G.val (WithLp.ofLp x.val) (Pi.single i 1)) ∧
      (∀ i, ∀ᵐ x ∂ν, |(χ i).val x| ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      (∀ i, ∀ᵐ x ∂ν.restrict {x | WithLp.ofLp x.val ∈ goodBlockEvent s a.succPNat N η},
        |(χ i).val x| ≤ restrictedBlockDerivativeNorm G {i} (goodBlockEvent s a.succPNat N η)) := by
  exact literal_block_sources_internal a N ν G hs _
    (InterpolantLocalLaws.convex_goodBlockEvent s a.succPNat N η)
    ⟨_,one_mem_interior_fine_event s η hη a.succPNat N (by change 2 ≤ a+1; omega) hN⟩
    (InterpolantLocalLaws.measurableSet_goodBlockEvent s a.succPNat N η)

/-- See the proof of Proposition 6.6 in the paper: the coordinate constants of
the source estimate are nonnegative and sum to the exact good norm
and at most the full global norm. -/
theorem frozen_source_constants_internal {n : ℕ+} (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) (E : Set (Fin (n : ℕ) → ℝ)) :
    (∀ i, 0 ≤ restrictedBlockDerivativeNorm G {i} E) ∧
      (∀ i, 0 ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      (∑ i ∈ J, restrictedBlockDerivativeNorm G {i} E) = restrictedBlockDerivativeNorm G J E ∧
      (∑ i ∈ J, (coordinateDerivativeNorm G i : ℝ)) ≤ blockDerivativeNorm G := by
  refine ⟨fun i => ?_,fun i => (coordinateDerivativeNorm G i).property,
    singleton_restricted_sum_internal G J E,?_⟩
  · unfold restrictedBlockDerivativeNorm
    exact Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  · exact Finset.sum_le_univ_sum_of_nonneg (fun _ => NNReal.coe_nonneg _)

section Physical

variable (p : Parameters) (a d e : ℕ) (ha : 1 ≤ a)
    (θ : PhysicalCutoff) (ε L : ℝ) (hL : 0 < L)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L)
    (hzL : ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩)
    (hKz : ∀ u (hu : RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
        gapAmbientDomain (e+1+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a
          (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩)


variable
    (hKys : ContDiffOn ℝ ∞ Ky (RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
        gapAmbientDomain (d+1+a).succPNat))
    (hKzs : ContDiffOn ℝ ∞ Kz (RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
        gapAmbientDomain (e+1+a).succPNat))

include ha hyL hzL hKy hKz hKys hKzs in
/-- See the proof of Proposition 6.6 in the paper: the actual β-scaled ambient
Hessian is positive semidefinite and coercive in every ambient direction
on the physical mass fibre. In particular it is coercive on the tangent
space used by the original certificate. -/
theorem physical_hessian_coercive_internal (hε : 0 ≤ ε)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let c := (p.val.1*min 1 (p.val.2*(p.val.2+1)))*(a+1 : ℝ)^(-(p.val.2+2)*ε)
    0 < c ∧ ∀ x ∈ AffineSimplex.massSimplex a L,
      (hessianMatrix H x).PosSemidef ∧ ∀ v : Fin (a+1) → ℝ,
        c*(∑ i, v i^2) ≤ ∑ i, ∑ j, v i*hessianMatrix H x i j*v j := by
  intro H c
  have hc : 0 < c := by
    have hs := p.property.2.1
    have hβ := p.property.1
    dsimp only [c]
    positivity
  refine ⟨hc,?_⟩
  intro x hx
  let H₀ := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
    (∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
      (1-t)*Ky u+t*Kz u
  have hs := physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL
    Ky Kz hKys hKzs t x hx
  change ContDiffAt ℝ ∞ H x at hs
  have hs₀ : ContDiffAt ℝ ∞ H₀ x := by
    have hβ : p.val.1 ≠ 0 := p.property.1.ne'
    have he : H₀ = fun u => p.val.1⁻¹*H u := by
      funext u
      simp only [H,H₀,← mul_assoc,inv_mul_cancel₀ hβ,one_mul]
    rw [he]
    exact contDiffAt_const.mul hs
  have hscale : hessianMatrix H x = p.val.1 • hessianMatrix H₀ x := by
    ext i j
    rw [Intrinsic.hessianMatrix_eq_second hs,
      PhysicalCollision.internal_hessian_const_mul (hs₀.of_le (by simp)),
      ← Intrinsic.hessianMatrix_eq_second hs₀]
    rfl
  have hl (v : Fin (a+1) → ℝ) :
      c*(∑ i, v i^2) ≤ ∑ i, ∑ j, v i*hessianMatrix H x i j*v j := by
    have hh := mul_le_mul_of_nonneg_left
      (InterpolationCoefficientBounds.coercivity_internal p θ ε hε (d+1) (e+1) a ha
        y z L hyL hzL Ky Kz hKy hKz t ht x hx (WithLp.toLp 2 v)) p.property.1.le
    rw [hscale]
    simpa only [c,H₀,Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,
      mul_assoc,mul_comm,mul_left_comm] using hh
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩,hl⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,Intrinsic.hessianMatrix_eq_second hs]
    exact hs.isSymmSndFDerivAt (by simp) _ _
  · intro v
    have hh := (mul_nonneg hc.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans (hl v)
    simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc] using hh

include ha hyL hzL hKy hKz hKys hKzs in
/-- See Proposition 3.6 and the proof of Proposition 6.6 of the paper:
the actual physical point-source solution has the all-size coordinate
supremum bound required for the exceptional-set pairing. The source
essential norm is finite because its class belongs to the bounded submodule. -/
theorem physical_point_source_maximum_internal (hε : 0 ≤ ε)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L)) :
    let ν := ρ.map (InterpolationTransport.inclusion a L N hLN)
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let c := (p.val.1*min 1 (p.val.2*(p.val.2+1)))*(a+1 : ℝ)^(-(p.val.2+2)*ε)
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
      (i : Fin (a+1)) (χ : BoundedL2Pairings.boundedSubmodule ν)
      (ψ : Fin (a+1) → Q.1),
      WeightedWeakSolution Q (fun x => hessianMatrix H x.val)
        (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
      ∀ j, ∀ᵐ x ∂ν, |(ψ j).val x| ≤
        c⁻¹*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal := by
  intro ν H c Q hQ i χ ψ hψ
  obtain ⟨hc,hcoerc⟩ := physical_hessian_coercive_internal p a d e ha θ ε L y z hyL hzL
    Ky Kz hKy hKz hKys hKzs hε t ht
  have hsupport : ∀ᵐ x ∂ν, x.val ∈ AffineSimplex.massSimplex a L := by
    rw [(InterpolationTransport.measurableEmbedding_inclusion a L N hLN).ae_map_iff]
    exact ae_of_all _ fun x => x.property
  have hmat : ∀ᵐ x ∂ν, (∀ i j, hessianMatrix H x.val i j = hessianMatrix H x.val j i) ∧
      ∀ v : Fin (a+1) → ℝ, c*(∑ i,v i^2) ≤ ∑ i,∑ j,v i*hessianMatrix H x.val i j*v j := by
    filter_upwards [hsupport] with x hx
    refine ⟨?_,(hcoerc x.val hx).2⟩
    intro i j
    have hh := congrFun (congrFun (hcoerc x.val hx).1.1 j) i
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh
  exact (FixedLengthDecay.point_source_ae_bound_internal Q hQ _
    (fun i j => (DifferentiatedPoisson.measurable_hessian_entries i j).comp measurable_subtype_coe)
    c hc hmat _ i χ.val _ ENNReal.toReal_nonneg
    (FixedLengthDecay.bounded_ae_essentialNorm_internal χ) ψ hψ).2

include ha hL hyL hzL hKy hKz hKys hKzs in
/-- See the proof of Proposition 6.6 in the paper: complete physical point-source
specialization on the original intrinsic certificate. All analytic chart,
Hessian, value, and derivative identifications are supplied here. The analytic hypotheses are the coefficient-envelope bounds for the
interaction. -/
theorem physical_point_source_covariance_internal (hε : 0 < ε)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (G : BlockObservable a.succPNat) (hs : ContDiff ℝ ∞ G.val)
    (J : Finset (Fin (a+1))) (hJ : DependsOnBlockCoordinates G J)
    (E : Set (Fin (a+1) → ℝ)) (hE : Convex ℝ E)
    (hne : (interior E).Nonempty) (hEm : MeasurableSet E) :
    let H : EuclideanSpace ℝ (Fin (a+1)) → ℝ := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U : Set (EuclideanSpace ℝ (Fin a)) := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin (a+1)) := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let D : EuclideanSpace ℝ (Fin (a+1)) → ℝ := fun u => Ky u-Kz u
    let b : Fin (a+1) → EuclideanSpace ℝ (Fin (a+1)) → ℝ := fun i u => InteractionDifferential.pinnedRepresentative (fun k : Fin a =>
      fderiv ℝ D u (WithLp.toLp 2 (Pi.single k.castSucc 1-Pi.single k.succ 1))) i
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (_hV : IsEuclideanGibbsPotential volume μ U (H ∘ g)),
    let ξ : Measure U := μ.comap Subtype.val
    let ν : Measure (AffineSimplex.chartDomain (a+1) N) := ξ.map j
    ∀ (Q : ScalarFormData ν)
      (_hQ : InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q)
      (good : Set (EuclideanSpace ℝ (Fin a))) (W : EuclideanSpace ℝ (Fin a) → ℝ)
      (B K : ℝ),
      (∀ i, ∀ᵐ x ∂μ.restrict good, |b i (g x)| ≤ B) →
      IntegrableOn W goodᶜ μ →
      (∀ i : Fin (a+1), ∀ᵐ x : EuclideanSpace ℝ (Fin a) ∂μ.restrict goodᶜ, (b i (g x))*(b i (g x)) ≤ K*W x) →
    ∃ χ : Fin (a+1) → BoundedL2Pairings.boundedSubmodule ν,
      (∀ i, (χ i).val =ᵐ[ν] fun x =>
        fderiv ℝ G.val (WithLp.ofLp x.val) (Pi.single i 1)) ∧
      (∀ i, ∀ᵐ x ∂ν, |(χ i).val x| ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      (∀ i, ∀ᵐ x ∂ν.restrict {x | WithLp.ofLp x.val ∈ E},
        |(χ i).val x| ≤ restrictedBlockDerivativeNorm G {i} E) ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 ν,
        (∀ i, b₂ i =ᵐ[ν] fun x => b i x.val) ∧
        (∀ i, ∃! ψ : Fin (a+1) → Q.1,
          WeightedWeakSolution Q (fun x => hessianMatrix H x.val)
            (zeroSumComponents (Fin (a+1)))
              (fun l => if l = i then (χ i).val else 0) ψ) ∧
        (∀ ψ : Fin (a+1) → Fin (a+1) → Q.1,
          (∀ i ∈ J, WeightedWeakSolution Q (fun x => hessianMatrix H x.val)
            (zeroSumComponents (Fin (a+1)))
              (fun l => if l = i then (χ i).val else 0) (ψ i)) →
          covariance (fun x => G.val (WithLp.ofLp x.val)) (fun x => D x.val) ν =
            ∑ i ∈ J, ∫ x, ∑ l, b l x.val*(ψ i l).val x ∂ν) := by
  intro H U g j D b μ hV ξ ν Q hQ good W B K hgood hW hsq
  let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  let hB := frame.isometry.lipschitzWith.isBounded_image
    (ConditionalWellPosedness.fibre_isBounded a L)
  let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
  let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
  let Tf := ScalarFormEmbedding.pullback ξ Subtype.val hv
  let Tj := ScalarFormEmbedding.pullback ξ j hj
  have hξ : ξ.map Subtype.val = μ :=
    (InterpolationTransport.orthonormal_law a L N hLN frame μ (H ∘ g) hV).1
  obtain ⟨hV',hcov⟩ := certificate_point_source_covariance_internal a L N hLN frame ν Q hQ
    μ (H ∘ g) hV rfl
  obtain ⟨_,_,hwell⟩ := physical_chart_wellposed_of_gibbs_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz
  have hw := (hwell t ht frame (ξ.map Subtype.val) hV').1
  obtain ⟨A,hA,hArange,hact⟩ := frame_matrix_internal a frame
  obtain ⟨F,hF,χ₀,hχ₀,hDF⟩ := smooth_block_source_internal a L frame A hact
    (ξ.map Subtype.val) (H ∘ g) hV' G
    (hs.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (a+1) => ℝ)).contDiff) J hJ
  obtain ⟨χ,hrecover,hχ,hglobal,hlocal,_⟩ := transported_block_sources_internal a L N hLN
    frame ξ G hs χ₀ hχ₀ E hE hne hEm
  have hgood' : ∀ i, ∀ᵐ x ∂(ξ.map Subtype.val).restrict good, |b i (g x)| ≤ B := by
    rw [hξ]; exact hgood
  have hW' : IntegrableOn W goodᶜ (ξ.map Subtype.val) := by rw [hξ]; exact hW
  have hsq' : ∀ i, ∀ᵐ x ∂(ξ.map Subtype.val).restrict goodᶜ,
      b i (g x)^2 ≤ K*W x := by
    rw [hξ]
    simpa only [pow_two] using hsq
  obtain ⟨K₀,hK₀,b₀,hb₀,hDK⟩ := physical_interaction_jet_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz hKys hKzs hε G t ht frame A hact
    (ξ.map Subtype.val) hV' good W B K hgood' hW' hsq'
  let b₂ := fun i => Tj.symm (Tf (b₀ i))
  have hb₂ (i) : b₂ i =ᵐ[ν] fun x => b i x.val := by
    apply (consecutive_literal_class_internal ξ Subtype.val hv j hj (b₀ i) _ ?_).1
    exact hv.ae_map_iff.mp (hb₀ i)
  let f := Tj.symm (Tf (ScalarForm.value _ F))
  let k := Tj.symm (Tf (ScalarForm.value _ K₀))
  have hf : f =ᵐ[ν] fun x => G.val (WithLp.ofLp x.val) := by
    apply (consecutive_literal_class_internal ξ Subtype.val hv j hj (ScalarForm.value _ F) _ ?_).1
    exact hv.ae_map_iff.mp hF
  have hk : k =ᵐ[ν] fun x => D x.val := by
    apply (consecutive_literal_class_internal ξ Subtype.val hv j hj (ScalarForm.value _ K₀) _ ?_).1
    exact hv.ae_map_iff.mp hK₀
  have hsupport : ∀ᵐ x ∂ν, x.val ∈ AffineSimplex.massSimplex a L := by
    rw [hj.ae_map_iff]
    exact ae_of_all _ fun x => by
      obtain ⟨w,hw,he⟩ := x.property
      change g x.val ∈ _
      rw [← he]
      simpa only [g,frame.symm_apply_apply,mem_preimage] using hw
  obtain ⟨hc,hcoerc⟩ := physical_hessian_coercive_internal p a d e ha θ ε L y z hyL hzL
    Ky Kz hKy hKz hKys hKzs hε.le t ht
  have hpos := hsupport.mono fun x hx => (hcoerc x.val hx).1
  have hlower := hsupport.mono fun x hx v (_ : v ∈ zeroSumComponents (Fin (a+1))) =>
    (hcoerc x.val hx).2 v
  have hM : (fun x => A.transpose*hessianMatrix H (g x)*A) =ᵐ[ξ.map Subtype.val]
      hessianMatrix (H ∘ g) := by
    filter_upwards [IntrinsicScalarCore.supported hU hV'] with x hx
    exact physical_chart_hessian_internal p a d e θ ε L y z hyL hzL Ky Kz
      hKys hKzs t frame A hact x hx
  refine ⟨χ,hχ,hglobal,hlocal,b₂,hb₂,?_,?_⟩
  · intro i
    exact MatrixEnergy.weightedWeakSolution_existsUnique Q
      (intrinsic_certificate_closed_internal a L N hLN frame ν Q hQ) _ _ hpos _ hc hlower
      (fun i l => (DifferentiatedPoisson.measurable_hessian_entries i l).comp measurable_subtype_coe) _
  intro ψ hψ
  have hvF : RectangularFormTransport.tupleMap A.transpose
      (fun i => Tf.symm (Tj (if i ∈ J then (χ i).val else 0))) =
        fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ F) := by
    rw [← hDF]
    congr 1
    funext i
    by_cases hi : i ∈ J
    · simp only [ite_eq_left hi]
      exact hrecover i
    · simp only [ite_eq_right hi,map_zero]
  have hbK : RectangularFormTransport.tupleMap A.transpose
      (fun i => Tf.symm (Tj (b₂ i))) =
        fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ K₀) := by
    simpa only [b₂,LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.symm_apply_apply] using hDK
  have hc' := hcov hw A hA hArange (fun x => hessianMatrix H x.val)
    (fun x => hessianMatrix H (g x)) (ae_of_all _ fun _ => rfl) hM hpos
    (fun i l => (DifferentiatedPoisson.measurable_hessian_entries i l).comp measurable_subtype_coe)
    _ hc hlower F K₀ f k
    (by
      change Tf.symm (Tj f) = _
      simp only [f,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.symm_apply_apply]
      rfl)
    (by
      change Tf.symm (Tj k) = _
      simp only [k,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.symm_apply_apply]
      rfl)
    J (fun i => (χ i).val) b₂ hvF hbK ψ hψ
  rw [covariance_ae_internal hf hk] at hc'
  refine hc'.trans (Finset.sum_congr rfl fun i _ => ?_)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hb₂] with x hx
  simp only [hx]

include ha hL hyL hzL hKy hKz in
/-- See Lemma 6.1 and the proof of Proposition 6.6 of the paper:
the time identity on the actual included chart laws. Expectations and
covariances are transported from the same intrinsic time law, and both
physical observables have second moments before the covariance is used. -/
theorem physical_included_integrated_identity_internal (hε : 0 < ε)
    (G : BlockObservable a.succPNat) (N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    ∀ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) →
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
    let F := fun x : AffineSimplex.chartDomain (a+1) N => G.val (WithLp.ofLp x.val)
    let D := fun x : AffineSimplex.chartDomain (a+1) N => Ky x.val-Kz x.val
    (∀ t ∈ Icc (0 : ℝ) 1, MemLp F 2 (ν t) ∧ MemLp D 2 (ν t)) ∧
      IntervalIntegrable (fun t => covariance F D (ν t)) volume 0 1 ∧
      (∫ x, F x ∂ν 1)-(∫ x, F x ∂ν 0) =
        p.val.1*∫ t in (0 : ℝ)..1, covariance F D (ν t) := by
  intro H U g j μ hV ν F D
  let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
  let ρ := fun t => (volume.comap (Subtype.val : Ω → AffineSimplex.Tangent a)).tilted
    (fun w : Ω => -H t (AffineSimplex.centredChart a L w.val))
  let f := fun w : Ω => G.val (WithLp.ofLp (AffineSimplex.centredChart a L w.val))
  let d₀ := fun w : Ω => Ky (AffineSimplex.centredChart a L w.val)-
    Kz (AffineSimplex.centredChart a L w.val)
  let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
  let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
  have hframe : MeasurableEmbedding (fun w : Ω => frame w.val) :=
    frame.toHomeomorph.measurableEmbedding.comp
      (MeasurableEmbedding.subtype_coe (ConditionalWellPosedness.fibre_isOpen a L).measurableSet)
  obtain ⟨_,_,_,_,hint,hid⟩ := physical_integrated_block_identity_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz hε G
  have hdata (t) (ht : t ∈ Icc (0 : ℝ) 1) :
      MemLp F 2 (ν t) ∧ MemLp D 2 (ν t) ∧
      (∫ x, F x ∂ν t) = ∫ w, f w ∂ρ t ∧
      covariance F D (ν t) = covariance f d₀ (ρ t) := by
    obtain ⟨hlaw,hf,hD⟩ := physical_chart_value_moments_internal p a d e ha θ ε L hL
      y z hyL hzL Ky Kz hKy hKz hε G t ht frame (μ t) (hV t ht)
    let ξ : Measure U := (μ t).comap Subtype.val
    have hξ : ξ.map Subtype.val = μ t :=
      (InterpolationTransport.orthonormal_law a L N hLN frame (μ t) (H t ∘ g) (hV t ht)).1
    have hfξ : MemLp (F ∘ j) 2 ξ := by
      change MemLp ((fun x => G.val (WithLp.ofLp (g x))) ∘ Subtype.val) 2 ξ
      exact hv.memLp_map_measure_iff.mp (hξ.symm ▸ hf)
    have hDξ : MemLp (D ∘ j) 2 ξ := by
      change MemLp ((fun x => Ky (g x)-Kz (g x)) ∘ Subtype.val) 2 ξ
      exact hv.memLp_map_measure_iff.mp (hξ.symm ▸ hD)
    have hfν : MemLp F 2 (ν t) := hj.memLp_map_measure_iff.mpr hfξ
    have hDν : MemLp D 2 (ν t) := hj.memLp_map_measure_iff.mpr hDξ
    have he : (∫ x, F x ∂ν t) = ∫ x, G.val (WithLp.ofLp (g x)) ∂μ t := by
      rw [hj.integral_map]
      change (∫ x, (fun x => G.val (WithLp.ofLp (g x))) (Subtype.val x) ∂ξ) = _
      have hh := hv.integral_map (μ := ξ) (g := fun x => G.val (WithLp.ofLp (g x)))
      exact (hξ ▸ hh).symm
    have he' : (∫ x, G.val (WithLp.ofLp (g x)) ∂μ t) = ∫ w, f w ∂ρ t := by
      rw [← hlaw,hframe.integral_map]
      simp only [g,f,frame.symm_apply_apply]
      rfl
    have hc : covariance F D (ν t) =
        covariance (fun x => G.val (WithLp.ofLp (g x))) (fun x => Ky (g x)-Kz (g x)) (μ t) := by
      rw [covariance_map hfν.aestronglyMeasurable hDν.aestronglyMeasurable hj.measurable.aemeasurable]
      have hh := covariance_map (hξ.symm ▸ hf.aestronglyMeasurable)
        (hξ.symm ▸ hD.aestronglyMeasurable) hv.measurable.aemeasurable
      exact (hξ ▸ hh).symm
    have hc' : covariance (fun x => G.val (WithLp.ofLp (g x)))
        (fun x => Ky (g x)-Kz (g x)) (μ t) = covariance f d₀ (ρ t) := by
      rw [← hlaw] at hf hD ⊢
      rw [covariance_map hf.aestronglyMeasurable hD.aestronglyMeasurable hframe.measurable.aemeasurable]
      simp only [Function.comp_def,f,d₀,frame.symm_apply_apply]
      rfl
    exact ⟨hfν,hDν,he.trans he',hc.trans hc'⟩
  have hcov : EqOn (fun t => covariance F D (ν t))
      (fun t => covariance f d₀ (ρ t)) (Icc (0 : ℝ) 1) :=
    fun t ht => (hdata t ht).2.2.2
  refine ⟨fun t ht => ⟨(hdata t ht).1,(hdata t ht).2.1⟩,?_,?_⟩
  · apply hint.congr
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact (hcov ⟨ht.1.le,ht.2⟩).symm
  · rw [(hdata 1 (by simp)).2.2.1,(hdata 0 (by simp)).2.2.1]
    exact hid.trans (congrArg (fun z => p.val.1*z)
      (intervalIntegral.integral_congr (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcov)).symm)

include ha hL hyL hzL hKy hKz hKys hKzs in
/-- See the proof of Proposition 6.6 in the paper: construct the actual bounded
coordinate source family, replace the integrated covariance by its physical
point-source pairings, and identify the included laws with the normalized
Hausdorff laws, including both endpoints. This supplies the literal `hid`
needed by `integrated_comparison_from_decay_internal`. The coefficient-envelope hypotheses are the interaction estimates. -/
theorem physical_integrated_point_sources_internal (hε : 0 < ε)
    (G : BlockObservable a.succPNat) (hs : ContDiff ℝ ∞ G.val)
    (J : Finset (Fin (a+1))) (hJ : DependsOnBlockCoordinates G J)
    (E : Set (Fin (a+1) → ℝ)) (hE : Convex ℝ E)
    (hne : (interior E).Nonempty) (hEm : MeasurableSet E)
    (N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let b := fun i u => InteractionDifferential.pinnedRepresentative (fun k : Fin a =>
      fderiv ℝ (fun u => Ky u-Kz u) u
        (WithLp.toLp 2 (Pi.single k.castSucc 1-Pi.single k.succ 1))) i
    let σ := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun t (u : AffineSimplex.massSimplex a L) => ENNReal.ofReal (Real.exp (-H t u.val))
    ∀ (μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)))
      (_hfinite : ∀ t, IsFiniteMeasure (μ t))
      (_hV : ∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)),
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
    ∀ (Q : (t : ℝ) → ScalarFormData (ν t))
      (_hQ : ∀ t ∈ Icc (0 : ℝ) 1,
        InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame (ν t) (Q t))
      (good : ℝ → Set (EuclideanSpace ℝ (Fin a)))
      (W : ℝ → EuclideanSpace ℝ (Fin a) → ℝ) (B K : ℝ → ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i, ∀ᵐ x ∂(μ t).restrict (good t), |b i (g x)| ≤ B t) →
      (∀ t ∈ Icc (0 : ℝ) 1, IntegrableOn (W t) (good t)ᶜ (μ t)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i, ∀ᵐ x ∂(μ t).restrict (good t)ᶜ,
        b i (g x)*b i (g x) ≤ K t*W t x) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∃ (h0 : (∫⁻ u, w t u ∂σ) ≠ 0)
      (htop : (∫⁻ u, w t u ∂σ) ≠ ⊤),
        ν t = (AffineFibre.normalizedMeasure σ (w t) h0 htop).map
          (InterpolationTransport.inclusion a L N hLN)) ∧
    ∃ χ : (t : ℝ) → Fin (a+1) → BoundedL2Pairings.boundedSubmodule (ν t),
      (∀ t i, (χ t i).val =ᵐ[ν t] fun x =>
        fderiv ℝ G.val (WithLp.ofLp x.val) (Pi.single i 1)) ∧
      (∀ t i, ∀ᵐ x ∂ν t, |(χ t i).val x| ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      (∀ t i, ∀ᵐ x ∂(ν t).restrict {x | WithLp.ofLp x.val ∈ E},
        |(χ t i).val x| ≤ restrictedBlockDerivativeNorm G {i} E) ∧
      ∀ ψ : (t : ℝ) → Fin (a+1) → Fin (a+1) → (Q t).1,
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ J,
          WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
            (zeroSumComponents (Fin (a+1)))
              (fun l => if l = i then (χ t i).val else 0) (ψ t i)) →
        IntervalIntegrable (fun t => ∑ i ∈ J, ∫ x, ∑ l,
          b l x.val*(ψ t i l).val x ∂ν t) volume 0 1 ∧
        ((∫ x, G.val (WithLp.ofLp x.val) ∂ν 1)-
          (∫ x, G.val (WithLp.ofLp x.val) ∂ν 0) =
            p.val.1*∫ t in (0 : ℝ)..1, ∑ i ∈ J, ∫ x, ∑ l,
              b l x.val*(ψ t i l).val x ∂ν t) := by
  intro H U g j b σ w μ hfinite hV ν Q hQ good W B K hgood hW hsq
  have hfiniteν (t) : IsFiniteMeasure (ν t) := by
    let := hfinite t
    dsimp only [ν]
    infer_instance
  let : ∀ t, IsFiniteMeasure (ν t) := hfiniteν
  choose χ hχ hglobal hlocal using fun t => literal_block_sources_internal a N (ν t) G hs E hE hne hEm
  refine ⟨?_,χ,hχ,hglobal,hlocal,?_⟩
  · intro t ht
    exact physical_normalized_chart_internal p a d e θ ε L y z hyL hzL Ky Kz hKys hKzs
      t N hLN frame (μ t) (hV t ht)
  · intro ψ hψ
    have hpair (t) (ht : t ∈ Icc (0 : ℝ) 1) :
        covariance (fun x => G.val (WithLp.ofLp x.val)) (fun x => Ky x.val-Kz x.val) (ν t) =
          ∑ i ∈ J, ∫ x, ∑ l, b l x.val*(ψ t i l).val x ∂ν t := by
      obtain ⟨φ,hφ,_,_,b₂,_,_,hc⟩ := physical_point_source_covariance_internal p a d e ha θ ε L hL
        y z hyL hzL Ky Kz hKy hKz hKys hKzs hε t ht N hLN frame G hs J hJ E hE hne hEm
        (μ t) (hV t ht) (Q t) (hQ t ht) (good t) (W t) (B t) (K t)
        (hgood t ht) (hW t ht) (hsq t ht)
      have he : φ = χ t := by
        funext i
        apply Subtype.ext
        exact Lp.ext ((hφ i).trans (hχ t i).symm)
      subst φ
      exact hc (ψ t) (hψ t ht)
    obtain ⟨_,hint,hid⟩ := physical_included_integrated_identity_internal p a d e ha θ ε L hL
      y z hyL hzL Ky Kz hKy hKz hε G N hLN frame μ hV
    refine ⟨hint.congr (fun t ht => hpair t ?_),?_⟩
    · rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le,ht.2⟩
    · exact hid.trans (congrArg (fun z => p.val.1*z)
        (intervalIntegral.integral_congr (fun t ht => hpair t (by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))))

end Physical

end Riesz2.CompatibleComparison

