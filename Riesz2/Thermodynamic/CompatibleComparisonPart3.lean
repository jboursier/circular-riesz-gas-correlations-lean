/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart2
public import Riesz2.Thermodynamic.InterpolationCoefficientBounds
public import Riesz2.ToMathlib.NeumannRealizationUnique
public import Riesz2.Frozen.DependsOnBlockCoordinates

/-!
# Physical derivatives for compatible comparison

Identification of the scalar realization in the existing physical fibre certificate, and
of the chart source and middle-normalized differential in the proof of Proposition 6.6.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper: the Neumann realization in
the very same physical fibre certificate is the canonical chart form.
The conclusion retains its law equality and the heterogeneous equality
of the entire transported form. -/
theorem intrinsic_certificate_canonical_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (AffineSimplex.chartDomain (a+1) N)) (Q : ScalarFormData ν)
    (hQ : InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q) :
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
    let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
    ∃ (ν₀ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ),
      IsEuclideanGibbsPotential volume ν₀ U V ∧
      let ξ : Measure U := ν₀.comap Subtype.val
      ∃ hV : IsEuclideanGibbsPotential volume (ξ.map Subtype.val) U V,
        ξ.map Subtype.val = ν₀ ∧ ξ.map j = ν ∧
        HEq Q (ScalarFormEmbedding.form ξ j hj
          (ScalarFormEmbedding.restriction ξ Subtype.val hv
            (IntrinsicScalarCore.form hU hB hV))) := by
  intro U hU hB j hj hv
  obtain ⟨ν₀,V,hV,Q₀,hreal,_hclosed,_hcons,hlaw,hform⟩ := hQ
  have hξ := (InterpolationTransport.orthonormal_law a L N hLN frame ν₀ V hV).1
  have hV' : IsEuclideanGibbsPotential volume
      ((ν₀.comap (Subtype.val : U → _)).map Subtype.val) U V := by
    rw [hξ]
    exact hV
  have he := NeumannRealization.unique Q₀ (IntrinsicScalarCore.form hU hB hV')
    hreal (IntrinsicScalarCore.realization hU hB hV')
  refine ⟨ν₀,V,hV,hV',hξ,hlaw,?_⟩
  rwa [he] at hform

/-- See the proof of Proposition 6.6 in the paper: any specified Gibbs
potential whose law has the physical pushforward can be used in the same
fibre certificate. Equality of the supported laws identifies the measures. Uniqueness of Neumann realization then identifies the complete forms.
There is no requirement that the certificate chose this potential. -/
theorem intrinsic_certificate_for_potential_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (AffineSimplex.chartDomain (a+1) N)) (Q : ScalarFormData ν)
    (hQ : InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q)
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (hlaw : (μ.comap Subtype.val).map
      (InterpolationTransport.orthonormalInclusion a L N hLN frame) = ν) :
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let ξ : Measure U := μ.comap Subtype.val
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
    let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
    ∃ hV' : IsEuclideanGibbsPotential volume (ξ.map Subtype.val) U V,
      ξ.map Subtype.val = μ ∧
      HEq Q (ScalarFormEmbedding.form ξ j hj
        (ScalarFormEmbedding.restriction ξ Subtype.val hv
          (IntrinsicScalarCore.form hU hB hV'))) := by
  intro U hU hB ξ j hj hv
  obtain ⟨μ₀,V₀,hV₀,Q₀,hreal,_hclosed,_hcons,hlaw₀,hform⟩ := hQ
  have heξ : μ₀.comap (Subtype.val : U → _) = ξ :=
    hj.map_injective (hlaw₀.trans hlaw.symm)
  have hξ := (InterpolationTransport.orthonormal_law a L N hLN frame μ V hV).1
  have hξ₀ := (InterpolationTransport.orthonormal_law a L N hLN frame μ₀ V₀ hV₀).1
  have heμ : μ₀ = μ := hξ₀.symm.trans
    ((congrArg (Measure.map (Subtype.val : U → _)) heξ).trans hξ)
  subst μ₀
  have hV' : IsEuclideanGibbsPotential volume (ξ.map Subtype.val) U V := by
    rw [hξ]
    exact hV
  have he := NeumannRealization.unique Q₀ (IntrinsicScalarCore.form hU hB hV')
    hreal (IntrinsicScalarCore.realization hU hB hV')
  refine ⟨hV',hξ,?_⟩
  rwa [he] at hform

section Jets

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
  {μ : Measure (EuclideanSpace ℝ (Fin d))}
  {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- See the proof of Proposition 6.6 in the paper: recover the value and the
actual derivative of a Neumann graph pair in the existing jet domain. -/
theorem jet_of_neumann_internal (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume μ U V)
    (f : Lp ℝ 2 μ) (df : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
    (hf : (f,df) ∈ neumannSobolevGraph μ U) :
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F = f ∧ ScalarForm.deriv _ F = df := by
  have := IntrinsicScalarCore.probability hV
  refine ⟨⟨WithLp.toLp 2 (f,df), ?_⟩, rfl, rfl⟩
  exact (EuclideanScalarForm.mem_neumannSobolevGraph_iff hU hB
    (IntrinsicScalarCore.supported hU hV) f df).mp hf

/-- See the proof of Proposition 6.6 in the paper: a globally Lipschitz
observable has a jet with its a.e. chart gradient under the
actual Gibbs law. -/
theorem lipschitz_jet_internal (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume μ U V)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] f ∧ ScalarForm.deriv _ F =ᵐ[μ] gradient f := by
  have := IntrinsicScalarCore.probability hV
  have hac : μ ≪ volume := by
    rw [hV.2.2.2]
    exact Measure.smul_absolutelyContinuous.trans
      ((withDensity_absolutelyContinuous _ _).trans
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
  have hw := Riesz1.WeightedSobolev.isWeightedH1_of_lipschitz hB
    (IntrinsicScalarCore.supported hU hV) hac hf
  have hgraph := (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hB
    (IntrinsicScalarCore.supported hU hV) hw.1 hw.2.1).mp hw
  obtain ⟨F,hF,hDF⟩ := jet_of_neumann_internal hU hB hV _ _ hgraph
  exact ⟨F,hF ▸ hw.1.coeFn_toLp,hDF ▸ hw.2.1.coeFn_toLp⟩

end Jets

/-- See Theorem 4 and the proof of Proposition 6.6 of the paper: the block
observable pulled back to the specified orthonormal fibre has its Sobolev jet. No values of an ambient derivative on a null fibre are used. -/
theorem block_jet_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (G : BlockObservable a.succPNat) :
    let _U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let g := fun x => G.val (WithLp.ofLp (AffineSimplex.centredChart a L (frame.symm x)))
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] g ∧ ScalarForm.deriv _ F =ᵐ[μ] gradient g := by
  intro _U hU hB g
  obtain ⟨K,hK⟩ := G.property
  apply lipschitz_jet_internal hU hB hV g
  exact hK.comp ((PiLp.lipschitzWith_ofLp 2 (fun _ : Fin (a+1) => ℝ)).comp
    ((AffineSimplex.isometry_centredChart a L).lipschitzWith.comp frame.symm.isometry.lipschitzWith))

section Differential

/-- See Lemma 6.4 of the paper: the pinned force reconstructed from an actual
ambient differential is its gradient minus the middle component. -/
theorem pinned_gradient_internal {a : ℕ}
    (D : EuclideanSpace ℝ (Fin (a+1)) → ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) :
    InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D u (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) =
      fun j => gradient D u j-gradient D u (InteractionDifferential.middle a) := by
  have he (i : Fin a) : fderiv ℝ D u
      (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1)) =
      gradient D u i.castSucc-gradient D u i.succ := by
    rw [← inner_gradient_left]
    change inner ℝ (gradient D u)
      (EuclideanSpace.single i.castSucc 1-EuclideanSpace.single i.succ 1) = _
    simp only [inner_sub_right, EuclideanSpace.inner_single_right,
      one_mul, conj_trivial]
  simp_rw [he]
  exact InteractionDifferential.pinnedRepresentative_of_coefficients _

/-- See the proof of Proposition 6.6 in the paper: the chart gradient is the
transpose-frame compression of the ambient gradient, at every point of
differentiability. -/
theorem frame_gradient_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (D : EuclideanSpace ℝ (Fin (a+1)) → ℝ) (x : EuclideanSpace ℝ (Fin a))
    (hD : DifferentiableAt ℝ D (AffineSimplex.centredChart a L (frame.symm x)))
    (k : Fin a) :
    gradient (fun y => D (AffineSimplex.centredChart a L (frame.symm y))) x k =
      ∑ j, A j k*gradient D (AffineSimplex.centredChart a L (frame.symm x)) j := by
  let B := (AffineSimplex.Tangent a).subtypeL.comp
    frame.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg := B.hasFDerivAt.add_const (AffineSimplex.centre a L) (x := x)
  have hd := hD.hasFDerivAt.comp x hg
  have hb : B (EuclideanSpace.single k 1) = WithLp.toLp 2 (fun j => A j k) := by
    apply PiLp.ext
    intro j
    have hh := congrFun (hA (Pi.single k 1)) j
    simpa [B, Matrix.mulVec, dotProduct, Pi.single_apply] using hh.symm
  have hh := congrArg (fun l : EuclideanSpace ℝ (Fin a) →L[ℝ] ℝ =>
    l (EuclideanSpace.single k 1)) hd.fderiv
  rw [← inner_gradient_left] at hh
  simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial,
    ContinuousLinearMap.comp_apply, hb] at hh
  rw [← inner_gradient_left, PiLp.inner_apply] at hh
  change gradient (fun y => D (AffineSimplex.centredChart a L (frame.symm y))) x k =
    ∑ j, (WithLp.toLp 2 (fun j => A j k) : EuclideanSpace ℝ (Fin (a+1))) j *
      gradient D (AffineSimplex.centredChart a L (frame.symm x)) j at hh
  exact hh

/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the middle pin
vanishes under transpose-frame compression. This is the pointwise
differential identification needed for the physical `hb`. -/
theorem frame_pinned_differential_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (D : EuclideanSpace ℝ (Fin (a+1)) → ℝ) (x : EuclideanSpace ℝ (Fin a))
    (hD : DifferentiableAt ℝ D (AffineSimplex.centredChart a L (frame.symm x)))
    (k : Fin a) :
    (∑ j, A j k*InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D (AffineSimplex.centredChart a L (frame.symm x))
        (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j) =
      gradient (fun y => D (AffineSimplex.centredChart a L (frame.symm y))) x k := by
  have hz : ∑ j, A j k = 0 := by
    have ht := (AffineSimplex.mem_hsOrthSubspace_iff a _).mp
      (frame.symm (EuclideanSpace.single k 1)).property
    have hh := hA (Pi.single k 1)
    have he : A *ᵥ Pi.single k 1 = fun j => A j k := by
      ext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [he] at hh
    exact (congrArg (fun t : Fin (a+1) → ℝ => ∑ j, t j) hh).trans ht
  rw [pinned_gradient_internal, frame_gradient_internal a L frame A hA D x hD k]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hz,
    zero_mul, sub_zero]

end Differential

section Restriction

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (f : X → Y) (hf : MeasurableEmbedding f)
  (Q : ScalarFormData (μ.map f))

local notation "Qr" => ScalarFormEmbedding.restriction μ f hf Q
local notation "T" => ScalarFormEmbedding.pullback μ f hf
local notation "R" => ScalarFormEmbedding.restrictionEquiv μ f hf Q

/-- See the proof of Proposition 6.6 in the paper: restriction to the supported
carrier preserves the entire natural matrix-energy domain. -/
theorem weighted_domain_restriction_iff_internal {ι : Type} [Fintype ι]
    (M : Y → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ)) (u : ι → Qr.1) :
    WeightedFormDomain Qr (M ∘ f) S u ↔
      WeightedFormDomain Q M S (fun i => R (u i)) := by
  have hi := InterpolationTransport.matrixFieldPair_integrable_iff μ f hf ι M
    (fun i => (R (u i)).val) (fun i => (R (u i)).val)
  have he (i : ι) : T (R (u i)).val = (u i).val := (T).apply_symm_apply _
  simp_rw [he] at hi
  have hs : (∀ᵐ x ∂μ.map f, (fun i => (R (u i)).val x) ∈ S) ↔
      ∀ᵐ x ∂μ, (fun i => (u i).val x) ∈ S := by
    rw [hf.ae_map_iff]
    have hh := ae_all_iff.mpr (fun i => ScalarFormEmbedding.inverse_ae μ f hf (u i).val)
    apply eventually_congr
    filter_upwards [hh] with x hx
    simp only [Function.comp_apply] at hx
    exact iff_of_eq (congrArg (fun t : ι → ℝ => t ∈ S) (funext hx))
  exact and_congr hs.symm hi.symm

/-- See the proof of Proposition 6.6 in the paper: the restriction leg of the
physical transport preserves the full weak equation and all finite-energy
tests, retaining the literal source. -/
theorem weak_equation_restriction_iff_internal {ι : Type} [Fintype ι]
    (M : Y → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (v : ι → Lp ℝ 2 (μ.map f)) (u : ι → Qr.1) :
    WeightedWeakSolution Qr (M ∘ f) S (fun i => T (v i)) u ↔
      WeightedWeakSolution Q M S v (fun i => R (u i)) := by
  have he (w : ι → Qr.1) :
      (∑ i, Qr.2 (u i) (w i)) +
        (∫ x, matrixFieldPair (M ∘ f) (fun i => (u i).val) (fun i => (w i).val) x ∂μ) =
      (∑ i, Q.2 (R (u i)) (R (w i))) +
        ∫ y, matrixFieldPair M (fun i => (R (u i)).val)
          (fun i => (R (w i)).val) y ∂μ.map f := by
    rw [InterpolationTransport.matrixFieldPair_integral μ f hf]
    have ht (z : Qr.1) : T (R z).val = z.val := (T).apply_symm_apply _
    simp_rw [ht]
    rfl
  have hs (w : ι → Qr.1) :
      (∑ i, inner ℝ (T (v i)) (w i).val) =
        ∑ i, inner ℝ (v i) (R (w i)).val := by
    apply Finset.sum_congr rfl
    intro i _
    have hh := (T).inner_map_map (v i) ((T).symm (w i).val)
    rw [LinearIsometryEquiv.apply_symm_apply] at hh
    exact hh
  have hi (w : ι → Qr.1) :
      Integrable (matrixFieldPair M (fun i => (R (u i)).val)
        (fun i => (R (w i)).val)) (μ.map f) ↔
      Integrable (matrixFieldPair (M ∘ f) (fun i => (u i).val)
        (fun i => (w i).val)) μ := by
    have hh := InterpolationTransport.matrixFieldPair_integrable_iff μ f hf ι M
      (fun i => (R (u i)).val) (fun i => (R (w i)).val)
    have ht (z : Qr.1) : T (R z).val = z.val := (T).apply_symm_apply _
    simpa only [ht] using hh
  constructor
  · rintro ⟨hu,hweak⟩
    refine ⟨(weighted_domain_restriction_iff_internal μ f hf Q M S u).mp hu, ?_⟩
    intro w hw
    let w' : ι → Qr.1 := fun i => (R).symm (w i)
    have hw' : WeightedFormDomain Qr (M ∘ f) S w' :=
      (weighted_domain_restriction_iff_internal μ f hf Q M S w').mpr (by
        simpa only [w', LinearEquiv.apply_symm_apply] using hw)
    obtain ⟨hint,hh⟩ := hweak w' hw'
    have hint' := (hi w').mpr hint
    rw [he,hs] at hh
    simpa only [w', LinearEquiv.apply_symm_apply] using And.intro hint' hh
  · rintro ⟨hu,hweak⟩
    refine ⟨(weighted_domain_restriction_iff_internal μ f hf Q M S u).mpr hu, ?_⟩
    intro w hw
    obtain ⟨hint,hh⟩ := hweak (fun i => R (w i))
      ((weighted_domain_restriction_iff_internal μ f hf Q M S w).mp hw)
    exact ⟨(hi w).mp hint, by rwa [he,hs]⟩

/-- See the proof of Proposition 6.6 in the paper: the signed differential
pairing transports through restriction using its actual L² classes. -/
theorem pairing_integral_restriction_internal {ι : Type} [Fintype ι]
    (b : ι → Lp ℝ 2 (μ.map f)) (u : ι → Qr.1) :
    (∫ x, ∑ i, T (b i) x*(u i).val x ∂μ) =
      ∫ y, ∑ i, b i y*(R (u i)).val y ∂μ.map f := by
  rw [hf.integral_map]
  apply integral_congr_ae
  have hb := ae_all_iff.mpr (fun i => ScalarFormEmbedding.pullback_ae μ f hf (b i))
  have hu := ae_all_iff.mpr (fun i => ScalarFormEmbedding.inverse_ae μ f hf (u i).val)
  filter_upwards [hb,hu] with x hx hy
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg₂ (fun r s : ℝ => r*s) (hx i) (hy i).symm

end Restriction

section Consecutive

variable {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  (μ : Measure X) (f : X → Y) (hf : MeasurableEmbedding f)
  (j : X → Z) (hj : MeasurableEmbedding j) (Q₀ : ScalarFormData (μ.map f))

local notation "Qr" => ScalarFormEmbedding.restriction μ f hf Q₀
local notation "Qj" => ScalarFormEmbedding.form μ j hj Qr
local notation "Tf" => ScalarFormEmbedding.pullback μ f hf
local notation "Tj" => ScalarFormEmbedding.pullback μ j hj
local notation "Dj" => ScalarFormEmbedding.domainEquiv μ j hj Qr
local notation "R" => ScalarFormEmbedding.restrictionEquiv μ f hf Q₀

/-- See the proof of Proposition 6.6 in the paper: consecutive restriction and
embedding transports preserve the full equation on the same scalar form.
The matrix fields agree on the common supported carrier. They need not
have bounded multiplication operators. -/
theorem consecutive_weak_equation_internal {ι : Type} [Fintype ι]
    (M : Z → Matrix ι ι ℝ) (M₀ : Y → Matrix ι ι ℝ)
    (hM : M ∘ j =ᵐ[μ] M₀ ∘ f) (S : Submodule ℝ (ι → ℝ))
    (v : ι → Lp ℝ 2 (μ.map j)) (u : ι → Qj.1) :
    WeightedWeakSolution Qj M S v u ↔
      WeightedWeakSolution Q₀ M₀ S
        (fun i => (Tf).symm (Tj (v i))) (fun i => R (Dj (u i))) := by
  have hh := weak_equation_embedding_iff_internal μ j hj Qr M S v u
  have hm := MatrixFieldTransport.weak_congr Qr hM S
    (fun i => Tj (v i)) (fun i => Dj (u i))
  have hr := weak_equation_restriction_iff_internal μ f hf Q₀ M₀ S
    (fun i => (Tf).symm (Tj (v i))) (fun i => Dj (u i))
  simp only [LinearIsometryEquiv.apply_symm_apply] at hr
  exact hh.trans (hm.trans hr)

/-- See the proof of Proposition 6.6 in the paper: the same consecutive
transports preserve the signed differential pairing, component by
component on the complete scalar domain. -/
theorem consecutive_pairing_integral_internal {ι : Type} [Fintype ι]
    (b : ι → Lp ℝ 2 (μ.map j)) (u : ι → Qj.1) :
    (∫ z, ∑ i, b i z*(u i).val z ∂μ.map j) =
      ∫ y, ∑ i, (Tf).symm (Tj (b i)) y*(R (Dj (u i))).val y ∂μ.map f := by
  rw [pairing_integral_embedding_internal μ j hj Qr b u]
  have hh := pairing_integral_restriction_internal μ f hf Q₀
    (fun i => (Tf).symm (Tj (b i))) (fun i => Dj (u i))
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

/-- See the proof of Proposition 6.6 in the paper: covariance uses the very
same consecutive L² equivalences as the sources and the pairings. -/
theorem consecutive_covariance_internal (G K : Lp ℝ 2 (μ.map j)) :
    covariance G K (μ.map j) =
      covariance ((Tf).symm (Tj G)) ((Tf).symm (Tj K)) (μ.map f) := by
  rw [covariance_embedding_internal μ j hj G K]
  have hh := covariance_embedding_internal μ f hf ((Tf).symm (Tj G))
    ((Tf).symm (Tj K))
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh.symm

end Consecutive

section DerivativeClasses

open RectangularFormTransport

/-- See the proof of Proposition 6.6 in the paper: an interior-smooth
interaction with finite value and gradient norms has a jet in the
literal Neumann completion. The collision barrier closes the interior
core. Interior smoothness alone is not silently treated as membership. -/
theorem interior_jet_internal {d : ℕ} (hd : 1 ≤ d)
    {U : Set (EuclideanSpace ℝ (Fin d))} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume μ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹^2-C ≤
      ‖gradient V x‖^2/4-Laplacian.laplacian V x/2)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hs : ContDiffOn ℝ ∞ f U)
    (hf : MemLp f 2 μ) (hdf : MemLp (gradient f) 2 μ) :
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] f ∧ ScalarForm.deriv _ F =ᵐ[μ] gradient f := by
  let : NeZero d := ⟨by omega⟩
  have hgraph := (IntrinsicScalarCore.mem_interior_completion_iff hU hB hV hC hbar
    (hf.toLp f) (hdf.toLp (gradient f))).mp (subset_closure ⟨f,hs,hf,hdf,rfl⟩)
  obtain ⟨F,hF,hDF⟩ := jet_of_neumann_internal hU hB hV _ _ hgraph
  exact ⟨F,hF ▸ hf.coeFn_toLp,hDF ▸ hdf.coeFn_toLp⟩

/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the actual
middle-normalized differential gives precisely the derivative L²
classes required by `ambient_covariance_point_sources_internal`. -/
theorem differential_lp_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (μ : Measure (EuclideanSpace ℝ (Fin a)))
    (D : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hD : ∀ᵐ x ∂μ, DifferentiableAt ℝ D (AffineSimplex.centredChart a L (frame.symm x)))
    (b : Fin (a+1) → Lp ℝ 2 μ)
    (hb : ∀ j, b j =ᵐ[μ] fun x => InteractionDifferential.pinnedRepresentative
      (fun i : Fin a => fderiv ℝ D (AffineSimplex.centredChart a L (frame.symm x))
        (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j)
    (df : Lp (EuclideanSpace ℝ (Fin a)) 2 μ)
    (hdf : df =ᵐ[μ] gradient (fun y => D (AffineSimplex.centredChart a L (frame.symm y)))) :
    tupleMap A.transpose b = fun k => DifferentiatedPoisson.coordinateLp k df := by
  funext k
  apply Lp.ext
  have hb' := ae_all_iff.mpr hb
  filter_upwards [tupleMap_lp_ae A.transpose b, hb', hD, hdf,
    DifferentiatedPoisson.coordinateLp_ae k df] with x hx hy hz hw hv
  rw [hx, hv, hw]
  simp only [Matrix.transpose_apply, hy]
  exact frame_pinned_differential_internal a L frame A hA D x hz k

/-- See the proof of Proposition 6.6 in the paper: the ambient source uses the
literal coordinate derivatives, with its prescribed support, and its
transpose is the chart derivative in L². -/
theorem supported_source_lp_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (μ : Measure (EuclideanSpace ℝ (Fin a)))
    (G : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hG : ∀ᵐ x ∂μ, DifferentiableAt ℝ G (AffineSimplex.centredChart a L (frame.symm x)))
    (J : Finset (Fin (a+1))) (χ : Fin (a+1) → Lp ℝ 2 μ)
    (hχ : ∀ j, (if j ∈ J then χ j else 0) =ᵐ[μ]
      fun x => gradient G (AffineSimplex.centredChart a L (frame.symm x)) j)
    (df : Lp (EuclideanSpace ℝ (Fin a)) 2 μ)
    (hdf : df =ᵐ[μ] gradient (fun y => G (AffineSimplex.centredChart a L (frame.symm y)))) :
    tupleMap A.transpose (fun j => if j ∈ J then χ j else 0) =
      fun k => DifferentiatedPoisson.coordinateLp k df := by
  funext k
  apply Lp.ext
  have hχ' := ae_all_iff.mpr hχ
  filter_upwards [tupleMap_lp_ae A.transpose (fun j => if j ∈ J then χ j else 0),
    hχ',hG,hdf,DifferentiatedPoisson.coordinateLp_ae k df] with x hx hy hz hw hv
  rw [hx,hv,hw]
  simp only [Matrix.transpose_apply,hy]
  exact (frame_gradient_internal a L frame A hA G x hz k).symm

/-- See Theorem 4 and the proof of Proposition 6.6 of the paper: a smooth block observable has zero classical derivative in each unused coordinate.
This uses the dependence predicate itself. -/
theorem gradient_zero_off_block_internal (a : ℕ) (G : BlockObservable a.succPNat)
    (J : Finset (Fin (a+1))) (hJ : DependsOnBlockCoordinates G J)
    (u : EuclideanSpace ℝ (Fin (a+1)))
    (hd : DifferentiableAt ℝ (fun y => G.val (WithLp.ofLp y)) u)
    (i : Fin (a+1)) (hi : i ∉ J) :
    gradient (fun y => G.val (WithLp.ofLp y)) u i = 0 := by
  let e := EuclideanSpace.single i (1 : ℝ)
  have he : (fun t : ℝ => G.val (WithLp.ofLp (u+t • e))) =
      fun _ : ℝ => G.val (WithLp.ofLp u) := by
    funext t
    apply hJ
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp only [e, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      ite_eq_right hji, smul_eq_mul, mul_zero, add_zero]
  have hp : HasDerivAt (fun t : ℝ => u+t • e) e 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add u
  have hd' : HasFDerivAt (fun y => G.val (WithLp.ofLp y))
      (fderiv ℝ (fun y => G.val (WithLp.ofLp y)) u) (u+(0 : ℝ) • e) := by
    simpa only [zero_smul,add_zero] using hd.hasFDerivAt
  have hh := hd'.comp_hasDerivAt 0 hp
  simp only [Function.comp_def] at hh
  rw [he] at hh
  have hz := hh.unique (hasDerivAt_const (0 : ℝ) (G.val (WithLp.ofLp u)))
  rw [← inner_gradient_left] at hz
  simpa only [e,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using hz

/-- See the proof of Proposition 6.6 in the paper: construct the supported
coordinate derivative classes of a smooth block observable on the
actual chart law, and prove their exact `hv` identification. -/
theorem smooth_block_source_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (G : BlockObservable a.succPNat)
    (hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (a+1)) => G.val (WithLp.ofLp y)))
    (J : Finset (Fin (a+1))) (hJ : DependsOnBlockCoordinates G J) :
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let g := fun x => G.val (WithLp.ofLp (AffineSimplex.centredChart a L (frame.symm x)))
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] g ∧
      ∃ χ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, χ j =ᵐ[μ] fun x =>
          gradient (fun y => G.val (WithLp.ofLp y))
            (AffineSimplex.centredChart a L (frame.symm x)) j) ∧
        tupleMap A.transpose (fun j => if j ∈ J then χ j else 0) =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  intro hU hB g
  have := IntrinsicScalarCore.probability hV
  obtain ⟨F,hF,hDF⟩ := block_jet_internal a L frame μ V hV G
  have hg : Continuous (fun x => AffineSimplex.centredChart a L (frame.symm x)) :=
    (AffineSimplex.isometry_centredChart a L).continuous.comp frame.symm.continuous
  have hdg := Riesz1.WeightedSobolev.continuous_gradient_of_contDiff hs
  have hm (i : Fin (a+1)) : MemLp (fun x =>
      gradient (fun y => G.val (WithLp.ofLp y))
        (AffineSimplex.centredChart a L (frame.symm x)) i) 2 μ := by
    exact Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB
      (IntrinsicScalarCore.supported hU hV)
      (((PiLp.continuous_apply 2 (fun _ : Fin (a+1) => ℝ) i).comp (hdg.comp hg)).continuousOn)
  let χ : Fin (a+1) → Lp ℝ 2 μ := fun i => (hm i).toLp _
  have hχ (i : Fin (a+1)) : χ i =ᵐ[μ] fun x =>
      gradient (fun y => G.val (WithLp.ofLp y))
        (AffineSimplex.centredChart a L (frame.symm x)) i := (hm i).coeFn_toLp
  refine ⟨F,hF,χ,hχ,?_⟩
  apply supported_source_lp_internal a L frame A hA μ
    (fun y => G.val (WithLp.ofLp y))
    (ae_of_all _ fun x => hs.differentiable (by simp) _) J χ ?_ _ hDF
  intro i
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi]
    exact hχ i
  · simp only [ite_eq_right hi]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    exact hx.trans (gradient_zero_off_block_internal a G J hJ _
      (hs.differentiable (by simp) _) i hi).symm

end DerivativeClasses

/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the good/bad coefficient bounds give scalar L² classes of the actual pinned
differential, the full interaction jet, and its exact derivative-class
identification. The interior-core step uses the same chart collision
barrier as the covariance representation. -/
theorem interaction_jet_from_envelope_internal (a : ℕ) (ha : 1 ≤ a) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (D : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ D (AffineSimplex.centredChart a L (frame.symm x)))
    (hs : ContDiffOn ℝ ∞ (fun x => D (AffineSimplex.centredChart a L (frame.symm x)))
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)))
    (hm : MemLp (fun x => D (AffineSimplex.centredChart a L (frame.symm x))) 2 μ)
    (good : Set (EuclideanSpace ℝ (Fin a)))
    (W : EuclideanSpace ℝ (Fin a) → ℝ) (B K C : ℝ) (hC : 0 ≤ C)
    (hbar : ∀ x ∈ frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      (Metric.infDist x (frontier (frame ''
        (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L))))⁻¹^2-C ≤
        ‖gradient V x‖^2/4-Laplacian.laplacian V x/2) :
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let b := fun j x => InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D (g x) (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j
    (∀ j, ∀ᵐ x ∂μ.restrict good, |b j x| ≤ B) →
    IntegrableOn W goodᶜ μ →
    (∀ j, ∀ᵐ x ∂μ.restrict goodᶜ, b j x^2 ≤ K*W x) →
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap A.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  intro hU hB g b hgood hW hsq
  have := IntrinsicScalarCore.probability hV
  have hg : Continuous g :=
    (AffineSimplex.isometry_centredChart a L).continuous.comp frame.symm.continuous
  have hgrad : Measurable (gradient D) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (a+1)))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ D)
  have hb (j : Fin (a+1)) : Measurable (b j) := by
    have hp := ((PiLp.continuous_apply 2 (fun _ : Fin (a+1) => ℝ) j).measurable.comp
      (hgrad.comp hg.measurable)).sub
        ((PiLp.continuous_apply 2 (fun _ : Fin (a+1) => ℝ)
          (InteractionDifferential.middle a)).measurable.comp (hgrad.comp hg.measurable))
    convert hp using 1
    funext x
    exact congrFun (pinned_gradient_internal D (g x)) j
  have hb₂ (j : Fin (a+1)) : MemLp (b j) 2 μ :=
    GoodSetL2Comparison.coefficient_memLp_two (b j) W (hb j).aestronglyMeasurable
      B K (hgood j) hW (hsq j)
  have hsum (k : Fin a) : MemLp (fun x => ∑ j, A j k*b j x) 2 μ := by
    exact memLp_finsetSum _ (fun j _ => (hb₂ j).const_mul (A j k))
  have hd₂ : MemLp (gradient (fun x => D (g x))) 2 μ := by
    have ht : MemLp (fun x => (WithLp.toLp 2 (fun k => ∑ j, A j k*b j x) :
        EuclideanSpace ℝ (Fin a))) 2 μ := memLp_piLp_iff.mpr hsum
    apply ht.ae_eq
    filter_upwards [hd] with x hx
    apply PiLp.ext
    intro k
    exact frame_pinned_differential_internal a L frame A hA D x hx k
  obtain ⟨F,hF,hDF⟩ := interior_jet_internal ha hU hB hV hC hbar
    (fun x => D (g x)) hs hm hd₂
  let b₂ : Fin (a+1) → Lp ℝ 2 μ := fun j => (hb₂ j).toLp (b j)
  have he (j : Fin (a+1)) : b₂ j =ᵐ[μ] b j := (hb₂ j).coeFn_toLp
  exact ⟨F,hF,b₂,he,differential_lp_internal a L frame A hA μ D hd b₂ he _ hDF⟩

/-- See the proof of Proposition 6.6 in the paper: covariance and the point
source solutions transport consecutively through restriction and physical
inclusion. The form is literally the transport of the chart realization,
as identified by `intrinsic_certificate_for_potential_internal`. The
analytic chart and derivative inputs remain explicit in this internal
assembly theorem. -/
theorem consecutive_covariance_point_sources_internal {d : ℕ} (n : ℕ+)
    {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (f : X → EuclideanSpace ℝ (Fin d)) (hf : MeasurableEmbedding f)
    (j : X → Z) (hj : MeasurableEmbedding j)
    {U : Set (EuclideanSpace ℝ (Fin d))} {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume (μ.map f) U V)
    (hwell : ConditionalWellPosedness.EuclideanWellPosed hU hB hV)
    (A : Matrix (Fin (n : ℕ)) (Fin d) ℝ) (hA : A.transpose*A = 1)
    (hArange : A.mulVecLin.range = zeroSumComponents (Fin (n : ℕ)))
    (M : Z → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (M₀ : EuclideanSpace ℝ (Fin d) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hfield : M ∘ j =ᵐ[μ] M₀ ∘ f)
    (hM : (fun x => A.transpose*M₀ x*A) =ᵐ[μ.map f] hessianMatrix V)
    (hpos : ∀ᵐ x ∂μ.map j, (M x).PosSemidef)
    (hmeas : ∀ i k, Measurable (fun x => M x i k))
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ᵐ x ∂μ.map j, ∀ t ∈ zeroSumComponents (Fin (n : ℕ)),
      c*(∑ i, t i^2) ≤ ∑ i, ∑ k, t i*M x i k*t k) :
    let Q₀ := IntrinsicScalarCore.form hU hB hV
    let Qr := ScalarFormEmbedding.restriction μ f hf Q₀
    let Q := ScalarFormEmbedding.form μ j hj Qr
    let Tf := ScalarFormEmbedding.pullback μ f hf
    let Tj := ScalarFormEmbedding.pullback μ j hj
    ∀ (G K : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV))
      (g k : Lp ℝ 2 (μ.map j)),
      Tf.symm (Tj g) = ScalarForm.value _ G →
      Tf.symm (Tj k) = ScalarForm.value _ K →
    ∀ (J : Finset (Fin (n : ℕ))) (χ b : Fin (n : ℕ) → Lp ℝ 2 (μ.map j)),
      RectangularFormTransport.tupleMap A.transpose
        (fun i => Tf.symm (Tj (if i ∈ J then χ i else 0))) =
          (fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ G)) →
      RectangularFormTransport.tupleMap A.transpose (fun i => Tf.symm (Tj (b i))) =
          (fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ K)) →
    ∀ ψ : Fin (n : ℕ) → Fin (n : ℕ) → Q.1,
      (∀ i ∈ J, WeightedWeakSolution Q M (zeroSumComponents (Fin (n : ℕ)))
        (fun l => if l = i then χ i else 0) (ψ i)) →
      covariance g k (μ.map j) =
        ∑ i ∈ J, ∫ x, ∑ l, b l x*(ψ i l).val x ∂μ.map j := by
  intro Q₀ Qr Q Tf Tj G K g k hg hk J χ b hv hb ψ hψ
  let Dj := ScalarFormEmbedding.domainEquiv μ j hj Qr
  let R := ScalarFormEmbedding.restrictionEquiv μ f hf Q₀
  obtain ⟨u₀,hu₀,_hint,hcov⟩ := ambient_covariance_lift_internal hU hB hV hwell
    A hA M₀ hM G K
      (fun i => Tf.symm (Tj (if i ∈ J then χ i else 0)))
      (fun i => Tf.symm (Tj (b i))) hv hb
  rw [hArange] at hu₀
  let u : Fin (n : ℕ) → Q.1 := fun i => Dj.symm (R.symm (u₀ i))
  have he (i : Fin (n : ℕ)) : R (Dj (u i)) = u₀ i := by
    simp only [u,LinearEquiv.apply_symm_apply]
  have hu : WeightedWeakSolution Q M (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i ∈ J then χ i else 0) u := by
    apply (consecutive_weak_equation_internal μ f hf j hj Q₀ M M₀ hfield _ _ u).mpr
    change WeightedWeakSolution Q₀ M₀ (zeroSumComponents (Fin (n : ℕ)))
      (fun i => Tf.symm (Tj (if i ∈ J then χ i else 0))) (fun i => R (Dj (u i)))
    simpa only [he] using hu₀
  have hclosed := ScalarFormEmbedding.closed_dirichlet μ j hj Qr
    (ScalarFormEmbedding.restriction_closed_dirichlet μ f hf Q₀
      (IntrinsicScalarCore.closed_dirichlet hU hB hV))
  have hsum := point_sources_superpose_internal Q hclosed n M hpos hmeas
    c hc hlower J χ ψ hψ u hu
  have hcov' : covariance g k (μ.map j) =
      ∫ x, ∑ l, b l x*(u l).val x ∂μ.map j := by
    rw [consecutive_covariance_internal μ f hf j hj g k,hg,hk,hcov,
      consecutive_pairing_integral_internal μ f hf j hj Q₀ b u]
    change (∫ x, ∑ l, Tf.symm (Tj (b l)) x*(u₀ l).val x ∂μ.map f) =
      ∫ x, ∑ l, Tf.symm (Tj (b l)) x*(R (Dj (u l))).val x ∂μ.map f
    simp only [he]
  rw [hcov',hsum]
  have hval : (fun l => (∑ i ∈ J, ψ i l).val) =
      ∑ i ∈ J, (fun l => (ψ i l).val) := by
    funext l
    simp only [Finset.sum_apply,Submodule.coe_sum]
  simp only [Finset.sum_apply]
  change (∫ x, ∑ l, b l x*(fun l => (∑ i ∈ J, ψ i l).val) l x ∂μ.map j) = _
  rw [hval]
  exact WeightedWeakSuperposition.pairing_finset_sum J b (fun i l => (ψ i l).val)

end Riesz2.CompatibleComparison
