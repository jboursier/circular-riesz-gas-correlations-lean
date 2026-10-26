/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationMatrix
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart10
public import Riesz2.Thermodynamic.InterpolationExceptional
public import Riesz2.Thermodynamic.AuxiliaryMeanPart2
public import Riesz2.ToMathlib.ScalarFormEmbedding
import all Riesz2.DecayLong.BoundarySchurBounds

/-!
# Common mass fibre and interpolation chart

The inclusion changes the measured carrier and preserves the normalized Hausdorff law,
good event and weight. The transported scalar form is intrinsic. These bridges serve
Subsection 6.1 and Lemma 6.4.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationTransport

open InterpolantLocalLaws

/-- See Subsection 6.1 of the paper: inclusion of the entire positive mass fibre
into a larger positive active chart. -/
def inclusion (a : ℕ) (L N : ℝ) (hLN : L < N) :
    AffineSimplex.massSimplex a L → AffineSimplex.chartDomain (a+1) N :=
  fun u => ⟨u.val, u.property.1, u.property.2.trans_lt hLN⟩

/-- See Subsection 6.1 of the paper: the inclusion is a measurable embedding,
including a zero dimensional mass fibre. -/
theorem measurableEmbedding_inclusion (a : ℕ) (L N : ℝ) (hLN : L < N) :
    MeasurableEmbedding (inclusion a L N hLN) := by
  have hs := MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex a L)
  refine ⟨fun u v h => Subtype.ext (congrArg (fun x : AffineSimplex.chartDomain (a+1) N => x.val) h),
    measurable_subtype_coe.subtype_mk, ?_⟩
  intro E hE
  have he : inclusion a L N hLN '' E =
      (Subtype.val : AffineSimplex.chartDomain (a+1) N → _) ⁻¹'
        ((Subtype.val : AffineSimplex.massSimplex a L → _) '' E) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, he⟩
      exact ⟨u, hu, Subtype.ext he⟩
  rw [he]
  exact (hs.measurableSet_image.mpr hE).preimage measurable_subtype_coe

/-- See Subsection 6.1 of the paper: forgetting the chart subtype recovers exactly
the physical Hausdorff law used by the local laws. -/
theorem map_inclusion_val (a : ℕ) (L N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L)) :
    (ρ.map (inclusion a L N hLN)).map Subtype.val = ρ.map Subtype.val := by
  rw [Measure.map_map measurable_subtype_coe
    (measurableEmbedding_inclusion a L N hLN).measurable]
  rfl

/-- See Subsection 6.1 of the paper: every physical event has the same probability
after the inclusion, with no measurability restriction on the event. -/
theorem map_inclusion_apply (a : ℕ) (L N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L))
    (E : Set (EuclideanSpace ℝ (Fin (a+1)))) :
    (ρ.map (inclusion a L N hLN)) {x | x.val ∈ E} = (ρ.map Subtype.val) E := by
  rw [(measurableEmbedding_inclusion a L N hLN).map_apply,
    (MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex a L)).map_apply]
  rfl

/-- See Subsection 6.1 of the paper: restricted nonnegative integrals are unchanged
under the inclusion, for arbitrary physical events and envelopes. -/
theorem lintegral_inclusion (a : ℕ) (L N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L))
    (E : Set (EuclideanSpace ℝ (Fin (a+1))))
    (W : EuclideanSpace ℝ (Fin (a+1)) → ℝ≥0∞) :
    (∫⁻ x in {x | x.val ∈ E}, W x.val ∂ρ.map (inclusion a L N hLN)) =
      ∫⁻ u in E, W u ∂ρ.map Subtype.val := by
  have hi := measurableEmbedding_inclusion a L N hLN
  have hv := MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex a L)
  rw [hi.restrict_map, hi.lintegral_map, hv.restrict_map, hv.lintegral_map]
  rfl

/-- See Subsection 6.1 of the paper: a nonempty positive exterior leaves strictly
less than the physical period as active mass. -/
theorem compatible_mass_lt (a d : ℕ) (hd : 1 ≤ d) (L : ℝ)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (hcompat : (∑ j, y.val j) + L = ((d+a : ℕ)+1 : ℝ)) :
    L < ((d+a : ℕ)+1 : ℝ) := by
  have hp : 0 < ∑ j, y.val j := by
    apply Finset.sum_pos'
    · intro j _; exact (y.property.1 j).le
    · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, y.property.1 _⟩
  linarith

/-- See Subsection 6.1 of the paper: probability transports on the same law. -/
theorem probability (a : ℕ) (L N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (ρ.map (inclusion a L N hLN)) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurableEmbedding_inclusion a L N hLN).measurable.aemeasurable).mpr inferInstance

/-- See Subsection 6.1 of the paper: the chart good event has the literal original
fine-event preimage on the positive mass fibre. -/
theorem goodSet_preimage (s : Riesz1.RieszExponent) (a d : ℕ)
    (L η : ℝ) (hLN : L < ((a+1+d : ℕ)+1 : ℝ)) :
    inclusion a L ((a+1+d : ℕ)+1) hLN ⁻¹'
      InterpolationMatrix.goodSet s a.succPNat d η =
    {u | WithLp.ofLp u.val ∈ goodBlockEvent s.val a.succPNat (a+1+d).succPNat η} := rfl

/-- See Appendix C in the paper: exact weighted exceptional integral
on the chart and on the physical ambient law. No integrability premise is
needed for these nonnegative extended integrals. -/
theorem weighted_tail_eq (s : Riesz1.RieszExponent) (a d : ℕ)
    (L η : ℝ) (hLN : L < ((a+1+d : ℕ)+1 : ℝ))
    (ρ : Measure (AffineSimplex.massSimplex a L)) :
    (∫⁻ x in (InterpolationMatrix.goodSet s a.succPNat d η)ᶜ,
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight s.val
        (n := a.succPNat) (WithLp.ofLp x.val))
      ∂ρ.map (inclusion a L ((a+1+d : ℕ)+1) hLN)) =
    ∫⁻ u in {u : EuclideanSpace ℝ (Fin (a+1)) |
      WithLp.ofLp u ∉ goodBlockEvent s.val a.succPNat (a+1+d).succPNat η},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight s.val
        (n := a.succPNat) (WithLp.ofLp u)) ∂ρ.map Subtype.val := by
  let i := inclusion a L ((a+1+d : ℕ)+1) hLN
  have hi := measurableEmbedding_inclusion a L ((a+1+d : ℕ)+1) hLN
  have hv := MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex a L)
  rw [hi.restrict_map, hi.lintegral_map, hv.restrict_map, hv.lintegral_map]
  rfl

/-- See Subsection 6.1 of the paper, reusable for Lemma 6.4: any actual weighted
tail estimate on the physical law gives the identical chart estimate. -/
theorem weighted_tail_le_internal (s : Riesz1.RieszExponent) (a d : ℕ)
    (L η : ℝ) (hLN : L < ((a+1+d : ℕ)+1 : ℝ))
    (ρ : Measure (AffineSimplex.massSimplex a L)) (R : ℝ≥0∞)
    (h : (∫⁻ u in {u : EuclideanSpace ℝ (Fin (a+1)) |
      WithLp.ofLp u ∉ goodBlockEvent s.val a.succPNat (a+1+d).succPNat η},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight s.val
        (n := a.succPNat) (WithLp.ofLp u)) ∂ρ.map Subtype.val) ≤ R) :
    (∫⁻ x in (InterpolationMatrix.goodSet s a.succPNat d η)ᶜ,
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight s.val
        (n := a.succPNat) (WithLp.ofLp x.val))
      ∂ρ.map (inclusion a L ((a+1+d : ℕ)+1) hLN)) ≤ R := by
  rw [weighted_tail_eq]
  exact h

/-- See Subsection 6.1 of the paper: normalization and inclusion commute literally.
This applies to the physical interpolant weight without any replacement
density or second normalizer. -/
theorem normalized_law (a : ℕ) (L N : ℝ) (hLN : L < N)
    (w : AffineSimplex.massSimplex a L → ℝ≥0∞)
    (h0 : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
    (ht : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤) :
    ((AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0 ht).map
        (inclusion a L N hLN)).map Subtype.val =
    (AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0 ht).map Subtype.val :=
  map_inclusion_val a L N hLN _

/-- See Subsection 6.1 and Lemma 6.4 of the paper: source and test L² classes
transport isometrically, and every extended Lᵖ norm, including the essential
supremum, is preserved. -/
theorem scalar_classes (a : ℕ) (L N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L)) :
    ∃ T : Lp ℝ 2 (ρ.map (inclusion a L N hLN)) ≃ₗᵢ[ℝ] Lp ℝ 2 ρ,
      (∀ u, T u =ᵐ[ρ] u ∘ inclusion a L N hLN) ∧
      ∀ u p, eLpNorm (T.symm u) p (ρ.map (inclusion a L N hLN)) = eLpNorm u p ρ :=
  ⟨ScalarFormEmbedding.pullback ρ _ (measurableEmbedding_inclusion a L N hLN),
    ScalarFormEmbedding.pullback_ae ρ _ _, ScalarFormEmbedding.inverse_eLpNorm ρ _ _⟩

/-- See Subsection 6.1 and Lemma 6.4 of the paper: the entire intrinsic form,
its closed Dirichlet property and conservativity transport to the pushed
law. The complete domain and every mixed energy pairing are preserved. -/
theorem scalar_form (a : ℕ) (L N : ℝ) (hLN : L < N)
    (ρ : Measure (AffineSimplex.massSimplex a L))
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (hQc : IsConservativeScalarForm Q) :
    let i := inclusion a L N hLN
    let hi := measurableEmbedding_inclusion a L N hLN
    let Q' := ScalarFormEmbedding.form ρ i hi Q
    IsClosedScalarDirichletForm Q' ∧ IsConservativeScalarForm Q' ∧
      ∃ D : Q'.1 ≃ₗ[ℝ] Q.1,
        (∀ u v, Q'.2 u v = Q.2 (D u) (D v)) ∧
        ∀ u, ‖u.val‖ = ‖(D u).val‖ := by
  intro i hi Q'
  refine ⟨ScalarFormEmbedding.closed_dirichlet ρ i hi Q hQ,
    ScalarFormEmbedding.conservative ρ i hi Q hQc,
    ScalarFormEmbedding.domainEquiv ρ i hi Q,
    ScalarFormEmbedding.energy ρ i hi Q, ?_⟩
  intro u
  exact (ScalarFormEmbedding.pullback ρ i hi).norm_map u.val |>.symm

/-- See Subsection 6.1 of the paper: an ambient fixed-exterior realization retains
the physical active Hessian block after inclusion. The differentiability
premise is on the full ambient realization at the assembled point, rather
than an identity only on the mass hyperplane. -/
theorem ambient_hessian_on_fibre (a e : ℕ) (L N : ℝ) (hLN : L < N)
    (y : EuclideanSpace ℝ (Fin e))
    (W : EuclideanSpace ℝ (Fin (e+a+1)) → ℝ)
    (u : AffineSimplex.massSimplex a L)
    (hW : ContDiffAt ℝ ∞ W (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u.val)) (i j : Fin (a+1)) :
    hessianMatrix (fun v => W (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y v)) (inclusion a L N hLN u).val i j =
    fderiv ℝ (fderiv ℝ W) (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u.val)
      (EuclideanSpace.single (i.castLE (show a+1 ≤ e+a+1 by omega)) 1)
      (EuclideanSpace.single (j.castLE (show a+1 ≤ e+a+1 by omega)) 1) :=
  InterpolationExceptional.hessian_assembly_internal e a y W u.val hW i j

/-- See Subsection 6.1 of the paper: the transported forcing is the ambient Hessian
of the exact two-sided penalty, with both singleton summands retained. -/
theorem forcing_on_fibre (a : ℕ) (L N : ℝ) (hLN : L < N)
    (θ : PhysicalCutoff) (ε : ℝ) (u : AffineSimplex.massSimplex a L) :
    InterpolationMatrix.penaltyHessian a.succPNat θ ε (inclusion a L N hLN u).val =
      hessianMatrix (fun x : EuclideanSpace ℝ (Fin (a+1)) =>
        ∑ i, (θ.val ((a+1 : ℝ)^(-ε)*x i) + θ.val ((a+1 : ℝ)^(-ε)*(x i)⁻¹))) u.val := by
  simp only [InterpolationMatrix.penaltyHessian, inclusion, Nat.succPNat_coe,
    Nat.cast_succ]

/-- See Subsection 6.1 of the paper: equality on an open ambient neighborhood
transports the entire physical Hessian block, including its normal part. -/
theorem hessian_realization_on_fibre {a : ℕ} {L N : ℝ} (hLN : L < N)
    {V W : EuclideanSpace ℝ (Fin (a+1)) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin (a+1)))} (hU : IsOpen U)
    (he : EqOn V W U) (u : AffineSimplex.massSimplex a L) (hu : u.val ∈ U) :
    hessianMatrix V (inclusion a L N hLN u).val = hessianMatrix W u.val :=
  InterpolationExceptional.hessian_eqOn_internal hU he hu

/-- See Subsection 6.1 of the paper: the positive part of an orthonormal intrinsic
chart maps to the same larger active chart as the mass-fibre inclusion. -/
def orthonormalInclusion (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) →
      AffineSimplex.chartDomain (a+1) N := by
  intro w
  have hw : AffineSimplex.centredChart a L (e.symm w.val) ∈ AffineSimplex.massSimplex a L := by
    obtain ⟨x, hx, he⟩ := w.property
    rw [← he, e.symm_apply_apply]
    exact hx
  exact inclusion a L N hLN ⟨_, hw⟩

/-- See Subsection 6.1 of the paper: the orthonormal chart inclusion is a measurable
embedding, so every L² source and every scalar form transports through it. -/
theorem measurableEmbedding_orthonormalInclusion (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    MeasurableEmbedding (orthonormalInclusion a L N hLN e) := by
  have hU : IsOpen (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) :=
    e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  have hchart := ((AffineSimplex.isometry_centredChart a L).comp e.symm.isometry).isClosedEmbedding.measurableEmbedding
  have h := ScalarFormEmbedding.codRestrict_embedding
    (hchart.comp (MeasurableEmbedding.subtype_coe hU.measurableSet))
    (AffineSimplex.chartDomain (a+1) N)
    (fun w => (orthonormalInclusion a L N hLN e w).property)
  exact h

/-- See Subsection 6.1 of the paper: inclusion and forgetting the intrinsic domain
give exactly the physical orthonormal pushforward, for every supported law. -/
theorem orthonormal_law (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V) :
    let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let ξ : Measure U := ν.comap Subtype.val
    ξ.map Subtype.val = ν ∧
      (ξ.map (orthonormalInclusion a L N hLN e)).map Subtype.val =
        ν.map (fun w => AffineSimplex.centredChart a L (e.symm w)) := by
  intro U ξ
  have hU : IsOpen (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) :=
    e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  have hsupport := IntrinsicScalarCore.supported hU hV
  have hξ : ξ.map Subtype.val = ν := by
    exact (map_comap_subtype_coe hU.measurableSet ν).trans
      (Measure.restrict_eq_self_of_ae_mem hsupport)
  refine ⟨hξ, ?_⟩
  rw [Measure.map_map measurable_subtype_coe
    (measurableEmbedding_orthonormalInclusion a L N hLN e).measurable]
  change ξ.map ((fun w => AffineSimplex.centredChart a L (e.symm w)) ∘ Subtype.val) = _
  have hg : Measurable (fun w => AffineSimplex.centredChart a L (e.symm w)) :=
    (AffineSimplex.isometry_centredChart a L).continuous.measurable.comp e.symm.continuous.measurable
  exact (Measure.map_map hg measurable_subtype_coe).symm.trans
    (congrArg (Measure.map (fun w => AffineSimplex.centredChart a L (e.symm w))) hξ)

/-- See Subsection 6.1 and Lemma 6.4 of the paper: construct the scalar form on
the included intrinsic law from its actual Gibbs realization in an
orthonormal chart. The original Neumann realization is retained on that
chart, and the full closed conservative form is transported to the larger
carrier. -/
theorem intrinsic_scalar_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V) :
    let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let ξ : Measure U := ν.comap Subtype.val
    let j := orthonormalInclusion a L N hLN e
    ξ.map Subtype.val = ν ∧
    ∃ Q₀ : ScalarFormData (ξ.map Subtype.val),
      IsNeumannRealization U Q₀ ∧ IsClosedScalarDirichletForm Q₀ ∧ IsConservativeScalarForm Q₀ ∧
    ∃ Q : ScalarFormData (ξ.map j),
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
    ∃ D : Q.1 ≃ₗ[ℝ] Q₀.1,
      (∀ u v, Q.2 u v = Q₀.2 (D u) (D v)) ∧
      (∀ u, ‖u.val‖ = ‖(D u).val‖) ∧
      ∃ T : Lp ℝ 2 (ξ.map j) ≃ₗᵢ[ℝ] Lp ℝ 2 (ξ.map Subtype.val),
        (∀ u p, eLpNorm (T u) p (ξ.map Subtype.val) = eLpNorm u p (ξ.map j)) ∧
        ∀ u : Q.1, (D u).val = T u.val := by
  intro U ξ j
  have hU : IsOpen (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) :=
    e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  have hB := e.isometry.lipschitzWith.isBounded_image (ConditionalWellPosedness.fibre_isBounded a L)
  have hv := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hj := measurableEmbedding_orthonormalInclusion a L N hLN e
  have hξ := (orthonormal_law a L N hLN e ν V hV).1
  have hforms : ∃ Q₀ : ScalarFormData (ξ.map Subtype.val),
      IsNeumannRealization U Q₀ ∧ IsClosedScalarDirichletForm Q₀ ∧ IsConservativeScalarForm Q₀ := by
    rw [hξ]
    exact ⟨IntrinsicScalarCore.form hU hB hV, IntrinsicScalarCore.realization hU hB hV,
      IntrinsicScalarCore.closed_dirichlet hU hB hV, IntrinsicScalarCore.conservative hU hB hV⟩
  obtain ⟨Q₀, hreal, hQ₀, hc₀⟩ := hforms
  let Qξ := ScalarFormEmbedding.restriction ξ Subtype.val hv Q₀
  have hQξ := ScalarFormEmbedding.restriction_closed_dirichlet ξ Subtype.val hv Q₀ hQ₀
  have hcξ := ScalarFormEmbedding.restriction_conservative ξ Subtype.val hv Q₀ hc₀
  let Q := ScalarFormEmbedding.form ξ j hj Qξ
  let D := (ScalarFormEmbedding.domainEquiv ξ j hj Qξ).trans
    (ScalarFormEmbedding.restrictionEquiv ξ Subtype.val hv Q₀)
  refine ⟨hξ, Q₀, hreal, hQ₀, hc₀, Q,
    ScalarFormEmbedding.closed_dirichlet ξ j hj Qξ hQξ,
    ScalarFormEmbedding.conservative ξ j hj Qξ hcξ, D, ?_, ?_, ?_⟩
  · intro u v; rfl
  · intro u
    have h1 := (ScalarFormEmbedding.pullback ξ j hj).norm_map u.val
    have h2 := (ScalarFormEmbedding.pullback ξ Subtype.val hv).symm.norm_map
      (ScalarFormEmbedding.pullback ξ j hj u.val)
    exact (h2.trans h1).symm
  · let T := (ScalarFormEmbedding.pullback ξ j hj).trans
      (ScalarFormEmbedding.pullback ξ Subtype.val hv).symm
    refine ⟨T, ?_, fun _ => rfl⟩
    intro u p
    exact (ScalarFormEmbedding.inverse_eLpNorm ξ Subtype.val hv
      (ScalarFormEmbedding.pullback ξ j hj u) p).trans
        (ScalarFormEmbedding.pullback_eLpNorm ξ j hj u p)

/-- See Subsection 6.1 of the paper: expose the exact transported form used in the
intrinsic construction, so the full resolvent transport can be applied to
that same form by definition, without choosing another realization. -/
theorem intrinsic_scalar_explicit_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V) :
    let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let hU : IsOpen U := e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let ξ : Measure U := ν.comap Subtype.val
    let j := orthonormalInclusion a L N hLN e
    let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
    let hj := measurableEmbedding_orthonormalInclusion a L N hLN e
    ∃ Q₀ : ScalarFormData (ξ.map Subtype.val),
      IsNeumannRealization U Q₀ ∧ IsClosedScalarDirichletForm Q₀ ∧ IsConservativeScalarForm Q₀ ∧
      let Qξ := ScalarFormEmbedding.restriction ξ Subtype.val hv Q₀
      let Q := ScalarFormEmbedding.form ξ j hj Qξ
      IsClosedScalarDirichletForm Qξ ∧ IsConservativeScalarForm Qξ ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  intro U hU ξ j hv hj
  obtain ⟨_, Q₀, hreal, hQ₀, hc₀, _⟩ := intrinsic_scalar_internal a L N hLN e ν V hV
  refine ⟨Q₀, hreal, hQ₀, hc₀, ?_⟩
  intro Qξ Q
  have hQξ := ScalarFormEmbedding.restriction_closed_dirichlet ξ Subtype.val hv Q₀ hQ₀
  have hcξ := ScalarFormEmbedding.restriction_conservative ξ Subtype.val hv Q₀ hc₀
  exact ⟨hQξ, hcξ, ScalarFormEmbedding.closed_dirichlet ξ j hj Qξ hQξ,
    ScalarFormEmbedding.conservative ξ j hj Qξ hcξ⟩

/-- See Subsection 6.1 and Lemma 6.4 of the paper:
identify the law of the transported intrinsic form with the actual
normalized Hausdorff law. The density is specified only on its physical
mass fibre. Its normalizer is proved positive and finite. -/
theorem normalized_intrinsic_law_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (w : AffineSimplex.massSimplex a L → ℝ≥0∞) (hw : Measurable w)
    (he : ∀ x ∈ e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      ∀ hx : AffineSimplex.centredChart a L (e.symm x) ∈ AffineSimplex.massSimplex a L,
        w ⟨AffineSimplex.centredChart a L (e.symm x), hx⟩ = ENNReal.ofReal (Real.exp (-V x))) :
    let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let ξ : Measure U := ν.comap Subtype.val
    ∃ h0 ht, ξ.map (orthonormalInclusion a L N hLN e) =
      (AffineFibre.normalizedMeasure ((AffineSimplex.simplexVolume a L).comap Subtype.val)
        w h0 ht).map (inclusion a L N hLN) := by
  intro U ξ
  let S := AffineSimplex.massSimplex a L
  let σ := AffineSimplex.simplexVolume a L
  let μ : Measure S := σ.comap Subtype.val
  have hv := MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex a L)
  obtain ⟨w', hw', hext⟩ := hv.exists_measurable_extend hw (fun _ => inferInstance)
  have hvol : μ.map Subtype.val = σ := by
    rw [map_comap_subtype_coe (RetainedSimplex.measurableSet_simplex a L)]
    dsimp only [σ]
    rw [AffineSimplex.simplexVolume_eq_restrict,
      Measure.restrict_restrict (RetainedSimplex.measurableSet_simplex a L), inter_self]
  obtain ⟨h0', ht', hν⟩ := AuxiliaryMean.simplex_density_internal a L e ν V hV w' hw' (by
    intro x hx
    have hxs : AffineSimplex.centredChart a L (e.symm x) ∈ S := by
      obtain ⟨y, hy, rfl⟩ := hx
      change AffineSimplex.centredChart a L (e.symm (e y)) ∈ AffineSimplex.massSimplex a L
      rw [e.symm_apply_apply]
      exact hy
    exact (congrFun hext ⟨_, hxs⟩).trans (he x hx hxs))
  have hl : (∫⁻ x, w' x ∂σ) = ∫⁻ u, w u ∂μ := by
    rw [← hvol, hv.lintegral_map]
    exact lintegral_congr (fun u => congrFun hext u)
  have h0 : (∫⁻ u, w u ∂μ) ≠ 0 := hl ▸ h0'
  have ht : (∫⁻ u, w u ∂μ) ≠ ⊤ := hl ▸ ht'
  have hext' : (fun u : S => w' u.val) = w := hext
  have hm := AffineFibre.normalizedMeasure_map μ hv hw'
    (show (∫⁻ u, w' u.val ∂μ) ≠ 0 by simpa only [hext'] using h0)
    (show (∫⁻ u, w' u.val ∂μ) ≠ ⊤ by simpa only [hext'] using ht)
  have hmap : AffineFibre.normalizedMeasure σ w' h0' ht' =
      (AffineFibre.normalizedMeasure μ w h0 ht).map Subtype.val := by
    simp only [AffineFibre.normalizedMeasure_eq_smul] at hm ⊢
    rw [hvol] at hm
    simpa only [hext'] using hm
  refine ⟨h0, ht, ?_⟩
  apply (MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain (a+1) N).measurableSet).map_injective
  exact (orthonormal_law a L N hLN e ν V hV).2.trans
    (hν.trans hmap) |>.trans (map_inclusion_val a L N hLN _).symm

/-- See Subsection 6.1 and Lemma 6.4 of the paper: the normalized Hausdorff
interpolant itself carries the transported intrinsic closed conservative
form. The complete class and energy equivalences are supplied by
`intrinsic_scalar_internal`, before the law equality is substituted. -/
theorem normalized_intrinsic_scalar_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (w : AffineSimplex.massSimplex a L → ℝ≥0∞) (hw : Measurable w)
    (he : ∀ x ∈ e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      ∀ hx : AffineSimplex.centredChart a L (e.symm x) ∈ AffineSimplex.massSimplex a L,
        w ⟨AffineSimplex.centredChart a L (e.symm x), hx⟩ = ENNReal.ofReal (Real.exp (-V x))) :
    ∃ (h0 : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
      (ht : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤),
    let ρ := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0 ht
    ∃ Q : ScalarFormData (ρ.map (inclusion a L N hLN)),
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  have hlaw0 := normalized_intrinsic_law_internal a L N hLN e ν V hV w hw he
  rcases hlaw0 with ⟨h0, ht, hlaw⟩
  let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
  let ξ : Measure U := ν.comap Subtype.val
  have hscalar : ∃ Q : ScalarFormData (ξ.map (orthonormalInclusion a L N hLN e)),
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
    obtain ⟨_, Q₀, _, _, _, Q, hQ, hc, _⟩ := intrinsic_scalar_internal a L N hLN e ν V hV
    exact ⟨Q, hQ, hc⟩
  rw [hlaw] at hscalar
  exact ⟨h0, ht, hscalar⟩

/-- See Subsection 6.1 and Lemma 6.4 of the paper: all scalar classes on the
normalized Hausdorff law are isometrically identified with the original
orthonormal Gibbs chart, preserving every extended essential norm. -/
theorem normalized_scalar_classes_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (w : AffineSimplex.massSimplex a L → ℝ≥0∞) (hw : Measurable w)
    (he : ∀ x ∈ e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      ∀ hx : AffineSimplex.centredChart a L (e.symm x) ∈ AffineSimplex.massSimplex a L,
        w ⟨AffineSimplex.centredChart a L (e.symm x), hx⟩ = ENNReal.ofReal (Real.exp (-V x))) :
    ∃ (h0 : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
      (ht : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤),
    let ρ := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0 ht
    ∃ T : Lp ℝ 2 (ρ.map (inclusion a L N hLN)) ≃ₗᵢ[ℝ] Lp ℝ 2 ν,
      ∀ u p, eLpNorm (T u) p ν = eLpNorm u p (ρ.map (inclusion a L N hLN)) := by
  have hnorm := normalized_intrinsic_law_internal a L N hLN e ν V hV w hw he
  rcases hnorm with ⟨h0, ht, hlaw⟩
  let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
  let ξ : Measure U := ν.comap Subtype.val
  let j := orthonormalInclusion a L N hLN e
  have hU : IsOpen U := e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  have hv := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hj := measurableEmbedding_orthonormalInclusion a L N hLN e
  have hclasses : ∃ T : Lp ℝ 2 (ξ.map j) ≃ₗᵢ[ℝ] Lp ℝ 2 (ξ.map Subtype.val),
      ∀ u p, eLpNorm (T u) p (ξ.map Subtype.val) = eLpNorm u p (ξ.map j) := by
    refine ⟨(ScalarFormEmbedding.pullback ξ j hj).trans
      (ScalarFormEmbedding.pullback ξ Subtype.val hv).symm, ?_⟩
    intro u p
    exact (ScalarFormEmbedding.inverse_eLpNorm ξ Subtype.val hv
      (ScalarFormEmbedding.pullback ξ j hj u) p).trans
        (ScalarFormEmbedding.pullback_eLpNorm ξ j hj u p)
  have hξ := (orthonormal_law a L N hLN e ν V hV).1
  rw [hξ, hlaw] at hclasses
  exact ⟨h0, ht, hclasses⟩

/-- See Subsection 6.1 of the paper: the full intrinsic volume change of variables
in an arbitrary orthonormal frame, before any density is normalized. -/
theorem orthonormal_simplexVolume (a : ℕ) (L : ℝ)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    (volume.restrict U).map (fun x => AffineSimplex.centredChart a L (e.symm x)) =
      AffineSimplex.simplexVolume a L := by
  intro U
  let g := fun x => AffineSimplex.centredChart a L (e.symm x)
  have hg : MeasurableEmbedding g :=
    ((AffineSimplex.isometry_centredChart a L).comp e.symm.isometry).isClosedEmbedding.measurableEmbedding
  have hpre : g ⁻¹' AffineSimplex.massSimplex a L = U := by
    ext x
    constructor
    · intro hx; exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change AffineSimplex.centredChart a L (e.symm (e y)) ∈ AffineSimplex.massSimplex a L
      rw [e.symm_apply_apply]
      exact hy
  have hm : (volume : Measure (EuclideanSpace ℝ (Fin a))).map g =
      AffineSimplex.hyperplaneVolume a L := by
    change volume.map (AffineSimplex.centredChart a L ∘ e.symm) = _
    rw [← Measure.map_map (AffineSimplex.isometry_centredChart a L).continuous.measurable
      e.symm.continuous.measurable, e.symm.measurePreserving.map_eq,
      AffineSimplex.map_volume_centredChart]
  rw [← hpre, ← hg.restrict_map, hm, ← AffineSimplex.simplexVolume_eq_restrict]

/-- See Subsection 6.1 and Lemma 6.4 of the paper: a smooth physical potential
and the given positive finite Hausdorff normalizer construct the intrinsic
Gibbs realization and its closed scalar form on the included law. A Gibbs
law is constructed here, rather than required as an extra input. -/
theorem scalar_of_smooth_density_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : ContDiffOn ℝ ∞ V
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)))
    (w : AffineSimplex.massSimplex a L → ℝ≥0∞) (hw : Measurable w)
    (he : ∀ x ∈ e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      ∀ hx : AffineSimplex.centredChart a L (e.symm x) ∈ AffineSimplex.massSimplex a L,
        w ⟨AffineSimplex.centredChart a L (e.symm x), hx⟩ = ENNReal.ofReal (Real.exp (-V x)))
    (h0 : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
    (ht : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤) :
    let ρ := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume a L).comap Subtype.val) w h0 ht
    let U := e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    ∃ ν : Measure (EuclideanSpace ℝ (Fin a)),
      IsEuclideanGibbsPotential volume ν U V ∧
      (ν.comap (Subtype.val : U → _)).map (orthonormalInclusion a L N hLN e) =
        ρ.map (inclusion a L N hLN) ∧
      ∃ Q : ScalarFormData (ρ.map (inclusion a L N hLN)),
        IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  intro ρ U
  let S := AffineSimplex.massSimplex a L
  let σ := AffineSimplex.simplexVolume a L
  let μ : Measure S := σ.comap Subtype.val
  let g := fun x => AffineSimplex.centredChart a L (e.symm x)
  have hU : IsOpen U := e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  have hg : MeasurableEmbedding g :=
    ((AffineSimplex.isometry_centredChart a L).comp e.symm.isometry).isClosedEmbedding.measurableEmbedding
  have hv := MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex a L)
  obtain ⟨w', hw', hext⟩ := hv.exists_measurable_extend hw (fun _ => inferInstance)
  have hvol : μ.map Subtype.val = σ := by
    rw [map_comap_subtype_coe (RetainedSimplex.measurableSet_simplex a L)]
    dsimp only [σ]
    rw [AffineSimplex.simplexVolume_eq_restrict,
      Measure.restrict_restrict (RetainedSimplex.measurableSet_simplex a L), inter_self]
  have he' : ∀ x ∈ U, w' (g x) = ENNReal.ofReal (Real.exp (-V x)) := by
    intro x hx
    have hxs : g x ∈ S := by
      obtain ⟨y, hy, rfl⟩ := hx
      change AffineSimplex.centredChart a L (e.symm (e y)) ∈ AffineSimplex.massSimplex a L
      rw [e.symm_apply_apply]
      exact hy
    exact (congrFun hext ⟨_, hxs⟩).trans (he x hx hxs)
  have hZ : (∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂volume.restrict U) = ∫⁻ u, w u ∂μ := by
    calc
      _ = ∫⁻ x, w' (g x) ∂volume.restrict U :=
        lintegral_congr_ae ((ae_restrict_mem hU.measurableSet).mono (fun x hx => (he' x hx).symm))
      _ = ∫⁻ x, w' x ∂σ := by
        exact (hg.lintegral_map (μ := volume.restrict U) (f := w')).symm.trans
          (congrArg (fun m => ∫⁻ x, w' x ∂m) (orthonormal_simplexVolume a L e))
      _ = ∫⁻ u, w u ∂μ := by
        rw [← hvol, hv.lintegral_map]
        exact lintegral_congr (fun u => congrFun hext u)
  have hZ0 : (∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂volume.restrict U) ≠ 0 := hZ.symm ▸ h0
  have hZt : (∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂volume.restrict U) ≠ ⊤ := hZ.symm ▸ ht
  let ν := AffineFibre.normalizedMeasure (volume.restrict U)
    (fun x => ENNReal.ofReal (Real.exp (-V x))) hZ0 hZt
  have hG : IsEuclideanGibbsPotential volume ν U V := by
    refine ⟨hV, bot_lt_iff_ne_bot.mpr hZ0, lt_top_iff_ne_top.mpr hZt, ?_⟩
    exact AffineFibre.normalizedMeasure_eq_smul _ _ _ _
  obtain ⟨_, _, hlaw⟩ := normalized_intrinsic_law_internal a L N hLN e ν V hG w hw he
  obtain ⟨_, _, Q, hQ, hc⟩ := normalized_intrinsic_scalar_internal a L N hLN e ν V hG w hw he
  exact ⟨ν, hG, hlaw, Q, hQ, hc⟩

/-- See Subsection 6.1 and Lemma 6.4 of the paper: the actual
fixed-exterior interpolant has an intrinsic closed conservative scalar
form on the included chart. The law is the literal normalized Hausdorff
law used by `local_laws`. The ambient endpoint realizations agree on
their full open domains. No Gibbs-form or coefficient premise is added.
This construction holds at every compatible positive size. -/
theorem physical_scalar_transport (p : Parameters) (a d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (θ : PhysicalCutoff) (ε L : ℝ)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (hcompatY : (∑ i, y.val i)+L = ((d+a : ℕ)+1 : ℝ))
    (hcompatZ : (∑ i, z.val i)+L = ((e+a : ℕ)+1 : ℝ)) :
    let hLN := compatible_mass_lt a d hd L y hcompatY
    let Y := RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val
    let Z := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (d+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (e+a).succPNat
    let S := AffineSimplex.massSimplex a L
    let μ : Measure S := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let Ey := fun u : S => physicalAmbientGapEnergy p (d+a).succPNat
      ⟨Y u.val, ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d a y u.val
        (by have hr : ((d+a : ℕ)+1 : ℝ)-∑ i, y.val i = L := by linarith
            rw [hr]; exact u.property))⟩
    let Ez := fun u : S => physicalAmbientGapEnergy p (e+a).succPNat
      ⟨Z u.val, ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e a z u.val
        (by have hr : ((e+a : ℕ)+1 : ℝ)-∑ i, z.val i = L := by linarith
            rw [hr]; exact u.property))⟩
    let P := fun x : EuclideanSpace ℝ (Fin (a+1)) => ∑ i,
      (θ.val (((a+1 : ℕ) : ℝ)^(-ε)*x i) + θ.val (((a+1 : ℕ) : ℝ)^(-ε)*(x i)⁻¹))
    ∃ Ay Az : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ay Dy ∧ ContDiffOn ℝ ∞ Az Dz ∧
      (∀ u (hu : u ∈ Dy), Ay u = physicalAmbientGapEnergy p (d+a).succPNat ⟨Y u, hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Az u = physicalAmbientGapEnergy p (e+a).succPNat ⟨Z u, hu⟩) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
      let w := fun u : S => ENNReal.ofReal (Real.exp (-p.val.1*(P u.val+(1-t)*Ey u+t*Ez u)))
      ∃ h0 ht,
      let ρ := AffineFibre.normalizedMeasure μ w h0 ht
      ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
      let U := frame '' (AffineSimplex.centredChart a L ⁻¹' S)
      let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
      let V := fun x => p.val.1*(P (g x)+(1-t)*Ay (g x)+t*Az (g x))
      ∃ ν : Measure (EuclideanSpace ℝ (Fin a)),
        IsEuclideanGibbsPotential volume ν U V ∧
        (ν.comap (Subtype.val : U → _)).map (orthonormalInclusion a L ((d+a : ℕ)+1) hLN frame) =
          ρ.map (inclusion a L ((d+a : ℕ)+1) hLN) ∧
        ∃ Q : ScalarFormData (ρ.map (inclusion a L ((d+a : ℕ)+1) hLN)),
          IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  intro hLN Y Z Dy Dz S μ Ey Ez P
  obtain ⟨Wy, hWy, hwy, _⟩ := PhysicalEnergy.ambient_derivatives p (d+a).succPNat
  obtain ⟨Wz, hWz, hwz, _⟩ := PhysicalEnergy.ambient_derivatives p (e+a).succPNat
  let Ay := fun u => Wy (Y u)
  let Az := fun u => Wz (Z u)
  have hAy : ContDiffOn ℝ ∞ Ay Dy := hWy.comp
    (InterpolantLocalLaws.contDiff_exterior_assembly d a y.val).contDiffOn (fun _ h => h)
  have hAz : ContDiffOn ℝ ∞ Az Dz := hWz.comp
    (InterpolantLocalLaws.contDiff_exterior_assembly e a z.val).contDiffOn (fun _ h => h)
  have hY (u : S) : u.val ∈ Dy := ProperMarginalChart.simplex_ambient _
    (InterpolatingDensities.assemble_exterior_mem d a y u.val (by
      have hr : ((d+a : ℕ)+1 : ℝ)-∑ i, y.val i = L := by linarith
      rw [hr]; exact u.property))
  have hZ (u : S) : u.val ∈ Dz := ProperMarginalChart.simplex_ambient _
    (InterpolatingDensities.assemble_exterior_mem e a z u.val (by
      have hr : ((e+a : ℕ)+1 : ℝ)-∑ i, z.val i = L := by linarith
      rw [hr]; exact u.property))
  have hAyval (u : S) : Ay u.val = Ey u := hwy ⟨Y u.val, hY u⟩
  have hAzval (u : S) : Az u.val = Ez u := hwz ⟨Z u.val, hZ u⟩
  obtain ⟨hP, hEy, h0y, hty, _⟩ := physical_endpoint_on_simplex p d a hd θ ε L y hcompatY
  obtain ⟨_, hEz, _h0z, htz, _⟩ := physical_endpoint_on_simplex p e a he θ ε L z hcompatZ
  refine ⟨Ay, Az, hAy, hAz, fun u hu => hwy ⟨Y u, hu⟩,
    fun u hu => hwz ⟨Z u, hu⟩, ?_⟩
  intro t ht w
  obtain ⟨h0, htop⟩ := Internal.gibbs_interpolation_normalizer μ (P ∘ Subtype.val) Ey Ez
    hP hEy hEz p.val.1 ht.1 ht.2 h0y hty htz
  refine ⟨h0, htop, ?_⟩
  intro ρ frame U g V
  have hwm : Measurable w :=
    (((hP.add (hEy.const_mul (1-t))).add (hEz.const_mul t)).const_mul (-p.val.1)).exp.ennreal_ofReal
  have hDy : IsOpen Dy := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (RetainedSimplex.continuous_assemble d a _ y.val)
  have hDz : IsOpen Dz := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (RetainedSimplex.continuous_assemble e a _ z.val)
  have hg : ContDiff ℝ ∞ g := by
    dsimp only [g, AffineSimplex.centredChart]
    exact (((AffineSimplex.Tangent a).subtypeL.contDiff).comp
      frame.symm.toContinuousLinearEquiv.contDiff).add contDiff_const
  have hgs (x : EuclideanSpace ℝ (Fin a)) (hx : x ∈ U) : g x ∈ S := by
    obtain ⟨v, hv, rfl⟩ := hx
    change AffineSimplex.centredChart a L (frame.symm (frame v)) ∈ S
    rw [frame.symm_apply_apply]; exact hv
  have hV : ContDiffOn ℝ ∞ V U := by
    intro x hx
    have hxs := hgs x hx
    have hxp : g x ∈ AffineSimplex.chartDomain (a+1) (L+1) :=
      ⟨hxs.1, hxs.2.trans_lt (by linarith)⟩
    have hpen := (MarginalCollision.active_penalty_smooth_convex (a+1) (L+1) θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (a+1 : ℕ)) (-ε)) Finset.univ true).1.contDiffAt
        ((AffineSimplex.isOpen_chartDomain (a+1) (L+1)).mem_nhds hxp)
    have hPa : ContDiffAt ℝ ∞ P (g x) := by
      simpa only [P, ite_true] using hpen
    exact (((hPa.comp x hg.contDiffAt).add
      (((hAy.contDiffAt (hDy.mem_nhds (hY ⟨g x, hxs⟩))).comp x hg.contDiffAt).const_smul (1-t))).add
        (((hAz.contDiffAt (hDz.mem_nhds (hZ ⟨g x, hxs⟩))).comp x hg.contDiffAt).const_smul t)).const_smul
          p.val.1 |>.contDiffWithinAt
  apply scalar_of_smooth_density_internal a L _ hLN frame V hV w hwm ?_ h0 htop
  intro x hx hxs
  have hy := hAyval ⟨g x, hxs⟩
  have hz := hAzval ⟨g x, hxs⟩
  simp only [w, V]
  rw [hy, hz]
  congr 2
  dsimp only [g]
  ring

/-- See Subsection 6.1 of the paper: the actual ambient fixed-exterior
interaction realizes the same square bound on the included chart law.
The open-neighborhood realization identities and both endpoint Hessians
are retained. The carrier inequality follows from `compatible_mass_lt`. -/
theorem physical_interaction_on_chart_internal (s ε : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ (n₀ : ℕ) (C : ℝ), 2 ≤ n₀ ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → ∀ (e f a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 → 4 * (a + 1) ≤ f + a + 1 →
      ∀ (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
        (z : AffineSimplex.chartDomain f ((f + a : ℕ) + 1)),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s ε f a z.val →
      ∀ L : ℝ,
      ((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k = L →
      ((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k = L →
      let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
      let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
      let Dy := Y ⁻¹' gapAmbientDomain (e + a).succPNat
      let Dz := Z ⁻¹' gapAmbientDomain (f + a).succPNat
      ∃ Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
        ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
        (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y u, hu⟩) ∧
        (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy p (f + a).succPNat ⟨Z u, hu⟩) ∧
        ∀ hLN : L < ((e+a : ℕ)+1 : ℝ),
        ∀ ρ : Measure (AffineSimplex.massSimplex a L),
        ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ᵐ x ∂ρ.map (inclusion a L ((e+a : ℕ)+1) hLN),
        ∀ i j : Fin (a + 1),
          |(1 - t) * hessianMatrix Ky x.val i j + t * hessianMatrix Kz x.val i j| ^ 2 ≤
            C * (a + 1 : ℝ) ^ C *
              InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp x.val) := by
  obtain ⟨n₀, C, hn₀, hC, hbound⟩ :=
    InterpolationExceptional.physical_interaction_sq_internal s ε hs hε hσε
  refine ⟨n₀, C, hn₀, hC, ?_⟩
  intro p hps e f a hn hNy hNz y z hgy hgz L hyL hzL Y Z Dy Dz
  obtain ⟨Ky, Kz, hKy, hKz, hky, hkz, hsq⟩ :=
    hbound p hps e f a hn hNy hNz y z hgy hgz L hyL hzL
  refine ⟨Ky, Kz, hKy, hKz, hky, hkz, ?_⟩
  intro hLN ρ t ht
  rw [(measurableEmbedding_inclusion a L _ hLN).ae_map_iff]
  exact ae_of_all _ (fun u => hsq t ht u.val u.property)

/-- See Appendix C in the paper, used by Subsection 6.1 and
Lemma 6.4: the actual normalized Hausdorff interpolant satisfies all
three local laws on the included chart, with its original constants,
normalizer, fine event and exceptional weight. The tail power is still
chosen before the temperature interval. -/
theorem local_laws_on_chart (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
        1 ≤ m → 4 * (m + 1) ≤ d + m + 1 → d ≤ e →
        ((m + 1 : ℕ) : ℝ) ^ (2 / s) ≤ ((d + m : ℕ) + 1 : ℝ) →
        let R := ENNReal.ofReal (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ δ))
        (physicalExteriorLaw p d m θ ε) {y | ¬admissibleExterior p d m hd θ ε A K y} ≤ R ∧
        ∀ L : ℝ,
        ∀ y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1),
        ∀ z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1),
        ∀ hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ),
        ∀ hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ),
        admissibleExterior p d m hd θ ε A K y →
        admissibleExterior p e m he θ ε A K z →
            let hLN := compatible_mass_lt m d hd L y hcompatY
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
                (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht).map (inclusion m L ((d+m : ℕ)+1) hLN)
              IsProbabilityMeasure ν ∧
              (∫⁻ u in {u : AffineSimplex.chartDomain (m+1) ((d+m : ℕ)+1) |
                  WithLp.ofLp u.val ∉ goodBlockEvent s m.succPNat (d + m).succPNat (K * ε)},
                ENNReal.ofReal (exceptionalWeight s (n := m.succPNat) (WithLp.ofLp u.val)) ∂ν) ≤ R ∧
              (∀ i : Fin (m + 1),
                1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u.val i ∧
                  u.val i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
              ∀ a b : ℕ, a < b → b ≤ m + 1 →
                ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s 1 / 2) <
                  |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u.val i) -
                    (b - a : ℕ)|} ≤ R := by
  obtain ⟨A, K, ε₀, hA, hK, hε₀, hlocal⟩ := InterpolantLocalLaws.local_laws hRig s hs hs1
  refine ⟨A, K, ε₀, hA, hK, hε₀, ?_⟩
  intro ε hε hε₀'
  obtain ⟨δ, hδ, hlocal⟩ := hlocal ε hε hε₀'
  refine ⟨δ, hδ, ?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C, c, hC, hc, hlocal⟩ := hlocal βlo βhi hlo hle θ
  refine ⟨C, c, hC, hc, ?_⟩
  intro p hps hpl hph d e m hd he hm hsize hde hpower R
  obtain ⟨houter, hlocal⟩ := hlocal p hps hpl hph d e m hd he hm hsize hde hpower
  refine ⟨houter, ?_⟩
  intro L y z hcompatY hcompatZ hy hz hLN S Ky Kz μ P t ht0 ht1
  obtain ⟨h0, ht, hprob, hbad, hcoords, hblocks⟩ :=
    hlocal L y z hcompatY hcompatZ hy hz t ht0 ht1
  let ρ := AffineFibre.normalizedMeasure μ (fun u : S => ENNReal.ofReal
    (Real.exp (-p.val.1 * (P u + (1-t)*Ky u + t*Kz u)))) h0 ht
  have hρ : IsProbabilityMeasure ρ := by
    have : IsProbabilityMeasure (ρ.map Subtype.val) := hprob
    exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable
  have := hρ
  refine ⟨h0, ht, probability m L _ hLN ρ, ?_, ?_, ?_⟩
  · exact (lintegral_inclusion m L _ hLN ρ
      {u | WithLp.ofLp u ∉ goodBlockEvent s m.succPNat (d+m).succPNat (K*ε)}
      (fun u => ENNReal.ofReal (exceptionalWeight s (n := m.succPNat) (WithLp.ofLp u)))).trans_le hbad
  · intro i
    exact hcoords i |>.trans_eq (map_inclusion_apply m L _ hLN ρ
      {u | ((m+1 : ℕ) : ℝ)^(-(K*ε)) ≤ u i ∧ u i ≤ ((m+1 : ℕ) : ℝ)^(K*ε)}).symm
  · intro a b hab hbm
    exact (map_inclusion_apply m L _ hLN ρ
      {u | ((m+1 : ℕ) : ℝ)^(K*ε) * (b-a : ℕ)^(min s 1 / 2) <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (m+1) => a ≤ i.val ∧ i.val < b), u i) -
          (b-a : ℕ)|}).trans_le (hblocks a b hab hbm)

section Exterior

variable {α γ : Type} [MeasurableSpace α] [MeasurableSpace γ]
  (μ : Measure α) (f : α → γ) (hf : MeasurableEmbedding f)
  (Q : ScalarFormData μ) (hQ : IsClosedScalarDirichletForm Q)

local notation "Q'" => ScalarFormEmbedding.form μ f hf Q
local notation "hQ'" => ScalarFormEmbedding.closed_dirichlet μ f hf Q hQ

/-- See Subsection 6.1 of the paper: transport of all exterior L² sources, with
the component set independent of the scalar fibre dimension. -/
def sourceEquiv (ι : Type) [Fintype ι] :
    PiLp 2 (fun _ : ι => Lp ℝ 2 (μ.map f)) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : ι => Lp ℝ 2 μ) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => ScalarFormEmbedding.pullback μ f hf)

/-- See Subsection 6.1 of the paper: transport of the complete exterior form domain. -/
def vectorEquiv (ι : Type) [Fintype ι] [DecidableEq ι] :
    MatrixEnergy.Vector (ι := ι) Q' hQ' ≃ₗᵢ[ℝ] MatrixEnergy.Vector (ι := ι) Q hQ :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => ScalarFormEmbedding.domainIsometry μ f hf Q hQ)

/-- See Subsection 6.1 of the paper: scalar values commute with exterior transport. -/
theorem vectorValues_transport (ι : Type) [Fintype ι] [DecidableEq ι]
    (u : MatrixEnergy.Vector (ι := ι) Q' hQ') :
    sourceEquiv μ f hf ι (OperatorSchur.vectorValues Q' hQ' u) =
      OperatorSchur.vectorValues Q hQ (vectorEquiv μ f hf Q hQ ι u) := rfl

/-- See Subsection 6.1 of the paper: all mixed intrinsic diffusion pairings are
preserved on the full exterior domain. -/
theorem vectorEnergy_transport (ι : Type) [Fintype ι] [DecidableEq ι]
    (u v : MatrixEnergy.Vector (ι := ι) Q' hQ') :
    OperatorSchur.vectorEnergy Q' hQ' u v = OperatorSchur.vectorEnergy Q hQ
      (vectorEquiv μ f hf Q hQ ι u) (vectorEquiv μ f hf Q hQ ι v) := by
  rw [OperatorSchur.vectorEnergy_apply, OperatorSchur.vectorEnergy_apply]
  rfl

/-- See Subsection 6.1 and Lemma 6.4 of the paper: arbitrary physical matrix
pairings commute with L² transport almost everywhere, including unbounded
multiplication coefficients. -/
theorem matrixFieldPair_transport_ae (ι : Type) [Fintype ι]
    (P : γ → Matrix ι ι ℝ) (u v : ι → Lp ℝ 2 (μ.map f)) :
    (matrixFieldPair P u v) ∘ f =ᵐ[μ]
      matrixFieldPair (P ∘ f) (fun i => ScalarFormEmbedding.pullback μ f hf (u i))
        (fun i => ScalarFormEmbedding.pullback μ f hf (v i)) := by
  have hu := ae_all_iff.mpr (fun i : ι => ScalarFormEmbedding.pullback_ae μ f hf (u i))
  have hv := ae_all_iff.mpr (fun i : ι => ScalarFormEmbedding.pullback_ae μ f hf (v i))
  filter_upwards [hu, hv] with x hx hy
  simp only [matrixFieldPair, Function.comp_apply, hx, hy]

/-- See Subsection 6.1 and Lemma 6.4 of the paper: the actual cross-integrability
domain is preserved under carrier transport. -/
theorem matrixFieldPair_integrable_iff (ι : Type) [Fintype ι]
    (P : γ → Matrix ι ι ℝ) (u v : ι → Lp ℝ 2 (μ.map f)) :
    Integrable (matrixFieldPair P u v) (μ.map f) ↔
      Integrable (matrixFieldPair (P ∘ f) (fun i => ScalarFormEmbedding.pullback μ f hf (u i))
        (fun i => ScalarFormEmbedding.pullback μ f hf (v i))) μ := by
  rw [hf.integrable_map_iff]
  exact integrable_congr (matrixFieldPair_transport_ae μ f hf ι P u v)

/-- See Subsection 6.1 and Lemma 6.4 of the paper: the signed multiplication
integral is preserved on its true integrability domain. -/
theorem matrixFieldPair_integral (ι : Type) [Fintype ι]
    (P : γ → Matrix ι ι ℝ) (u v : ι → Lp ℝ 2 (μ.map f)) :
    (∫ y, matrixFieldPair P u v y ∂μ.map f) =
      ∫ x, matrixFieldPair (P ∘ f) (fun i => ScalarFormEmbedding.pullback μ f hf (u i))
        (fun i => ScalarFormEmbedding.pullback μ f hf (v i)) x ∂μ := by
  rw [hf.integral_map]
  exact integral_congr_ae (matrixFieldPair_transport_ae μ f hf ι P u v)

/-- See Subsection 6.1 of the paper: constant exterior matrix energy transports
without an integrability assumption or a bounded extension of a physical
multiplication operator. -/
theorem constant_pair_transport (ι : Type) [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ)
    (u v : PiLp 2 (fun _ : ι => Lp ℝ 2 (μ.map f))) :
    (∫ y, matrixFieldPair (fun _ => D) u.ofLp v.ofLp y ∂μ.map f) =
    ∫ x, matrixFieldPair (fun _ => D) (sourceEquiv μ f hf ι u).ofLp
      (sourceEquiv μ f hf ι v).ofLp x ∂μ := by
  rw [hf.integral_map]
  apply integral_congr_ae
  have hu := ae_all_iff.mpr (fun i : ι => ScalarFormEmbedding.pullback_ae μ f hf (u i))
  have hv := ae_all_iff.mpr (fun i : ι => ScalarFormEmbedding.pullback_ae μ f hf (v i))
  filter_upwards [hu, hv] with x hx hy
  simp only [matrixFieldPair, sourceEquiv, LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply, Function.comp_apply, hx, hy]

variable (s : Riesz1.RieszExponent) (β : InverseTemperature)
  (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ)/4) (n : ℕ)

/-- See Subsection 6.1 of the paper: the whole exterior weak form, including its
matrix part and its intrinsic diffusion, transports exactly. -/
theorem exteriorForm_transport
    (u v : MatrixEnergy.Vector (ι := InterpolationMatrix.exteriorIndices M n) Q' hQ') :
    InterpolationMatrix.referenceExteriorForm (μ.map f) Q' hQ' s β M hM K hK hKM n u v =
      InterpolationMatrix.referenceExteriorForm μ Q hQ s β M hM K hK hKM n
        (vectorEquiv μ f hf Q hQ _ u) (vectorEquiv μ f hf Q hQ _ v) := by
  unfold InterpolationMatrix.referenceExteriorForm
  rw [BoundarySchurBounds.constantForm_apply, BoundarySchurBounds.constantForm_apply,
    vectorEnergy_transport μ f hf Q hQ,
    constant_pair_transport μ f hf]
  rw [vectorValues_transport, vectorValues_transport]

/-- See Subsection 6.1 of the paper: uniqueness identifies the transported full
resolvent, on every exterior L² source, with the defined resolvent. -/
theorem referenceResolvent_transport :
    InterpolationMatrix.referenceResolvent (μ.map f) Q' hQ' s β M hM K hK hKM n =
      (vectorEquiv μ f hf Q hQ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((InterpolationMatrix.referenceResolvent μ Q hQ s β M hM K hK hKM n).comp
          (sourceEquiv μ f hf _).toContinuousLinearEquiv.toContinuousLinearMap) := by
  symm
  apply InterpolationMatrix.referenceResolvent_unique
  intro g w
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [exteriorForm_transport μ f hf Q hQ, LinearIsometryEquiv.apply_symm_apply,
    InterpolationMatrix.referenceResolvent_solves]
  rw [← vectorValues_transport μ f hf Q hQ]
  exact (sourceEquiv μ f hf _).inner_map_map _ _

/-- See Subsection 6.1 of the paper: tensorization preserves the reference column,
and hence also an input-column difference with its original sign. -/
theorem tensor_transport (ι : Type) [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (u : Lp ℝ 2 (μ.map f)) :
    sourceEquiv μ f hf ι (BoundarySchurBounds.tensor v u) =
      BoundarySchurBounds.tensor v (ScalarFormEmbedding.pullback μ f hf u) := by
  apply PiLp.ext
  intro i
  exact map_smul (ScalarFormEmbedding.pullback μ f hf) (v i) u

/-- See Subsection 6.1 of the paper: the Schur pairing on arbitrary sources
transports with the exact beta squared normalization. -/
theorem resolvent_pair_transport
    (u v : PiLp 2 (fun _ : InterpolationMatrix.exteriorIndices M n => Lp ℝ 2 (μ.map f))) :
    β.val^2 * inner ℝ u (OperatorSchur.vectorValues Q' hQ'
      (InterpolationMatrix.referenceResolvent (μ.map f) Q' hQ' s β M hM K hK hKM n v)) =
    β.val^2 * inner ℝ (sourceEquiv μ f hf _ u) (OperatorSchur.vectorValues Q hQ
      (InterpolationMatrix.referenceResolvent μ Q hQ s β M hM K hK hKM n
        (sourceEquiv μ f hf _ v))) := by
  rw [referenceResolvent_transport μ f hf Q hQ]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [← (sourceEquiv μ f hf _).inner_map_map,
    vectorValues_transport μ f hf Q hQ, LinearIsometryEquiv.apply_symm_apply]

/-- See Subsection 6.1 of the paper: exact transport of the point Schur pairing. -/
theorem schurPointPair_transport (φ η : Lp ℝ 2 (μ.map f)) (j i : Fin (M : ℕ)) :
    InterpolationMatrix.schurPointPair (μ.map f) Q' hQ' s β M hM K hK hKM n φ η j i =
      InterpolationMatrix.schurPointPair μ Q hQ s β M hM K hK hKM n
        (ScalarFormEmbedding.pullback μ f hf φ) (ScalarFormEmbedding.pullback μ f hf η) j i := by
  unfold InterpolationMatrix.schurPointPair
  rw [resolvent_pair_transport μ f hf Q hQ, tensor_transport, tensor_transport]

/-- See Subsection 6.1 of the paper: exact transport of the signed input-column
increment, with no absolute values inserted before the resolvent. -/
theorem schurIncrementPair_transport (φ η : Lp ℝ 2 (μ.map f)) (j i l : Fin (M : ℕ)) :
    InterpolationMatrix.schurIncrementPair (μ.map f) Q' hQ' s β M hM K hK hKM n φ η j i l =
      InterpolationMatrix.schurIncrementPair μ Q hQ s β M hM K hK hKM n
        (ScalarFormEmbedding.pullback μ f hf φ) (ScalarFormEmbedding.pullback μ f hf η) j i l := by
  unfold InterpolationMatrix.schurIncrementPair
  rw [resolvent_pair_transport μ f hf Q hQ, tensor_transport, tensor_transport]

end Exterior

end Riesz2.InterpolationTransport
