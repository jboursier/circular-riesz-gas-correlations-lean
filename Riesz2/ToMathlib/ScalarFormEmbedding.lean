/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MatrixEnergySpaces
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Riesz2.Frozen.IsConservativeScalarForm

/-!
# Scalar forms under measurable embeddings

Pullback is a surjective L² isometry for an embedding and its image law.
The transported domain and energy are the original scalar form in these
L² coordinates. This also applies to laws supported on a lower dimensional
affine fibre. It does not assert an ambient Neumann gradient realization.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.ScalarFormEmbedding

/-- Restricting the codomain of a measurable embedding to a set containing
its whole image preserves the embedding. -/
theorem codRestrict_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (S : Set β) (hS : ∀ x, f x ∈ S) :
    MeasurableEmbedding (Set.codRestrict f S hS) := by
  refine ⟨fun u v h => hf.injective (congrArg Subtype.val h), hf.measurable.subtype_mk, ?_⟩
  intro E hE
  have he : Set.codRestrict f S hS '' E = (Subtype.val : S → β) ⁻¹' (f '' E) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, he⟩; exact ⟨u, hu, Subtype.ext he⟩
  rw [he]
  exact (hf.measurableSet_image.mpr hE).preimage measurable_subtype_coe

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) (f : α → β) (hf : MeasurableEmbedding f)

/-- Pullback along an embedding is onto L² of the original law. -/
theorem pullback_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℝ f (⟨hf.measurable, rfl⟩ :
      MeasurePreserving f μ (μ.map f)) : Lp ℝ 2 (μ.map f) →ₗᵢ[ℝ] Lp ℝ 2 μ) := by
  intro u
  obtain ⟨v, _hv, he⟩ := hf.exists_measurable_extend (Lp.stronglyMeasurable u).measurable
    (fun _ => inferInstance : β → Nonempty ℝ)
  have hv : MemLp v 2 (μ.map f) := hf.memLp_map_measure_iff.mpr (he.symm ▸ Lp.memLp u)
  refine ⟨hv.toLp v, Lp.ext ?_⟩
  have hp : MeasurePreserving f μ (μ.map f) := ⟨hf.measurable, rfl⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving (hv.toLp v) hp,
    hp.quasiMeasurePreserving.ae hv.coeFn_toLp] with x hx hy
  exact hx.trans (hy.trans (congrFun he x))

/-- The canonical L² equivalence is pullback. Its inverse is uniquely
determined as an L² class, regardless of representatives off the image. -/
def pullback : Lp ℝ 2 (μ.map f) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℝ f (⟨hf.measurable, rfl⟩ :
      MeasurePreserving f μ (μ.map f))) (pullback_surjective μ f hf)

/-- Pullback has the actual composed scalar representative. -/
theorem pullback_ae (u : Lp ℝ 2 (μ.map f)) :
    pullback μ f hf u =ᵐ[μ] u ∘ f :=
  Lp.coeFn_compMeasurePreserving u ⟨hf.measurable, rfl⟩

/-- The inverse equivalence recovers the original scalar on the image. -/
theorem inverse_ae (u : Lp ℝ 2 μ) :
    ((pullback μ f hf).symm u : β → ℝ) ∘ f =ᵐ[μ] u := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (pullback_ae μ f hf ((pullback μ f hf).symm u)).symm

/-- Essential Lᵖ norms of transported classes, including p = infinity,
agree exactly. No finite real essential supremum is totalized. -/
theorem inverse_eLpNorm (u : Lp ℝ 2 μ) (p : ℝ≥0∞) :
    eLpNorm ((pullback μ f hf).symm u) p (μ.map f) = eLpNorm u p μ := by
  rw [hf.eLpNorm_map_measure]
  exact eLpNorm_congr_ae (inverse_ae μ f hf u)

/-- Pullback preserves every extended essential Lᵖ norm, including
essential boundedness of an L² class. -/
theorem pullback_eLpNorm (u : Lp ℝ 2 (μ.map f)) (p : ℝ≥0∞) :
    eLpNorm (pullback μ f hf u) p μ = eLpNorm u p (μ.map f) := by
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    (inverse_eLpNorm μ f hf (pullback μ f hf u) p).symm

variable (Q : ScalarFormData μ)

/-- The transported scalar domain is the exact inverse image under L²
pullback, with the original bilinear energy. -/
def form : ScalarFormData (μ.map f) :=
  let D := Q.1.comap (pullback μ f hf).toLinearEquiv.toLinearMap
  let T : D →ₗ[ℝ] Q.1 :=
    { toFun := fun u => ⟨pullback μ f hf u.val, u.property⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  ⟨D, (Q.2.compl₂ T).comp T⟩

/-- The full transported domain is linearly equivalent to the original. -/
def domainEquiv : (form μ f hf Q).1 ≃ₗ[ℝ] Q.1 where
  toFun u := ⟨pullback μ f hf u.val, u.property⟩
  invFun u := ⟨(pullback μ f hf).symm u.val, by
    change pullback μ f hf ((pullback μ f hf).symm u.val) ∈ Q.1
    simpa only [LinearIsometryEquiv.apply_symm_apply] using u.property⟩
  left_inv _ := Subtype.ext ((pullback μ f hf).symm_apply_apply _)
  right_inv _ := Subtype.ext ((pullback μ f hf).apply_symm_apply _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Both mixed energy pairings are preserved on the complete domain. -/
theorem energy (u v : (form μ f hf Q).1) :
    (form μ f hf Q).2 u v = Q.2 (domainEquiv μ f hf Q u) (domainEquiv μ f hf Q v) := rfl

/-- Closedness, density and the Markov contraction property survive the
embedding, even when its image has empty ambient interior. -/
theorem closed_dirichlet (hQ : IsClosedScalarDirichletForm Q) :
    IsClosedScalarDirichletForm (form μ f hf Q) := by
  let T := pullback μ f hf
  let D := domainEquiv μ f hf Q
  refine ⟨?_, fun u v => hQ.2.1 (D u) (D v),
    fun u => hQ.2.2.1 (D u), ?_, ?_⟩
  · have hd := hQ.1
    rw [denseRange_iff_closure_range] at hd ⊢
    have he : Set.range (fun u : (form μ f hf Q).1 => u.val) =
        T.symm '' Set.range (fun u : Q.1 => u.val) := by
      ext u
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨(D u).val, ⟨D u, rfl⟩, T.symm_apply_apply u.val⟩
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
        exact ⟨D.symm u, rfl⟩
    rw [he]
    change closure (T.symm.toHomeomorph '' Set.range (fun u : Q.1 => u.val)) = _
    rw [← T.symm.toHomeomorph.image_closure, hd]
    exact Set.image_univ.trans T.symm.surjective.range_eq
  · intro u v huv hc
    obtain ⟨g, hgv, hg⟩ := hQ.2.2.2.1 (fun k => D (u k)) (T v)
      (T.continuous.tendsto v |>.comp huv) (by
        intro ε hε
        obtain ⟨k, hk⟩ := hc ε hε
        refine ⟨k, fun i j hi hj => ?_⟩
        have hn : ‖(D (u i)).val - (D (u j)).val‖ = ‖(u i).val - (u j).val‖ :=
          (T.map_sub (u i).val (u j).val).symm ▸ T.norm_map _
        rw [hn, ← map_sub D]
        exact hk i j hi hj)
    refine ⟨D.symm g, ?_, ?_⟩
    · apply T.injective
      exact (T.apply_symm_apply g.val).trans hgv
    · change Tendsto (fun k => Q.2 (D (u k - D.symm g)) (D (u k - D.symm g))) _ _
      simpa only [map_sub, D.apply_symm_apply] using hg
  · intro φ hφ hφ0 u
    obtain ⟨g, hg, he⟩ := hQ.2.2.2.2 φ hφ hφ0 (D u)
    refine ⟨D.symm g, ?_, ?_⟩
    · rw [hf.ae_map_iff]
      filter_upwards [inverse_ae μ f hf g.val, pullback_ae μ f hf u.val, hg] with x hx hy hz
      exact hx.trans (hz.trans (congrArg φ hy))
    · change Q.2 (D (D.symm g)) (D (D.symm g)) ≤ Q.2 (D u) (D u)
      simpa only [D.apply_symm_apply] using he

/-- Conservativity transports with the constant-one L² class. -/
theorem conservative (hQ : IsConservativeScalarForm Q) :
    IsConservativeScalarForm (form μ f hf Q) := by
  obtain ⟨u, hu, he⟩ := hQ
  refine ⟨(domainEquiv μ f hf Q).symm u, ?_, ?_⟩
  · rw [hf.ae_map_iff]
    exact (inverse_ae μ f hf u.val).trans hu
  · rw [energy, LinearEquiv.apply_symm_apply]
    exact he

/-- The complete scalar form Hilbert spaces are isometric, for the norm
consisting of scalar mass plus intrinsic energy. -/
def domainIsometry (hQ : IsClosedScalarDirichletForm Q) :
    ScalarFormHilbert.Space (form μ f hf Q) (closed_dirichlet μ f hf Q hQ) ≃ₗᵢ[ℝ]
      ScalarFormHilbert.Space Q hQ where
  toLinearEquiv := domainEquiv μ f hf Q
  norm_map' u := by
    let v : ScalarFormHilbert.Space Q hQ :=
      (ScalarFormHilbert.equiv Q hQ).symm (domainEquiv μ f hf Q u)
    change ‖v‖ = ‖u‖
    have h1 := ScalarFormHilbert.norm_sq (form μ f hf Q)
      (closed_dirichlet μ f hf Q hQ) u
    have h2 := ScalarFormHilbert.norm_sq Q hQ v
    have hn : ‖(domainEquiv μ f hf Q u).val‖ = ‖u.val‖ :=
      (pullback μ f hf).norm_map u.val
    change ‖u‖ ^ 2 = ‖u.val‖ ^ 2 +
      Q.2 (domainEquiv μ f hf Q u) (domainEquiv μ f hf Q u) at h1
    have hv : ScalarFormHilbert.equiv Q hQ v = domainEquiv μ f hf Q u := rfl
    rw [hv, hn] at h2
    nlinarith only [h1, h2, norm_nonneg u, norm_nonneg v]

section Restriction

variable (Q : ScalarFormData (μ.map f))

/-- Restriction of the scalar form to the original measured carrier,
the inverse direction of `form`. The energy and full domain are retained. -/
def restriction : ScalarFormData μ :=
  let D := Q.1.comap (pullback μ f hf).symm.toLinearEquiv.toLinearMap
  let T : D →ₗ[ℝ] Q.1 :=
    { toFun := fun u => ⟨(pullback μ f hf).symm u.val, u.property⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  ⟨D, (Q.2.compl₂ T).comp T⟩

/-- The full transported domain is linearly equivalent to the original. -/
def restrictionEquiv : (restriction μ f hf Q).1 ≃ₗ[ℝ] Q.1 where
  toFun u := ⟨(pullback μ f hf).symm u.val, u.property⟩
  invFun u := ⟨pullback μ f hf u.val, by
    change (pullback μ f hf).symm (pullback μ f hf u.val) ∈ Q.1
    simpa only [LinearIsometryEquiv.symm_apply_apply] using u.property⟩
  left_inv _ := Subtype.ext ((pullback μ f hf).apply_symm_apply _)
  right_inv _ := Subtype.ext ((pullback μ f hf).symm_apply_apply _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Both mixed energy pairings are preserved on the complete domain. -/
theorem restriction_energy (u v : (restriction μ f hf Q).1) :
    (restriction μ f hf Q).2 u v = Q.2 (restrictionEquiv μ f hf Q u) (restrictionEquiv μ f hf Q v) := rfl

/-- Closedness, density and the Markov contraction property survive the
embedding, even when its image has empty ambient interior. -/
theorem restriction_closed_dirichlet (hQ : IsClosedScalarDirichletForm Q) :
    IsClosedScalarDirichletForm (restriction μ f hf Q) := by
  let T := (pullback μ f hf).symm
  let D := restrictionEquiv μ f hf Q
  refine ⟨?_, fun u v => hQ.2.1 (D u) (D v),
    fun u => hQ.2.2.1 (D u), ?_, ?_⟩
  · have hd := hQ.1
    rw [denseRange_iff_closure_range] at hd ⊢
    have he : Set.range (fun u : (restriction μ f hf Q).1 => u.val) =
        T.symm '' Set.range (fun u : Q.1 => u.val) := by
      ext u
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨(D u).val, ⟨D u, rfl⟩, T.symm_apply_apply u.val⟩
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
        exact ⟨D.symm u, rfl⟩
    rw [he]
    change closure (T.symm.toHomeomorph '' Set.range (fun u : Q.1 => u.val)) = _
    rw [← T.symm.toHomeomorph.image_closure, hd]
    exact Set.image_univ.trans T.symm.surjective.range_eq
  · intro u v huv hc
    obtain ⟨g, hgv, hg⟩ := hQ.2.2.2.1 (fun k => D (u k)) (T v)
      (T.continuous.tendsto v |>.comp huv) (by
        intro ε hε
        obtain ⟨k, hk⟩ := hc ε hε
        refine ⟨k, fun i j hi hj => ?_⟩
        have hn : ‖(D (u i)).val - (D (u j)).val‖ = ‖(u i).val - (u j).val‖ :=
          (T.map_sub (u i).val (u j).val).symm ▸ T.norm_map _
        rw [hn, ← map_sub D]
        exact hk i j hi hj)
    refine ⟨D.symm g, ?_, ?_⟩
    · apply T.injective
      exact (T.apply_symm_apply g.val).trans hgv
    · change Tendsto (fun k => Q.2 (D (u k - D.symm g)) (D (u k - D.symm g))) _ _
      simpa only [map_sub, D.apply_symm_apply] using hg
  · intro φ hφ hφ0 u
    obtain ⟨g, hg, he⟩ := hQ.2.2.2.2 φ hφ hφ0 (D u)
    refine ⟨D.symm g, ?_, ?_⟩
    · have hg' := hf.ae_map_iff.mp hg
      filter_upwards [pullback_ae μ f hf g.val, inverse_ae μ f hf u.val, hg'] with x hx hy hz
      exact hx.trans (hz.trans (congrArg φ hy))
    · change Q.2 (D (D.symm g)) (D (D.symm g)) ≤ Q.2 (D u) (D u)
      simpa only [D.apply_symm_apply] using he

/-- Conservativity transports with the constant-one L² class. -/
theorem restriction_conservative (hQ : IsConservativeScalarForm Q) :
    IsConservativeScalarForm (restriction μ f hf Q) := by
  obtain ⟨u, hu, he⟩ := hQ
  refine ⟨(restrictionEquiv μ f hf Q).symm u, ?_, ?_⟩
  · exact (pullback_ae μ f hf u.val).trans (hf.ae_map_iff.mp hu)
  · rw [restriction_energy, LinearEquiv.apply_symm_apply]
    exact he

end Restriction

end Riesz2.ScalarFormEmbedding
