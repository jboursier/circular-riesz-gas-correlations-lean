/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineSimplexCharts
public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1Convolution

/-!
# Absolute continuity of proper simplex projections

The full length-simplex law is singular in ambient coordinates. Every proper
coordinate block has a Lebesgue density. This supplies the null-set transfer
needed for Lipschitz derivatives in the proof of Proposition 6.6.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.ProperSimplexProjection

/-- A surjective affine map sends an absolutely continuous finite-dimensional
law to an absolutely continuous law, including zero-dimensional targets. -/
theorem affine_absolutelyContinuous {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A : E →ₗ[ℝ] F) (hA : Function.Surjective A) (c : F)
    {μ : Measure E} (hμ : μ ≪ volume) :
    μ.map (fun x => A x + c) ≪ volume := by
  have hm : Measurable A := A.continuous_of_finiteDimensional.measurable
  obtain ⟨r, _, hr⟩ := A.exists_map_addHaar_eq_smul_addHaar
    (volume : Measure E) (volume : Measure F) hA
  have hlin : μ.map A ≪ volume := (hμ.map hm).trans (by
    rw [hr]
    exact Measure.smul_absolutelyContinuous)
  rw [show (fun x => A x + c) = (fun y => y + c) ∘ A from rfl,
    ← Measure.map_map (by fun_prop) hm]
  exact (hlin.map (by fun_prop)).trans
    (measurePreserving_add_right volume c).quasiMeasurePreserving.absolutelyContinuous

/-- See the proof of Proposition 6.6 in the paper: projection of the actual Euclidean
Hausdorff simplex measure onto any proper coordinate block has a density.
The omitted coordinate absorbs the mass constraint. No positivity condition
on the length is needed for this null-set statement. -/
theorem simplexVolume_absolutelyContinuous (n : ℕ) (L : ℝ)
    (J : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∉ J) :
    (AffineSimplex.simplexVolume n L).map
      (fun x => (WithLp.toLp 2 (fun i : J => x i.val) : EuclideanSpace ℝ J)) ≪ volume := by
  classical
  let A : AffineSimplex.Tangent n →ₗ[ℝ] EuclideanSpace ℝ J :=
    { toFun := fun z => WithLp.toLp 2 (fun i => z.val i.val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hA : Function.Surjective A := by
    intro v
    let w : Fin (n+1) → ℝ := fun i => if hi : i ∈ J then v ⟨i, hi⟩ else 0
    let z : EuclideanSpace ℝ (Fin (n+1)) :=
      WithLp.toLp 2 (Function.update w k (-∑ i ∈ Finset.univ.erase k, w i))
    have hz : z ∈ AffineSimplex.Tangent n := by
      rw [AffineSimplex.mem_hsOrthSubspace_iff]
      change (∑ i, Function.update w k (-∑ j ∈ Finset.univ.erase k, w j) i) = 0
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      simp only [Function.update_self]
      have he : (∑ i ∈ Finset.univ.erase k,
          Function.update w k (-∑ j ∈ Finset.univ.erase k, w j) i) =
          ∑ i ∈ Finset.univ.erase k, w i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
      rw [he, add_neg_cancel]
    refine ⟨⟨z,hz⟩, ?_⟩
    apply PiLp.ext
    intro i
    have hik : i.val ≠ k := by rintro rfl; exact hk i.property
    change Function.update w k _ i.val = v i
    rw [Function.update_of_ne hik]
    simp only [w, dite_eq_left i.property]
  rw [AffineSimplex.simplexVolume_eq_centredChart_map,
    Measure.map_map (by fun_prop) (AffineSimplex.isometry_centredChart n L).continuous.measurable]
  exact affine_absolutelyContinuous A hA
    (WithLp.toLp 2 (fun i : J => AffineSimplex.centre n L i.val)) Measure.restrict_le_self.absolutelyContinuous

/-- The same density conclusion holds for every law absolutely continuous
with respect to the Hausdorff simplex measure, as used in the proof of Proposition 6.6. -/
theorem law_absolutelyContinuous (n : ℕ) (L : ℝ)
    (J : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∉ J)
    {μ : Measure (EuclideanSpace ℝ (Fin (n+1)))}
    (hμ : μ ≪ AffineSimplex.simplexVolume n L) :
    μ.map (fun x => (WithLp.toLp 2 (fun i : J => x i.val) : EuclideanSpace ℝ J)) ≪ volume :=
  (hμ.map (by fun_prop)).trans (simplexVolume_absolutelyContinuous n L J k hk)

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the literal normalized
Hausdorff law on the positive mass-simplex subtype has absolutely continuous
proper coordinate marginals, for every normalizable density. This applies to
each physical interpolant, without any typicality assumption. -/
theorem normalized_law_absolutelyContinuous (n : ℕ) (L : ℝ)
    (J : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∉ J)
    (w : AffineSimplex.massSimplex n L → ℝ≥0∞)
    (h0 : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ 0)
    (ht : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ ⊤) :
    (AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume n L).comap Subtype.val) w h0 ht).map
        (fun x => (WithLp.toLp 2 (fun i : J => x.val i.val) : EuclideanSpace ℝ J)) ≪ volume := by
  let μ := (AffineSimplex.simplexVolume n L).comap
    (Subtype.val : AffineSimplex.massSimplex n L → EuclideanSpace ℝ (Fin (n+1)))
  have hmass : MeasurableSet (AffineSimplex.massSimplex n L) := by
    change MeasurableSet ({x : EuclideanSpace ℝ (Fin (n+1)) | ∀ i, 0 < x i} ∩ {x | ∑ i, x i = L})
    have hp : IsOpen {x : EuclideanSpace ℝ (Fin (n+1)) | ∀ i, 0 < x i} :=
      by
        simp only [ofPred_forall]
        exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
          (PiLp.continuous_apply 2 (fun _ : Fin (n+1) => ℝ) i)
    exact hp.measurableSet.inter (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have he := MeasurableEmbedding.subtype_coe hmass
  have hμ : μ.map Subtype.val ≪ AffineSimplex.simplexVolume n L := by
    rw [show μ = (AffineSimplex.simplexVolume n L).comap Subtype.val from rfl, he.map_comap]
    exact Measure.restrict_le_self.absolutelyContinuous
  have hnorm : AffineFibre.normalizedMeasure μ w h0 ht ≪ μ :=
    withDensity_absolutelyContinuous _ _
  rw [show (fun x : AffineSimplex.massSimplex n L =>
      (WithLp.toLp 2 (fun i : J => x.val i.val) : EuclideanSpace ℝ J)) =
      (fun x => (WithLp.toLp 2 (fun i : J => x i.val) : EuclideanSpace ℝ J)) ∘ Subtype.val from rfl,
    ← Measure.map_map (by fun_prop) measurable_subtype_coe]
  exact law_absolutelyContinuous n L J k hk ((hnorm.map measurable_subtype_coe).trans hμ)

/-- Almost-everywhere derivative certificates on a proper coordinate block
transfer to every absolutely continuous simplex law. In particular the
Rademacher null set is invisible on each fixed-length fibre. -/
theorem ae_on_law (n : ℕ) (L : ℝ)
    (J : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∉ J)
    {μ : Measure (EuclideanSpace ℝ (Fin (n+1)))}
    (hμ : μ ≪ AffineSimplex.simplexVolume n L) {P : EuclideanSpace ℝ J → Prop}
    (hP : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂μ, P (WithLp.toLp 2 (fun i : J => x i.val)) :=
  ae_of_ae_map (by fun_prop) ((law_absolutelyContinuous n L J k hk hμ).ae_le hP)

/-- See the proof of Proposition 6.6 in the paper: Rademacher derivatives on a proper
block exist almost everywhere under each normalized fixed-length law. -/
theorem normalized_ae_differentiable (n : ℕ) (L : ℝ)
    (J : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∉ J)
    (w : AffineSimplex.massSimplex n L → ℝ≥0∞)
    (h0 : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ 0)
    (ht : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ ⊤)
    {F : EuclideanSpace ℝ J → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) :
    ∀ᵐ x ∂AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume n L).comap Subtype.val) w h0 ht,
        DifferentiableAt ℝ F (WithLp.toLp 2 (fun i : J => x.val i.val)) := by
  exact ae_of_ae_map (by fun_prop)
    ((normalized_law_absolutelyContinuous n L J k hk w h0 ht).ae_le
      (hF.ae_differentiableAt (μ := volume)))

/-- See the proof of Proposition 6.6 in the paper: the library's smooth block
approximations have their derivative convergence on the actual normalized
Hausdorff law, not just on almost every unspecified fibre. The approximations
use only coordinates in `J`. This theorem does not assert preservation of a
restricted coordinate Lipschitz constant on a convex good set. -/
theorem normalized_smooth_approximation (n : ℕ) (L : ℝ)
    (J : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∉ J)
    (w : AffineSimplex.massSimplex n L → ℝ≥0∞)
    (h0 : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ 0)
    (ht : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ ⊤)
    {F : EuclideanSpace ℝ J → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) :
    ∃ φ : ℕ → EuclideanSpace ℝ J → ℝ,
      (∀ m, ContDiff ℝ ∞ (φ m)) ∧
      (∀ m x, ‖φ m x-F x‖ ≤ C) ∧
      (∀ m x, ‖gradient (φ m) x‖ ≤ C) ∧
      (∀ x, Filter.Tendsto (fun m => φ m x) Filter.atTop (nhds (F x))) ∧
      ∀ᵐ x ∂AffineFibre.normalizedMeasure
        ((AffineSimplex.simplexVolume n L).comap Subtype.val) w h0 ht,
        Filter.Tendsto (fun m => gradient (φ m)
          (WithLp.toLp 2 (fun i : J => x.val i.val))) Filter.atTop
            (nhds (gradient F (WithLp.toLp 2 (fun i : J => x.val i.val)))) := by
  obtain ⟨φ,hs,he,hb,hp,hd⟩ := Riesz1.WeightedSobolev.exists_smooth_approximation_lipschitz hF
  refine ⟨φ,hs,he,hb,hp,?_⟩
  exact ae_of_ae_map (by fun_prop)
    ((normalized_law_absolutelyContinuous n L J k hk w h0 ht).ae_le hd)

end Riesz2.ProperSimplexProjection
