/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.RadialDomainGaps
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-!
# Arbitrary-mass affine simplex charts

Infrastructure for Subsection 3.2 and the volume calculation in Subsection 1.7.
The parameter `n` counts free coordinates: the simplex has `n + 1` gaps. Its tangent
space is the existing `Riesz1.hsOrthSubspace`, exposed by the `Tangent` abbreviation.
Intrinsic volume means Mathlib's
normalized Euclidean Hausdorff measure, which agrees with Lebesgue measure in
orthonormal coordinates. The raw diameter-normalized Hausdorff measure is different.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace Riesz2
namespace AffineSimplex

/-- The library's zero-sum space, with the ambient dimension exposed for type inference. -/
abbrev Tangent (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  Riesz1.hsOrthSubspace ⟨n + 1, Nat.succ_pos n⟩

/-- The affine hyperplane of total mass `L` (Subsection 3.2). -/
def massHyperplane (n : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {y | ∑ i, y i = L}

/-- Positive gaps of arbitrary total mass (Subsection 3.2). -/
def massSimplex (n : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {y | (∀ i, 0 < y i) ∧ ∑ i, y i = L}

/-- The domain of the chart obtained by deleting the last coordinate. -/
def chartDomain (n : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < L}

/-- Recover the last coordinate from the total mass. Defined on the whole vector space. -/
def chart (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) (L - ∑ i, x i))

/-- Delete the last coordinate. -/
def coordinates (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => y i.castSucc)

theorem chart_castSucc (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    chart n L x i.castSucc = x i := by simp [chart]

theorem chart_last (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    chart n L x (Fin.last n) = L - ∑ i, x i := by simp [chart]

theorem sum_chart (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, chart n L x i = L := by
  rw [Fin.sum_univ_castSucc]
  simp only [chart_castSucc, chart_last]
  ring

theorem coordinates_chart (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinates n (chart n L x) = x := by ext i; exact chart_castSucc n L x i

theorem chart_coordinates (n : ℕ) (L : ℝ) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ massHyperplane n L) : chart n L (coordinates n y) = y := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hsum := hy
    change ∑ i, y i = L at hsum
    rw [Fin.sum_univ_castSucc] at hsum
    rw [chart_last]
    change L - ∑ j : Fin n, y j.castSucc = y (Fin.last n)
    linarith
  · exact chart_castSucc n L (coordinates n y) j

theorem range_chart (n : ℕ) (L : ℝ) : range (chart n L) = massHyperplane n L := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact sum_chart n L x
  · intro hy; exact ⟨coordinates n y, chart_coordinates n L hy⟩

theorem chart_injective (n : ℕ) (L : ℝ) : Function.Injective (chart n L) :=
  Function.LeftInverse.injective (coordinates_chart n L)

theorem chart_mem_simplex_iff (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    chart n L x ∈ massSimplex n L ↔ x ∈ chartDomain n L := by
  simp only [massSimplex, chartDomain, mem_ofPred_eq, sum_chart, and_true]
  constructor
  · intro h
    exact ⟨fun i => by simpa only [chart_castSucc] using h i.castSucc,
      sub_pos.mp (by simpa only [chart_last] using h (Fin.last n))⟩
  · rintro ⟨hpos, hsum⟩ i
    exact Fin.lastCases (by simpa only [chart_last] using sub_pos.mpr hsum)
      (fun j => by simpa only [chart_castSucc] using hpos j) i

theorem image_chart_domain (n : ℕ) (L : ℝ) :
    chart n L '' chartDomain n L = massSimplex n L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (chart_mem_simplex_iff n L x).mpr hx
  · intro hy
    have hinv := chart_coordinates n L hy.2
    refine ⟨coordinates n y, ?_, hinv⟩
    exact (chart_mem_simplex_iff n L _).mp (hinv.symm ▸ hy)

/-- At the physical mass this is the existing Riesz 1 simplex, in Euclidean coordinates. -/
theorem massSimplex_physical (n : ℕ) :
    massSimplex n (n + 1) = WithLp.ofLp ⁻¹' Riesz1.gapSimplex ⟨n + 1, Nat.succ_pos n⟩ := by
  ext y
  change ((∀ i, 0 < y i) ∧ ∑ i, y i = (n : ℝ) + 1) ↔
    ((∀ i, 0 < y i) ∧ ∑ i, y i = ((n + 1 : ℕ) : ℝ))
  rw [Nat.cast_add, Nat.cast_one]

/-- Linear tangent map for the chart: `(x₁,…,xₙ,-∑xᵢ)`. -/
def tangentMap (n : ℕ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1)) where
  toFun := chart n 0
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [chart_last, Finset.sum_add_distrib]
      ring
    · simp [chart_castSucc]
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [chart_last, Finset.mul_sum]
    · simp [chart_castSucc]

theorem chart_eq_tangentMap_add (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    chart n L x = tangentMap n x + chart n L 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [tangentMap, chart_last]
    ring
  · simp [tangentMap, chart_castSucc]

theorem continuous_chart (n : ℕ) (L : ℝ) : Continuous (chart n L) := by
  simpa only [← chart_eq_tangentMap_add] using
    (tangentMap n).continuous_of_finiteDimensional.add_const (chart n L 0)

theorem continuous_coordinates (n : ℕ) : Continuous (coordinates n) := by
  unfold coordinates
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => PiLp.continuous_apply 2 _ i.castSucc))

theorem isClosed_massHyperplane (n : ℕ) (L : ℝ) : IsClosed (massHyperplane n L) :=
  isClosed_eq (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i)) continuous_const

theorem isOpen_chartDomain (n : ℕ) (L : ℝ) : IsOpen (chartDomain n L) := by
  change IsOpen ({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < x i} ∩
    {x : EuclideanSpace ℝ (Fin n) | ∑ i, x i < L})
  apply IsOpen.inter
  · simpa only [ofPred_forall] using isOpen_iInter_of_finite
      (fun i : Fin n => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i))
  · exact isOpen_lt (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i))
      continuous_const

/-- The chart metric is `I + 𝟏𝟏ᵀ`, not the coordinate Euclidean metric. -/
theorem inner_tangentMap (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪tangentMap n x, tangentMap n y⟫ = ⟪x, y⟫ + (∑ i, x i) * (∑ i, y i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, tangentMap,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_castSucc,
    chart_castSucc, chart_last, zero_sub, neg_mul_neg]
  ring

/-- The exact norm formula includes the metric correction from the deleted coordinate. -/
theorem norm_tangentMap_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖tangentMap n x‖ ^ 2 = ‖x‖ ^ 2 + (∑ i, x i) ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, pow_two] using inner_tangentMap n x x

/-- The coordinate chart never contracts tangent lengths. -/
theorem norm_le_tangentMap (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ‖tangentMap n x‖ := by
  have h := norm_tangentMap_sq n x
  nlinarith [sq_nonneg (∑ i, x i), norm_nonneg x, norm_nonneg (tangentMap n x)]

/-- The chart's largest singular value is bounded by `√(n+1)`. -/
theorem norm_tangentMap_le (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖tangentMap n x‖ ≤ Real.sqrt (n + 1) * ‖x‖ := by
  have hsum := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => x i) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  rw [← EuclideanSpace.real_norm_sq_eq] at hsum
  have hroot : (Real.sqrt (n + 1)) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hmetric := norm_tangentMap_sq n x
  have hnonneg : 0 ≤ Real.sqrt (n + 1) * ‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (Real.sqrt (n + 1) * ‖x‖ - ‖tangentMap n x‖)]

/-- Chart differences are tangent vectors. The mass parameter disappears. -/
theorem chart_sub_chart (n : ℕ) (L : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    chart n L x - chart n L y = tangentMap n (x - y) := by
  rw [chart_eq_tangentMap_add n L x, chart_eq_tangentMap_add n L y, map_sub]
  abel

/-- Both singular-value bounds, in a form usable for boundary-distance comparison. -/
theorem dist_chart_bounds (n : ℕ) (L : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    dist x y ≤ dist (chart n L x) (chart n L y) ∧
      dist (chart n L x) (chart n L y) ≤ Real.sqrt (n + 1) * dist x y := by
  simp only [dist_eq_norm, chart_sub_chart]
  exact ⟨norm_le_tangentMap n _, norm_tangentMap_le n _⟩

/-- The same derivative works at every mass and every coordinate point. -/
theorem hasFDerivAt_chart (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (chart n L) (tangentMap n).toContinuousLinearMap x := by
  have h := ((tangentMap n).toContinuousLinearMap.hasFDerivAt (x := x)).add_const
    (chart n L 0)
  change HasFDerivAt (fun u => tangentMap n u + chart n L 0) _ x at h
  simpa only [← chart_eq_tangentMap_add] using h

/-- The ordinary chain rule with the actual intrinsic chart metric. -/
theorem hasFDerivAt_comp_chart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (L : ℝ) {f : EuclideanSpace ℝ (Fin (n + 1)) → F}
    {f' : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] F} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f f' (chart n L x)) :
    HasFDerivAt (fun u => f (chart n L u))
      (f'.comp (tangentMap n).toContinuousLinearMap) x :=
  hf.comp x (hasFDerivAt_chart n L x)

/-- The derivative takes values in the library's zero-sum tangent space. -/
theorem mem_hsOrthSubspace_iff (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    y ∈ Tangent n ↔ ∑ i, y i = 0 := by
  constructor
  · exact Riesz1.sum_coord_eq_zero_of_mem_orth (N := ⟨n + 1, Nat.succ_pos n⟩) y
  · intro hy
    apply (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))).mpr
    change inner ℝ ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ •
      (WithLp.toLp 2 (fun _ : Fin (n + 1) => (1 : ℝ)))) y = 0
    rw [inner_smul_left]
    simp [PiLp.inner_apply, hy]

/-- Coordinate linear equivalence onto the existing intrinsic tangent space. -/
def tangentEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
    Tangent n where
  toFun x := ⟨tangentMap n x, (mem_hsOrthSubspace_iff n _).mpr (sum_chart n 0 x)⟩
  invFun y := coordinates n y.val
  left_inv := coordinates_chart n 0
  right_inv y := Subtype.ext (chart_coordinates n 0
    ((mem_hsOrthSubspace_iff n y.val).mp y.property))
  map_add' x y := Subtype.ext ((tangentMap n).map_add x y)
  map_smul' c x := Subtype.ext ((tangentMap n).map_smul c x)

theorem finrank_tangent (n : ℕ) :
    Module.finrank ℝ (Tangent n) = n := by
  rw [← (tangentEquiv n).finrank_eq]
  simp

/-- The chart is a closed embedding of the entire coordinate space. -/
theorem isClosedEmbedding_chart (n : ℕ) (L : ℝ) :
    Topology.IsClosedEmbedding (chart n L) :=
  ⟨Function.LeftInverse.isEmbedding (coordinates_chart n L)
      (continuous_coordinates n) (continuous_chart n L),
    range_chart n L ▸ isClosed_massHyperplane n L⟩

/-- Gram matrix of the coordinate tangent vectors. -/
theorem gram_tangentMap (n : ℕ) :
    Matrix.gram ℝ (fun i => tangentMap n (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      1 + Matrix.replicateCol Unit (fun _ : Fin n => (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ)) := by
  classical
  ext i j
  rw [Matrix.gram_apply, inner_tangentMap]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    PiLp.single_apply, Matrix.mul_apply, Matrix.one_apply]

/-- The non-square Jacobian of the graph chart is exactly `√(n+1)`.
This is the area factor used in Subsection 1.7. -/
theorem normDet_tangentMap (n : ℕ) :
    (tangentMap n).normDet = Real.sqrt (n + 1) := by
  have hsquare := (tangentMap n).normDet_sq_eq_det_gram
    (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [gram_tangentMap, Matrix.det_one_add_replicateCol_mul_replicateRow] at hsquare
  simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsquare
  change (tangentMap n).normDet ^ 2 = 1 + (n : ℝ) at hsquare
  apply (sq_eq_sq₀ (LinearMap.normDet_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  linarith

/-- Intrinsic Euclidean volume on the whole mass hyperplane, as an ambient measure.
The normalization is the one in Subsection 3.2. -/
def hyperplaneVolume (n : ℕ) (L : ℝ) : Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  (Measure.euclideanHausdorffMeasure n).restrict (massHyperplane n L)

/-- Intrinsic volume on the relatively open simplex, as an ambient measure. -/
def simplexVolume (n : ℕ) (L : ℝ) : Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  (Measure.euclideanHausdorffMeasure n).restrict (massSimplex n L)

/-- Area formula for every coordinate set, including dimension zero. -/
theorem volume_chart_image (n : ℕ) (L : ℝ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    Measure.euclideanHausdorffMeasure n (chart n L '' s) =
      ENNReal.ofReal (Real.sqrt (n + 1)) * volume s := by
  have himage : chart n L '' s = (fun y => y + chart n L 0) '' (tangentMap n '' s) := by
    simp only [image_image, ← chart_eq_tangentMap_add]
  rw [himage, (isometry_add_right _).euclideanHausdorffMeasure_image]
  have h := (tangentMap n).euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
  simpa only [finrank_euclideanSpace, Fintype.card_fin, normDet_tangentMap] using h

/-- Constant-Jacobian change of variables on the entire affine hyperplane. -/
theorem hyperplaneVolume_eq (n : ℕ) (L : ℝ) :
    hyperplaneVolume n L = ENNReal.ofReal (Real.sqrt (n + 1)) •
      (volume : Measure (EuclideanSpace ℝ (Fin n))).map (chart n L) := by
  ext s hs
  rw [hyperplaneVolume, Measure.restrict_apply hs, Measure.smul_apply,
    Measure.map_apply (continuous_chart n L).measurable hs, smul_eq_mul]
  rw [← volume_chart_image n L (chart n L ⁻¹' s), image_preimage_eq_inter_range,
    range_chart]

/-- Restricting the full affine volume to positive gaps gives simplex volume. -/
theorem simplexVolume_eq_restrict (n : ℕ) (L : ℝ) :
    simplexVolume n L = (hyperplaneVolume n L).restrict (massSimplex n L) := by
  rw [hyperplaneVolume, Measure.restrict_restrict_of_subset]
  · rfl
  · exact fun _ hy => hy.2

/-- Constant-Jacobian change of variables on positive gaps. -/
theorem simplexVolume_eq (n : ℕ) (L : ℝ) :
    simplexVolume n L = ENNReal.ofReal (Real.sqrt (n + 1)) •
      (volume.restrict (chartDomain n L)).map (chart n L) := by
  rw [simplexVolume_eq_restrict, hyperplaneVolume_eq, Measure.restrict_smul,
    (isClosedEmbedding_chart n L).measurableEmbedding.restrict_map]
  have heq : chart n L ⁻¹' massSimplex n L = chartDomain n L :=
    Set.ext (chart_mem_simplex_iff n L)
  rw [heq]

/-- The inverse chart pushes intrinsic volume to `√(n+1)` times coordinate volume. -/
theorem map_coordinates_simplexVolume (n : ℕ) (L : ℝ) :
    (simplexVolume n L).map (coordinates n) = ENNReal.ofReal (Real.sqrt (n + 1)) •
      volume.restrict (chartDomain n L) := by
  rw [simplexVolume_eq, Measure.map_smul, Measure.map_map
    (continuous_coordinates n).measurable (continuous_chart n L).measurable]
  have hid : coordinates n ∘ chart n L = id := funext (coordinates_chart n L)
  rw [hid, Measure.map_id]
  exact (continuous_coordinates n).measurable.aemeasurable

/-- Nonnegative change of variables has no integrability or finiteness premise. -/
theorem lintegral_simplexVolume (n : ℕ) (L : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) :
    ∫⁻ y, f y ∂simplexVolume n L = ENNReal.ofReal (Real.sqrt (n + 1)) *
      ∫⁻ x in chartDomain n L, f (chart n L x) := by
  rw [simplexVolume_eq, lintegral_smul_measure,
    (isClosedEmbedding_chart n L).measurableEmbedding.lintegral_map, smul_eq_mul]

/-- Bochner change of variables on the simplex, valid also for nonintegrable functions
with Mathlib's usual integral convention. -/
theorem integral_simplexVolume {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin (n + 1)) → F) :
    ∫ y, f y ∂simplexVolume n L = Real.sqrt (n + 1) •
      ∫ x in chartDomain n L, f (chart n L x) := by
  rw [simplexVolume_eq, integral_smul_measure,
    (isClosedEmbedding_chart n L).integral_map, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- Integrability transfers in both directions. The volume factor is positive and finite. -/
theorem integrable_simplexVolume_iff {F : Type*} [NormedAddCommGroup F]
    (n : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin (n + 1)) → F) :
    Integrable f (simplexVolume n L) ↔
      IntegrableOn (fun x => f (chart n L x)) (chartDomain n L) := by
  rw [simplexVolume_eq, integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))) ENNReal.ofReal_ne_top,
    (isClosedEmbedding_chart n L).measurableEmbedding.integrable_map_iff]
  rfl

/-- The symmetric base point of the mass hyperplane. -/
def centre (n : ℕ) (L : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun _ => L / (n + 1))

theorem sum_centre (n : ℕ) (L : ℝ) : ∑ i, centre n L i = L := by
  simp only [centre, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The barycentre verifies positivity and normalization for every positive mass. -/
theorem centre_mem_simplex (n : ℕ) {L : ℝ} (hL : 0 < L) :
    centre n L ∈ massSimplex n L :=
  ⟨fun _ => div_pos hL (by positivity), sum_centre n L⟩

/-- The correct mass range includes the one-gap case and excludes all nonpositive masses. -/
theorem massSimplex_nonempty_iff (n : ℕ) (L : ℝ) :
    (massSimplex n L).Nonempty ↔ 0 < L := by
  constructor
  · rintro ⟨y, hpos, hsum⟩
    rw [← hsum]
    exact Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  · intro hL
    exact ⟨centre n L, centre_mem_simplex n hL⟩

/-- Outside the positive mass range the simplex is empty and its measure is zero. -/
theorem simplexVolume_nonpos (n : ℕ) {L : ℝ} (hL : L ≤ 0) :
    simplexVolume n L = 0 := by
  have hempty : massSimplex n L = ∅ :=
    not_nonempty_iff_eq_empty.mp (fun h => (not_lt_of_ge hL) ((massSimplex_nonempty_iff n L).mp h))
  simp only [simplexVolume, hempty, Measure.restrict_empty]

/-- The fixed tangent-space chart used on moving-length fibres (Appendix A). -/
def centredChart (n : ℕ) (L : ℝ)
    (z : Tangent n) :
    EuclideanSpace ℝ (Fin (n + 1)) := z.val + centre n L

theorem sum_centredChart (n : ℕ) (L : ℝ)
    (z : Tangent n) :
    ∑ i, centredChart n L z i = L := by
  simp only [centredChart, PiLp.add_apply, Finset.sum_add_distrib, sum_centre,
    (mem_hsOrthSubspace_iff n z.val).mp z.property, zero_add]

/-- The inverse fixed-fibre chart on the full affine hyperplane. -/
def centredCoordinates (n : ℕ) (L : ℝ) (y : massHyperplane n L) :
    Tangent n :=
  ⟨y.val - centre n L, (mem_hsOrthSubspace_iff n _).mpr (by
    simp only [PiLp.sub_apply, Finset.sum_sub_distrib, sum_centre]
    exact sub_eq_zero.mpr y.property)⟩

/-- The affine hyperplane carries exactly the Euclidean metric on its tangent space. -/
def centredIsometryEquiv (n : ℕ) (L : ℝ) :
    Tangent n ≃ᵢ massHyperplane n L where
  toFun z := ⟨centredChart n L z, sum_centredChart n L z⟩
  invFun := centredCoordinates n L
  left_inv z := by apply Subtype.ext; change z.val + centre n L - centre n L = z.val; abel
  right_inv y := by apply Subtype.ext; change y.val - centre n L + centre n L = y.val; abel
  isometry_toFun := by
    intro z w
    change edist (z.val + centre n L) (w.val + centre n L) = edist z.val w.val
    exact (isometry_add_right _).edist_eq z.val w.val

/-- Translation of the library tangent space is an ambient isometric embedding. -/
theorem isometry_centredChart (n : ℕ) (L : ℝ) : Isometry (centredChart n L) :=
  (isometry_add_right (centre n L)).comp isometry_subtype_coe

theorem range_centredChart (n : ℕ) (L : ℝ) :
    range (centredChart n L) = massHyperplane n L := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩; exact sum_centredChart n L z
  · intro hy
    refine ⟨centredCoordinates n L ⟨y, hy⟩, ?_⟩
    exact congrArg Subtype.val ((centredIsometryEquiv n L).apply_symm_apply ⟨y, hy⟩)

/-- The fixed-fibre translation preserves intrinsic volume with factor one. -/
theorem map_volume_centredChart (n : ℕ) (L : ℝ) :
    (volume : Measure (Tangent n)).map
      (centredChart n L) = hyperplaneVolume n L := by
  have h := (isometry_centredChart n L).map_euclideanHausdorffMeasure (d := n)
  have hvol : (Measure.euclideanHausdorffMeasure n :
      Measure (Tangent n)) = volume := by
    simpa only [finrank_tangent] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Tangent n))
  simpa only [hvol, range_centredChart, hyperplaneVolume] using h

/-- Constant-one Jacobian on each positive fibre in fixed zero-sum coordinates. -/
theorem simplexVolume_eq_centredChart_map (n : ℕ) (L : ℝ) :
    simplexVolume n L =
      (volume.restrict (centredChart n L ⁻¹' massSimplex n L)).map (centredChart n L) := by
  rw [simplexVolume_eq_restrict, ← map_volume_centredChart]
  exact (isometry_centredChart n L).isClosedEmbedding.measurableEmbedding.restrict_map _ _

/-- Nonnegative integration over a fixed-fibre chart, also in dimension zero. -/
theorem lintegral_centredChart (n : ℕ) (L : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) :
    ∫⁻ y, f y ∂simplexVolume n L =
      ∫⁻ z in centredChart n L ⁻¹' massSimplex n L, f (centredChart n L z) := by
  rw [simplexVolume_eq_centredChart_map,
    (isometry_centredChart n L).isClosedEmbedding.measurableEmbedding.lintegral_map]

/-- Supply an orthonormal frame explicitly. No choice of coordinates is hidden in the chart. -/
def orthonormalChart (n : ℕ) (L : ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Tangent n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  centredChart n L (b.repr.symm x)

theorem isometry_orthonormalChart (n : ℕ) (L : ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Tangent n)) :
    Isometry (orthonormalChart n L b) :=
  (isometry_centredChart n L).comp b.repr.symm.isometry

/-- Intrinsic volume is Lebesgue measure in every orthonormal frame. -/
theorem map_volume_orthonormalChart (n : ℕ) (L : ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Tangent n)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).map (orthonormalChart n L b) =
      hyperplaneVolume n L := by
  change volume.map (centredChart n L ∘ b.repr.symm) = _
  rw [← Measure.map_map (isometry_centredChart n L).continuous.measurable
    b.repr.symm.continuous.measurable, b.measurePreserving_repr_symm.map_eq,
    map_volume_centredChart]

/-- Restricting an orthonormal chart gives the intrinsic simplex measure. -/
theorem simplexVolume_eq_orthonormalChart_map (n : ℕ) (L : ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Tangent n)) :
    simplexVolume n L =
      (volume.restrict (orthonormalChart n L b ⁻¹' massSimplex n L)).map
        (orthonormalChart n L b) := by
  rw [simplexVolume_eq_restrict, ← map_volume_orthonormalChart n L b]
  exact (isometry_orthonormalChart n L b).isClosedEmbedding.measurableEmbedding.restrict_map _ _

/-- Nonnegative integration in an explicitly supplied orthonormal frame. -/
theorem lintegral_orthonormalChart (n : ℕ) (L : ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Tangent n))
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) :
    ∫⁻ y, f y ∂simplexVolume n L =
      ∫⁻ x in orthonormalChart n L b ⁻¹' massSimplex n L, f (orthonormalChart n L b x) := by
  rw [simplexVolume_eq_orthonormalChart_map n L b,
    (isometry_orthonormalChart n L b).isClosedEmbedding.measurableEmbedding.lintegral_map]

/-- Zero-dimensional fibres are actual point masses. -/
theorem hyperplaneVolume_zero (L : ℝ) :
    hyperplaneVolume 0 L = Measure.dirac (chart 0 L 0) := by
  rw [hyperplaneVolume_eq]
  simp only [Nat.cast_zero, zero_add, Real.sqrt_one, ENNReal.ofReal_one, one_smul]
  rw [volume_euclideanSpace_eq_dirac]
  exact Measure.map_dirac' (continuous_chart 0 L).measurable 0

/-- For one gap and positive mass, the open simplex consists of that single gap. -/
theorem simplexVolume_zero {L : ℝ} (hL : 0 < L) :
    simplexVolume 0 L = Measure.dirac (chart 0 L 0) := by
  have hdomain : chartDomain 0 L = univ := by
    ext x
    simp [chartDomain, hL]
  rw [simplexVolume_eq, hdomain, Measure.restrict_univ]
  simp only [Nat.cast_zero, zero_add, Real.sqrt_one, ENNReal.ofReal_one, one_smul]
  rw [volume_euclideanSpace_eq_dirac]
  exact Measure.map_dirac' (continuous_chart 0 L).measurable 0

/-- Explicit two-gap check of the graph metric. -/
theorem chart_one (L : ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    chart 1 L x = WithLp.toLp 2 ![x 0, L - x 0] := by
  ext i
  fin_cases i <;> simp [chart, Fin.snoc]

end AffineSimplex
end Riesz2
