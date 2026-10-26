/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Riesz2.ToMathlib.SimplexFirstCoordinate

/-!
# Retained coordinates on a mass simplex

The existing deleted-coordinate chart is split into retained and exterior free
coordinates. A permutation permits every retained set and every omitted exterior
coordinate. The volume factor is the existing square root of the number of gaps.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.RetainedSimplex

/-- Concatenation of two lists of free Euclidean coordinates. -/
def join (n m : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n + m)) where
  toFun p := WithLp.toLp 2 (Fin.append (WithLp.ofLp p.1) (WithLp.ofLp p.2))
  invFun y := (WithLp.toLp 2 (fun i => y (i.castAdd m)),
    WithLp.toLp 2 (fun i => y (i.natAdd n)))
  left_inv p := by ext <;> simp
  right_inv y := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_add' p q := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' a p := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem join_left (n m : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    join n m (x, z) (i.castAdd m) = x i := Fin.append_left _ _ _

theorem join_right (n m : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    join n m (x, z) (i.natAdd n) = z i := Fin.append_right _ _ _

theorem sum_join (n m : ℕ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ∑ i, join n m p i = (∑ i, p.1 i) + ∑ i, p.2 i := by
  rw [Fin.sum_univ_add]
  simp [join]

theorem measurePreserving_join (n m : ℕ) : MeasurePreserving (join n m) := by
  have h := (PiLp.volume_preserving_toLp (Fin (n + m))).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (n + m) => ℝ)
      finSumFinEquiv).comp
      ((volume_measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin n ⊕ Fin m => ℝ)).comp
        ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).prod
          (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)))))
  convert h using 1
  funext p
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [join, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]

/-- The original affine simplex chart, with arbitrary labels and split free coordinates.
The last coordinate after relabelling is an exterior coordinate. -/
def chart (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (n + m + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
    (AffineSimplex.chart (n + m) L (join n m p))

/-- The open product-coordinate domain. No values at an empty fibre are chosen. -/
def domain (n m : ℕ) (L : ℝ) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  join n m ⁻¹' AffineSimplex.chartDomain (n + m) L

theorem mem_domain (n m : ℕ) (L : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    p ∈ domain n m L ↔ (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2 i) ∧
      (∑ i, p.2 i) < L - ∑ i, p.1 i := by
  change ((∀ i, 0 < join n m p i) ∧ _) ↔ _
  rw [sum_join]
  constructor
  · rintro ⟨hp, hs⟩
    exact ⟨fun i => by simpa [join] using hp (i.castAdd m),
      fun i => by simpa [join] using hp (i.natAdd n), by linarith⟩
  · rintro ⟨hx, hz, hs⟩
    refine ⟨fun i => ?_, by linarith⟩
    exact Fin.addCases (fun j => by simpa [join] using hx j)
      (fun j => by simpa [join] using hz j) i

theorem isOpen_domain (n m : ℕ) (L : ℝ) : IsOpen (domain n m L) :=
  (AffineSimplex.isOpen_chartDomain (n + m) L).preimage
    (join n m).toContinuousLinearEquiv.continuous

theorem chart_retained (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    chart n m L σ (x, z) (σ (i.castAdd m).castSucc) = x i := by
  simp [chart, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    AffineSimplex.chart_castSucc, join_left]

theorem isBounded_domain (n m : ℕ) (L : ℝ) : Bornology.IsBounded (domain n m L) := by
  have hb := (join n m).symm.toContinuousLinearEquiv.toContinuousLinearMap.lipschitzWith.isBounded_image
    (AffineSimplex.isBounded_chartDomain (n + m) L)
  apply hb.subset
  intro p hp
  exact ⟨join n m p, hp, (join n m).symm_apply_apply p⟩

theorem convex_domain (n m : ℕ) (L : ℝ) : Convex ℝ (domain n m L) :=
  (AffineSimplex.convex_chartDomain (n + m) L).linear_preimage (join n m).toLinearMap

theorem fst_image_domain (n m : ℕ) (L : ℝ) :
    Prod.fst '' domain n m L = AffineSimplex.chartDomain n L := by
  ext x
  constructor
  · rintro ⟨⟨x, z⟩, hp, rfl⟩
    obtain ⟨hx, hz, hs⟩ := (mem_domain n m L (x, z)).mp hp
    exact ⟨hx, by linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hz i).le)]⟩
  · intro hx
    let z : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2
      (fun _ => (L - ∑ i, x i) / (m + 1 : ℝ))
    have hd : 0 < (L - ∑ i, x i) / (m + 1 : ℝ) :=
      div_pos (sub_pos.mpr hx.2) (by positivity)
    refine ⟨(x, z), (mem_domain n m L (x, z)).mpr ⟨hx.1, fun _ => hd, ?_⟩, rfl⟩
    change (∑ _i : Fin m, (L - ∑ i, x i) / (m + 1 : ℝ)) < _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he := div_mul_cancel₀ (L - ∑ i, x i) (show (m + 1 : ℝ) ≠ 0 by positivity)
    nlinarith

theorem reindex_mem_simplex (k : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (k + 1)))
    (y : EuclideanSpace ℝ (Fin (k + 1))) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ y ∈ AffineSimplex.massSimplex k L ↔
      y ∈ AffineSimplex.massSimplex k L := by
  change ((∀ i, 0 < y (σ.symm i)) ∧ (∑ i, y (σ.symm i)) = L) ↔ _
  rw [σ.symm.sum_comp]
  constructor
  · rintro ⟨hp, hs⟩
    exact ⟨fun i => by simpa using hp (σ i), hs⟩
  · rintro ⟨hp, hs⟩
    exact ⟨fun i => hp _, hs⟩

theorem measurableSet_simplex (k : ℕ) (L : ℝ) :
    MeasurableSet (AffineSimplex.massSimplex k L) := by
  change MeasurableSet ({y | ∀ i, 0 < y i} ∩ AffineSimplex.massHyperplane k L)
  apply MeasurableSet.inter
  · simpa only [ofPred_forall] using MeasurableSet.iInter
      (fun i : Fin (k + 1) => measurableSet_lt measurable_const
        (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) i).measurable)
  · exact (AffineSimplex.isClosed_massHyperplane k L).measurableSet

/-- Relabelling is an isometry of intrinsic simplex volume. It is not asserted
that the physical energy is invariant under arbitrary permutations. -/
theorem map_reindex_simplexVolume (k : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (k + 1))) :
    (AffineSimplex.simplexVolume k L).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ) = AffineSimplex.simplexVolume k L := by
  have h := ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure k).restrict_preimage
      (measurableSet_simplex k L)
  have he : (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ) ⁻¹'
      AffineSimplex.massSimplex k L = AffineSimplex.massSimplex k L :=
    Set.ext (reindex_mem_simplex k L σ)
  change MeasurePreserving (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ)
    ((Measure.euclideanHausdorffMeasure k).restrict
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ) ⁻¹' AffineSimplex.massSimplex k L))
    ((Measure.euclideanHausdorffMeasure k).restrict (AffineSimplex.massSimplex k L)) at h
  rw [he] at h
  exact h.map_eq

theorem continuous_chart (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1))) :
    Continuous (chart n m L σ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).continuous.comp
    ((AffineSimplex.continuous_chart (n + m) L).comp
      (join n m).toContinuousLinearEquiv.continuous)

theorem chart_mem_simplex (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    chart n m L σ p ∈ AffineSimplex.massSimplex (n + m) L ↔ p ∈ domain n m L := by
  rw [chart, reindex_mem_simplex, AffineSimplex.chart_mem_simplex_iff]
  rfl

/-- Constant-Jacobian transport for every retained set, also for point fibres. -/
theorem simplexVolume_eq_chart_map (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    AffineSimplex.simplexVolume (n + m) L =
      ENNReal.ofReal (Real.sqrt (n + m + 1)) •
        ((volume.prod volume).restrict (domain n m L)).map (chart n m L σ) := by
  have hj := ((measurePreserving_join n m).restrict_preimage
    (AffineSimplex.isOpen_chartDomain (n + m) L).measurableSet).map_eq
  have hm : Measurable (join n m) := (join n m).toContinuousLinearEquiv.continuous.measurable
  calc
    _ = (AffineSimplex.simplexVolume (n + m) L).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ) :=
      (map_reindex_simplexVolume (n + m) L σ).symm
    _ = _ := by
      rw [AffineSimplex.simplexVolume_eq, Measure.map_smul _
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).continuous.measurable.aemeasurable,
        ← hj, Measure.map_map
          (AffineSimplex.continuous_chart (n + m) L).measurable
          hm,
        Measure.map_map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).continuous.measurable
          ((AffineSimplex.continuous_chart (n + m) L).measurable.comp
            hm)]
      simp only [Nat.cast_add]
      rfl

/-- Tonelli in retained coordinates with the full intrinsic area factor. -/
theorem lintegral_simplexVolume (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {f : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂AffineSimplex.simplexVolume (n + m) L =
      ENNReal.ofReal (Real.sqrt (n + m + 1)) *
        ∫⁻ x : EuclideanSpace ℝ (Fin n), ∫⁻ z : EuclideanSpace ℝ (Fin m),
          (domain n m L).indicator (fun p => f (chart n m L σ p)) (x, z) := by
  rw [simplexVolume_eq_chart_map n m L σ, lintegral_smul_measure,
    lintegral_map hf (continuous_chart n m L σ).measurable, smul_eq_mul,
    ← lintegral_indicator (isOpen_domain n m L).measurableSet]
  congr 1
  exact lintegral_prod _ (((hf.comp (continuous_chart n m L σ).measurable).indicator
    (isOpen_domain n m L).measurableSet).aemeasurable)

/-- Inverse free coordinates on the whole ambient space. On the mass hyperplane
these are the inverse of `chart`. -/
def coordinates (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (y : EuclideanSpace ℝ (Fin (n + m + 1))) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
  (join n m).symm (AffineSimplex.coordinates (n + m)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm y))

theorem continuous_coordinates (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1))) :
    Continuous (coordinates n m σ) :=
  (join n m).symm.toContinuousLinearEquiv.continuous.comp
    ((AffineSimplex.continuous_coordinates (n + m)).comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm).continuous)

theorem coordinates_chart (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    coordinates n m σ (chart n m L σ p) = p := by
  simp [coordinates, chart, ← LinearIsometryEquiv.piLpCongrLeft_symm,
    AffineSimplex.coordinates_chart]

/-- The coordinate law of intrinsic volume, with its explicit area factor. -/
theorem map_coordinates_simplexVolume (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    (AffineSimplex.simplexVolume (n + m) L).map (coordinates n m σ) =
      ENNReal.ofReal (Real.sqrt (n + m + 1)) •
        (volume.prod volume).restrict (domain n m L) := by
  rw [simplexVolume_eq_chart_map n m L σ, Measure.map_smul _
    (continuous_coordinates n m σ).measurable.aemeasurable,
    Measure.map_map (continuous_coordinates n m σ).measurable
      (continuous_chart n m L σ).measurable]
  have he : coordinates n m σ ∘ chart n m L σ = id := funext (coordinates_chart n m L σ)
  rw [he, Measure.map_id]

/-- Convex combinations in the split chart are ambient convex combinations. -/
theorem chart_convex_combination (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (p q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
    {a b : ℝ} (hab : a + b = 1) :
    chart n m L σ (a • p + b • q) =
      a • chart n m L σ p + b • chart n m L σ q := by
  simp only [chart, map_add, map_smul,
    AffineSimplex.chart_convex_combination (n + m) L _ _ hab]

/-- A general density transported to the split chart. The indicator is precisely
its coordinate support, not an assigned value of the energy off the simplex. -/
theorem map_coordinates_withDensity (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {w : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ≥0∞} (hw : Measurable w) :
    ((AffineSimplex.simplexVolume (n + m) L).withDensity w).map (coordinates n m σ) =
      ENNReal.ofReal (Real.sqrt (n + m + 1)) •
        (volume.prod volume).withDensity
          ((domain n m L).indicator (fun p => w (chart n m L σ p))) := by
  have hm : Measurable (coordinates n m σ) := (continuous_coordinates n m σ).measurable
  rw [simplexVolume_eq_chart_map n m L σ, withDensity_smul_measure,
    Measure.map_smul _ hm.aemeasurable,
    ← Riesz1.map_withDensity_comp _ (continuous_chart n m L σ).measurable hw,
    Measure.map_map hm (continuous_chart n m L σ).measurable]
  have he : coordinates n m σ ∘ chart n m L σ = id := funext (coordinates_chart n m L σ)
  rw [he, Measure.map_id, withDensity_indicator (isOpen_domain n m L).measurableSet]

/-- The intrinsic base-coordinate carrier has finite Lebesgue volume. -/
instance finite_baseVolume (n : ℕ) (L : ℝ) :
    IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
      ((↑) : AffineSimplex.chartDomain n L → EuclideanSpace ℝ (Fin n))) where
  measure_univ_lt_top := by
    rw [comap_subtype_coe_apply (AffineSimplex.isOpen_chartDomain n L).measurableSet,
      Set.image_univ, Subtype.range_coe]
    exact lt_of_le_of_lt (measure_mono subset_closure)
      ((AffineSimplex.isBounded_chartDomain n L).isCompact_closure.measure_lt_top)

/-- The retained coordinates really are the selected original gap labels. -/
theorem coordinates_retained (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (y : EuclideanSpace ℝ (Fin (n + m + 1))) (i : Fin n) :
    (coordinates n m σ y).1 i = y (σ (i.castAdd m).castSucc) := by
  simp [coordinates, join, AffineSimplex.coordinates,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- A scalar multiple of an intrinsic density in retained coordinates. -/
theorem map_coordinates_smul_withDensity (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (c : ℝ≥0∞)
    {w : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ≥0∞} (hw : Measurable w) :
    (c • (ENNReal.ofReal (Real.sqrt (n + m + 1)))⁻¹ •
        (AffineSimplex.simplexVolume (n + m) L).withDensity w).map (coordinates n m σ) =
      c • (volume.prod volume).withDensity
        ((domain n m L).indicator (fun p => w (chart n m L σ p))) := by
  have hm := (continuous_coordinates n m σ).measurable
  rw [Measure.map_smul _ hm.aemeasurable, Measure.map_smul _ hm.aemeasurable,
    map_coordinates_withDensity n m L σ hw]
  simp only [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
    (Real.sqrt_pos.mpr (show (0 : ℝ) < n + m + 1 by positivity))) ENNReal.ofReal_ne_top,
    mul_one]

/-- Insert a full exterior gap vector after the retained coordinates, then
apply the selected relabelling. This uses the same concatenation map. -/
def assemble (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (n + m + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ (join n (m + 1) (x, y))

theorem continuous_assemble (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n)) : Continuous (assemble n m σ x) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).continuous.comp
    ((join n (m + 1)).toContinuousLinearEquiv.continuous.comp
      (continuous_const.prodMk continuous_id))

set_option backward.isDefEq.respectTransparency false in
/-- The exterior coordinates in the full chart are exactly the existing
arbitrary-mass exterior simplex chart. -/
theorem assemble_chart (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) :
    assemble n m σ x (AffineSimplex.chart m (L - ∑ i, x i) z) = chart n m L σ (x, z) := by
  unfold assemble chart
  congr 1
  change join n (m + 1) (x, AffineSimplex.chart m (L - ∑ i, x i) z) =
    AffineSimplex.chart (n + m) L (join n m (x, z))
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · calc
      _ = AffineSimplex.chart m (L - ∑ i, x i) z (Fin.last m) :=
        join_right n (m + 1) x _ (Fin.last m)
      _ = L - ∑ i, x i - ∑ i, z i := AffineSimplex.chart_last m _ z
      _ = L - ∑ i, join n m (x, z) i := by rw [sum_join]; ring
      _ = _ := (AffineSimplex.chart_last (n + m) L _).symm
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · calc
        _ = x k := join_left n (m + 1) x _ k
        _ = join n m (x, z) (k.castAdd m) := (join_left n m x z k).symm
        _ = _ := (AffineSimplex.chart_castSucc (n + m) L _ (k.castAdd m)).symm
    · calc
        _ = AffineSimplex.chart m (L - ∑ i, x i) z k.castSucc :=
          join_right n (m + 1) x _ k.castSucc
        _ = z k := AffineSimplex.chart_castSucc m _ z k
        _ = join n m (x, z) (k.natAdd n) := (join_right n m x z k).symm
        _ = _ := (AffineSimplex.chart_castSucc (n + m) L _ (k.natAdd n)).symm

/-- On the retained interior the support in exterior free coordinates is exactly
the existing exterior chart domain, with its true remaining mass. -/
theorem fibre_domain (n m : ℕ) (L : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n L) :
    {z : EuclideanSpace ℝ (Fin m) | (x, z) ∈ domain n m L} =
      AffineSimplex.chartDomain m (L - ∑ i, x i) := by
  ext z
  rw [Set.mem_ofPred_eq, mem_domain]
  exact and_iff_right hx.1

/-- Every enumeration of retained gap labels occurs in one of these charts.
No particular extension permutation is chosen as part of a definition. -/
theorem exists_chart_labels (n m : ℕ) (e : Fin n ↪ Fin (n + m + 1)) :
    ∃ σ : Equiv.Perm (Fin (n + m + 1)), ∀ i : Fin n,
      σ (i.castAdd m).castSucc = e i := by
  apply Equiv.Perm.exists_extending_pair
    (fun i : Fin n => (i.castAdd m).castSucc) e
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin (n + m + 1) => k.val) hij
  · exact e.injective

end Riesz2.RetainedSimplex
