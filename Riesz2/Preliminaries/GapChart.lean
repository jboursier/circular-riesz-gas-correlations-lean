/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineSimplexCharts
public import Riesz2.Preliminaries.FiniteModelValidity
public import Riesz2.Frozen.PhysicalAmbientGapEnergy
public import Riesz2.Preliminaries.ShortKernelProperties
public import Riesz2.Bridges.CyclicLabels
public import Riesz1.Rigidity.GapLawSimplex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite microscopic gap coordinates

The deleted-last-coordinate chart in Subsection 1.7, using the literal
library configuration carrier and the microscopic gaps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2
namespace GapChart

/-- First `n` microscopic gaps of the library cumulative chart. -/
def difference (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun y i := Riesz1.anchoredGapVector n y i.castSucc
  map_add' y z := by
    ext i
    simp only [Pi.add_apply, Riesz1.anchoredGapVector_castSucc]
    have h (j : Fin (n + 1)) := Riesz1.anchorVector_combo y z 1 1 j
    simp only [one_smul, one_mul] at h
    rw [h, h]
    ring
  map_smul' a y := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Riesz1.anchoredGapVector_castSucc]
    have h (j : Fin (n + 1)) := Riesz1.anchorVector_combo y y a 0 j
    simp only [zero_smul, add_zero, zero_mul] at h
    rw [h, h]
    ring

theorem difference_apply (n : ℕ) (y : Fin n → ℝ) (i : Fin n) :
    difference n y i = (n + 1 : ℝ) *
      (y i - Riesz1.anchorVector y i.castSucc) :=
  Riesz1.anchoredGapVector_castSucc n y i

/-- The triangular gap derivative has diagonal `n+1`. -/
theorem det_difference (n : ℕ) : LinearMap.det (difference n) = (n + 1 : ℝ) ^ n := by
  classical
  rw [← LinearMap.det_toMatrix']
  have hm (i j : Fin n) : LinearMap.toMatrix' (difference n) i j =
      (n + 1 : ℝ) * ((Pi.single j 1 : Fin n → ℝ) i -
        Riesz1.anchorVector (Pi.single j 1) i.castSucc) := by
    rw [LinearMap.toMatrix'_apply, difference_apply]
  have hlow : (LinearMap.toMatrix' (difference n)).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    rw [hm]
    have hne : i ≠ j := ne_of_lt hij
    have hz : Riesz1.anchorVector (Pi.single j 1) i.castSucc = 0 := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          change (Pi.single j 1 : Fin (n + 1) → ℝ) i.castSucc = 0
          apply Pi.single_eq_of_ne
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_castSucc] at hv
          change i.val + 1 < j.val at hij
          omega
    simp [hne, hz]
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  have hdiag (i : Fin n) : LinearMap.toMatrix' (difference n) i i = (n + 1 : ℝ) := by
    rw [hm]
    have hz : Riesz1.anchorVector (Pi.single i 1) i.castSucc = 0 := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          change (Pi.single i.succ 1 : Fin (n + 1) → ℝ) i.castSucc = 0
          apply Pi.single_eq_of_ne
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_succ] at hv
          omega
    simp [hz]
  simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The square, deleted-coordinate gap map is invertible. -/
def differenceEquiv (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (difference n).equivOfIsUnitDet (isUnit_iff_ne_zero.mpr (by
    rw [det_difference]
    positivity))

theorem differenceEquiv_apply (n : ℕ) (y : Fin n → ℝ) :
    differenceEquiv n y = difference n y := by
  exact LinearMap.equivOfIsUnitDet_apply _ _

/-- The actual chart sends a configuration to its rotation and its first `n` gaps. -/
def coordinates (n : ℕ) (X : Riesz1.Configuration n.succPNat) : ℝ × (Fin n → ℝ) :=
  (X.val 0, fun i => gapVector X i.castSucc)

theorem coordinates_eq (n : ℕ) (X : Riesz1.Configuration n.succPNat) :
    coordinates n X = Prod.map id (difference n) (Riesz1.anchorCoords n X.val) := by
  refine Prod.ext rfl ?_
  ext i
  exact congrFun (Riesz1.gapVector_eq_anchoredGapVector n X) i.castSucc

theorem measurable_coordinates (n : ℕ) : Measurable (coordinates n) := by
  have heq : coordinates n = Prod.map id (difference n) ∘
      (fun X : Riesz1.Configuration n.succPNat => Riesz1.anchorCoords n X.val) :=
    funext (coordinates_eq n)
  rw [heq]
  exact (measurable_id.prodMap (difference n).continuous_of_finiteDimensional.measurable).comp
    (Riesz1.measurable_anchorCoords_config n)

theorem sum_anchoredGapVector (n : ℕ) (y : Fin n → ℝ) :
    ∑ i, Riesz1.anchoredGapVector n y i = (n + 1 : ℝ) := by
  have hs := Riesz1.partialSum_anchoredGapVector n y (Fin.last n)
  have ht := Fin.partialSum_succ (Riesz1.anchoredGapVector n y) (Fin.last n)
  let v : Fin (n + 1) → ℝ := Riesz1.anchoredGapVector n y
  change Fin.partialSum v (Fin.last (n + 1)) =
    Fin.partialSum v (Fin.last n).castSucc + v (Fin.last n) at ht
  change Fin.partialSum v (Fin.last n).castSucc = _ at hs
  rw [Riesz1.partialSum_last_real, hs] at ht
  have hl : v (Fin.last n) = (n + 1 : ℝ) * (1 - Riesz1.anchorVector y (Fin.last n)) :=
    Riesz1.anchoredGapVector_last n y
  rw [hl] at ht
  change ∑ i, v i = _
  linarith

/-- The cumulative and deleted-coordinate charts give the same full gap vector. -/
theorem completion_difference (n : ℕ) (y : Fin n → ℝ) :
    AffineSimplex.chart n (n + 1) (WithLp.toLp 2 (difference n y)) =
      WithLp.toLp 2 (Riesz1.anchoredGapVector n y) := by
  apply AffineSimplex.chart_coordinates n (n + 1)
    (y := WithLp.toLp 2 (Riesz1.anchoredGapVector n y))
  exact sum_anchoredGapVector n y

/-- Exact domain equivalence, including positivity of the omitted gap. -/
theorem difference_mem_iff (n : ℕ) (y : Fin n → ℝ) :
    WithLp.toLp 2 (difference n y) ∈ AffineSimplex.chartDomain n (n + 1) ↔
      y ∈ Riesz1.anchoredDomain n := by
  rw [← AffineSimplex.chart_mem_simplex_iff, completion_difference]
  constructor
  · intro hy
    have hys : Riesz1.anchoredGapVector n y ∈ Riesz1.gapSimplex n.succPNat :=
      ⟨hy.1, by convert hy.2 using 1 <;> first | rfl | simp [Nat.succPNat_coe]⟩
    have h := Riesz1.gapCumulative_mem_anchoredDomain n hys
    rwa [Riesz1.gapCumulative_anchoredGapVector] at h
  · intro hy
    have h := Riesz1.anchoredGapVector_mem_gapSimplex n hy
    exact ⟨h.1, by convert h.2 using 1 <;> first | rfl | simp [Nat.succPNat_coe]⟩

/-- Exact inverse of the gap differences, expressed as normalized partial sums. -/
theorem difference_inverse (n : ℕ) (y : Fin n → ℝ) :
    (differenceEquiv n).symm y =
      Riesz1.gapCumulative n
        (WithLp.ofLp (AffineSimplex.chart n (n + 1) (WithLp.toLp 2 y))) := by
  apply (differenceEquiv n).injective
  rw [(differenceEquiv n).apply_symm_apply, differenceEquiv_apply]
  ext i
  have h := congrFun (Riesz1.anchoredGapVector_gapCumulative n
    (WithLp.ofLp (AffineSimplex.chart n (n + 1) (WithLp.toLp 2 y)))
    (AffineSimplex.sum_chart n (n + 1) _)) i.castSucc
  exact (h.trans (AffineSimplex.chart_castSucc n (n + 1) _ i)).symm

/-- Lebesgue change of variables for the square gap derivative. -/
theorem map_volume_difference (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).map (difference n) =
      ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ • volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [det_difference]; positivity),
    det_difference, abs_of_pos (inv_pos.mpr (by positivity)),
    ENNReal.ofReal_inv_of_pos (by positivity)]

/-- Restricted volume in the first `n` gaps. This is the factor `N^{-(N-1)}`. -/
theorem map_restrict_volume_difference (n : ℕ) :
    (volume.restrict (Riesz1.anchoredDomain n)).map (difference n) =
      ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
        volume.restrict ((WithLp.toLp 2) ⁻¹' AffineSimplex.chartDomain n (n + 1)) := by
  have hpre : (difference n) ⁻¹' ((WithLp.toLp 2) ⁻¹'
      AffineSimplex.chartDomain n (n + 1)) = Riesz1.anchoredDomain n :=
    Set.ext (difference_mem_iff n)
  rw [← hpre, ← Measure.restrict_map (difference n).continuous_of_finiteDimensional.measurable
    ((AffineSimplex.isOpen_chartDomain n (n + 1)).measurableSet.preimage
      (PiLp.continuous_toLp 2 _).measurable), map_volume_difference, Measure.restrict_smul]

/-- See Subsection 1.7 of the paper, the exact particle-volume formula in deleted gap
coordinates. Rotation is ordinary Lebesgue measure on `[0,1)`. -/
theorem map_configurationVolume_coordinates (n : ℕ) :
    (Riesz1.configurationVolume n.succPNat).map (coordinates n) =
      ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
        ((volume.restrict (Ico (0 : ℝ) 1)).prod
          (volume.restrict ((WithLp.toLp 2) ⁻¹'
            AffineSimplex.chartDomain n (n + 1)))) := by
  have heq : coordinates n = Prod.map id (difference n) ∘
      (fun X : Riesz1.Configuration n.succPNat => Riesz1.anchorCoords n X.val) :=
    funext (coordinates_eq n)
  rw [heq, ← Measure.map_map
    (measurable_id.prodMap (difference n).continuous_of_finiteDimensional.measurable)
    (Riesz1.measurable_anchorCoords_config n), Riesz1.map_anchorCoords_configurationVolume,
    ← Measure.map_prod_map _ _ measurable_id
      (difference n).continuous_of_finiteDimensional.measurable,
    Measure.map_id, map_restrict_volume_difference, Measure.prod_smul_right]

/-- Inverse particle lifts, on the entire coordinate space. -/
def inverse (n : ℕ) (p : ℝ × (Fin n → ℝ)) : Fin (n + 1) → ℝ :=
  Riesz1.anchorInverse n (p.1, (differenceEquiv n).symm p.2)

/-- Every configuration is recovered from its rotation and first `n` gaps. -/
theorem inverse_coordinates (n : ℕ) (X : Riesz1.Configuration n.succPNat) :
    inverse n (coordinates n X) = X.val := by
  have h : (differenceEquiv n).symm (coordinates n X).2 =
      (Riesz1.anchorCoords n X.val).2 := by
    rw [coordinates_eq]
    change (differenceEquiv n).symm (difference n (Riesz1.anchorCoords n X.val).2) = _
    rw [← differenceEquiv_apply, (differenceEquiv n).symm_apply_apply]
  ext i
  change (coordinates n X).1 + Riesz1.anchorVector
    ((differenceEquiv n).symm (coordinates n X).2) i = X.val i
  rw [h]
  exact (Riesz1.apply_eq_anchor_add n X.val i).symm

/-- The inverse formula in Subsection 1.7: positions are normalized
partial sums of the full gap vector plus the rotation coordinate. -/
theorem inverse_apply (n : ℕ) (p : ℝ × (Fin n → ℝ)) (i : Fin (n + 1)) :
    inverse n p i = p.1 +
      Fin.partialSum (WithLp.ofLp
        (AffineSimplex.chart n (n + 1) (WithLp.toLp 2 p.2))) i.castSucc / (n + 1 : ℝ) := by
  change p.1 + Riesz1.anchorVector ((differenceEquiv n).symm p.2) i = _
  rw [difference_inverse, Riesz1.anchorVector_gapCumulative]

/-- The chart domain is exactly `[0,1)` times the open deleted-coordinate simplex. -/
theorem inverse_mem_orderedDomain_iff (n : ℕ) (p : ℝ × (Fin n → ℝ)) :
    inverse n p ∈ Riesz1.orderedDomain n.succPNat ↔
      p.1 ∈ Ico (0 : ℝ) 1 ∧
        WithLp.toLp 2 p.2 ∈ AffineSimplex.chartDomain n (n + 1) := by
  rw [Riesz1.orderedDomain_eq_preimage]
  change Riesz1.anchorCoords n (Riesz1.anchorInverse n
    (p.1, (differenceEquiv n).symm p.2)) ∈
      Ico (0 : ℝ) 1 ×ˢ Riesz1.anchoredDomain n ↔ _
  rw [Riesz1.anchorCoords_anchorInverse]
  change (_ ∧ (differenceEquiv n).symm p.2 ∈ Riesz1.anchoredDomain n) ↔ _
  rw [← difference_mem_iff]
  have h : difference n ((differenceEquiv n).symm p.2) = p.2 := by
    rw [← differenceEquiv_apply, (differenceEquiv n).apply_symm_apply]
  rw [h]

theorem coordinates_inverse (n : ℕ) (p : ℝ × (Fin n → ℝ))
    (hp : p.1 ∈ Ico (0 : ℝ) 1 ∧
      WithLp.toLp 2 p.2 ∈ AffineSimplex.chartDomain n (n + 1)) :
    coordinates n ⟨inverse n p, (inverse_mem_orderedDomain_iff n p).mpr hp⟩ = p := by
  rw [coordinates_eq]
  change Prod.map id (difference n)
    (Riesz1.anchorCoords n (Riesz1.anchorInverse n
      (p.1, (differenceEquiv n).symm p.2))) = p
  rw [Riesz1.anchorCoords_anchorInverse]
  refine Prod.ext rfl ?_
  change difference n ((differenceEquiv n).symm p.2) = p.2
  rw [← differenceEquiv_apply, (differenceEquiv n).apply_symm_apply]

/-- The exact bijective part of Subsection 1.7, with no discarded endpoints. -/
theorem coordinates_range (n : ℕ) :
    range (coordinates n) = Ico (0 : ℝ) 1 ×ˢ
      ((WithLp.toLp 2) ⁻¹' AffineSimplex.chartDomain n (n + 1)) := by
  ext p
  constructor
  · rintro ⟨X, rfl⟩
    exact (inverse_mem_orderedDomain_iff n _).mp
      (by rw [inverse_coordinates]; exact X.property)
  · intro hp
    exact ⟨⟨inverse n p, (inverse_mem_orderedDomain_iff n p).mpr hp⟩,
      coordinates_inverse n p hp⟩

theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates n) := by
  intro X Y h
  apply Subtype.ext
  rw [← inverse_coordinates n X, ← inverse_coordinates n Y, h]

/-- Transfer from product coordinates to Euclidean coordinates preserves volume. -/
theorem map_toLp_restrict (n : ℕ) :
    (volume.restrict ((WithLp.toLp 2) ⁻¹'
      AffineSimplex.chartDomain n (n + 1))).map (WithLp.toLp 2) =
        volume.restrict (AffineSimplex.chartDomain n (n + 1)) := by
  rw [← Measure.restrict_map (PiLp.volume_preserving_toLp (Fin n)).measurable
    (AffineSimplex.isOpen_chartDomain n (n + 1)).measurableSet,
    (PiLp.volume_preserving_toLp (Fin n)).map_eq]

/-- The library's cumulative-coordinate simplex volume and the intrinsic Euclidean
volume differ by precisely `N^{-(N-1)} / √N` (Subsection 1.7). -/
theorem map_toLp_gapSimplexVolume (n : ℕ) :
    (Riesz1.gapSimplexVolume n).map
      (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))) =
      ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
        (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ •
          AffineSimplex.simplexVolume n (n + 1) := by
  have hfun : (fun y => (WithLp.toLp 2 (fun i : Fin (n + 1) =>
      Riesz1.anchoredGapVector n y i) :
      EuclideanSpace ℝ (Fin (n + 1)))) =
      AffineSimplex.chart n (n + 1) ∘ (WithLp.toLp 2) ∘ difference n :=
    funext (fun y => (completion_difference n y).symm)
  rw [Riesz1.gapSimplexVolume, Measure.map_map
    (PiLp.volume_preserving_toLp (Fin (n + 1))).measurable
    (Riesz1.measurable_anchoredGapVector n)]
  change (volume.restrict (Riesz1.anchoredDomain n)).map
    (fun y => (WithLp.toLp 2 (fun i : Fin (n + 1) =>
      Riesz1.anchoredGapVector n y i) :
      EuclideanSpace ℝ (Fin (n + 1)))) = _
  rw [hfun, ← Measure.map_map (AffineSimplex.continuous_chart n (n + 1)).measurable
    ((PiLp.volume_preserving_toLp (Fin n)).measurable.comp
      (difference n).continuous_of_finiteDimensional.measurable),
    ← Measure.map_map (PiLp.volume_preserving_toLp (Fin n)).measurable
      (difference n).continuous_of_finiteDimensional.measurable,
    map_restrict_volume_difference, Measure.map_smul, map_toLp_restrict,
    Measure.map_smul, AffineSimplex.simplexVolume_eq, smul_smul, smul_smul, mul_assoc,
    ENNReal.inv_mul_cancel (by simp [Real.sqrt_pos.mpr (show (0 : ℝ) < n + 1 by positivity)])
      ENNReal.ofReal_ne_top, mul_one]
  · exact (AffineSimplex.continuous_chart n (n + 1)).measurable.aemeasurable
  · exact (PiLp.volume_preserving_toLp (Fin n)).measurable.aemeasurable

/-- The chart's true positive domain as a subtype, so inverse configurations and
their densities need no values on invalid gaps. -/
abbrev Domain (n : ℕ) :=
  {y : Fin n → ℝ // WithLp.toLp 2 y ∈ AffineSimplex.chartDomain n (n + 1)}

theorem measurableSet_domain (n : ℕ) : MeasurableSet
    ((WithLp.toLp 2) ⁻¹' AffineSimplex.chartDomain n (n + 1)) :=
  (AffineSimplex.isOpen_chartDomain n (n + 1)).measurableSet.preimage
    (PiLp.volume_preserving_toLp (Fin n)).measurable

/-- Lebesgue measure on the actual open coordinate domain. -/
def coordinateVolume (n : ℕ) : Measure (Domain n) := volume.comap Subtype.val

/-- The positive gap coordinates of an actual configuration. -/
def gaps (n : ℕ) (X : Riesz1.Configuration n.succPNat) : Domain n :=
  ⟨(coordinates n X).2, ((coordinates_range n).subset ⟨X, rfl⟩).2⟩

theorem measurable_gaps (n : ℕ) : Measurable (gaps n) :=
  ((measurable_coordinates n).snd).subtype_mk

/-- The unique inverse configuration with rotation zero. -/
def reconstruct (n : ℕ) (y : Domain n) : Riesz1.Configuration n.succPNat :=
  ⟨inverse n (0, y.val), (inverse_mem_orderedDomain_iff n _).mpr
    ⟨by norm_num, y.property⟩⟩

theorem measurable_reconstruct (n : ℕ) : Measurable (reconstruct n) := by
  apply Measurable.subtype_mk
  change Measurable (fun y : Domain n => Riesz1.anchorInverse n
    (0, (differenceEquiv n).symm y.val))
  unfold Riesz1.anchorInverse
  exact Measurable.of_eval (fun i => measurable_const.add
    ((measurable_pi_apply i).comp (((Riesz1.measurable_anchorVector n).comp
      (differenceEquiv n).symm.toLinearMap.continuous_of_finiteDimensional.measurable).comp
        measurable_subtype_coe)))

theorem anchorCoords_reconstruct (n : ℕ) (y : Domain n) :
    Riesz1.anchorCoords n (reconstruct n y).val =
      (0, (differenceEquiv n).symm y.val) :=
  Riesz1.anchorCoords_anchorInverse n _

theorem anchored_gaps (n : ℕ) (X : Riesz1.Configuration n.succPNat) :
    (differenceEquiv n).symm (gaps n X).val = (Riesz1.anchorCoords n X.val).2 := by
  change (differenceEquiv n).symm (coordinates n X).2 = _
  rw [coordinates_eq]
  change (differenceEquiv n).symm (difference n (Riesz1.anchorCoords n X.val).2) = _
  rw [← differenceEquiv_apply, (differenceEquiv n).symm_apply_apply]

/-- Translation changes no short-range pair separation. -/
theorem shortEnergy_eq_of_pair_differences (s : ShortExponent) {N : ℕ+}
    (X Y : Riesz1.Configuration N)
    (h : ∀ i j, X.val i - X.val j = Y.val i - Y.val j) :
    shortEnergy s X = shortEnergy s Y := by
  unfold shortEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Subtype.ext
  exact h i j.val

/-- The actual energy depends only on the positive gaps, in either exponent regime.
This is the inverse-chart part of the energy identity in Subsection 1.7. -/
theorem energy_reconstruct_gaps (p : Parameters) (n : ℕ)
    (X : Riesz1.Configuration n.succPNat) :
    energy p (reconstruct n (gaps n X)) = energy p X := by
  have hc := anchorCoords_reconstruct n (gaps n X)
  rw [anchored_gaps] at hc
  unfold energy
  split_ifs with hs
  · rw [Riesz1.energy_eq_anchoredEnergy, Riesz1.energy_eq_anchoredEnergy, hc]
  · apply shortEnergy_eq_of_pair_differences
    intro i j
    rw [Riesz1.apply_eq_anchor_add n (reconstruct n (gaps n X)).val i,
      Riesz1.apply_eq_anchor_add n (reconstruct n (gaps n X)).val j,
      Riesz1.apply_eq_anchor_add n X.val i, Riesz1.apply_eq_anchor_add n X.val j, hc]
    ring

instance coordinateVolume_finite (n : ℕ) : IsFiniteMeasure (coordinateVolume n) where
  measure_univ_lt_top := by
    have hm := comap_subtype_coe_apply (measurableSet_domain n)
      (volume : Measure (Fin n → ℝ)) (Set.univ : Set (Domain n))
    apply lt_of_eq_of_lt hm
    rw [Set.image_univ, Subtype.range_coe]
    apply lt_of_le_of_lt (measure_mono ?_)
      ((isCompact_Icc : IsCompact (Icc (0 : Fin n → ℝ) (fun _ => (n + 1 : ℝ)))).measure_lt_top
        (μ := (volume : Measure (Fin n → ℝ))))
    intro y hy
    refine ⟨fun i => (hy.1 i).le, fun i => ?_⟩
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin n => y j) (fun j _ => (hy.1 j).le) (Finset.mem_univ i)
    exact le_trans h hy.2.le

/-- The chart-volume formula on the true positive coordinate carrier. -/
theorem map_configurationVolume_gaps (n : ℕ) :
    (Riesz1.configurationVolume n.succPNat).map
      (fun X => (X.val 0, gaps n X)) =
        ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
          (volume.restrict (Ico (0 : ℝ) 1)).prod (coordinateVolume n) := by
  have he : MeasurableEmbedding
      (Prod.map (id : ℝ → ℝ) (Subtype.val : Domain n → (Fin n → ℝ))) :=
    (MeasurableEquiv.refl ℝ).measurableEmbedding.prodMap
      (MeasurableEmbedding.subtype_coe (measurableSet_domain n))
  have hrot : Measurable (fun X : Riesz1.Configuration n.succPNat => X.val 0) :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have hc : (coordinateVolume n).map (Subtype.val : Domain n → (Fin n → ℝ)) =
      volume.restrict ((WithLp.toLp 2) ⁻¹' AffineSimplex.chartDomain n (n + 1)) :=
    map_comap_subtype_coe (measurableSet_domain n) volume
  apply he.map_injective
  rw [Measure.map_map he.measurable (hrot.prodMk (measurable_gaps n)),
    Measure.map_smul _ he.measurable.aemeasurable,
    ← Measure.map_prod_map _ _ measurable_id measurable_subtype_coe,
    Measure.map_id, hc]
  exact map_configurationVolume_coordinates n

/-- Unnormalized Gibbs density in the exact inverse chart. It is defined only on
the positive domain, and uses the particle energy without an extension. -/
def weight (p : Parameters) (n : ℕ) (y : Domain n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-p.val.1 * energy p (reconstruct n y)))

theorem measurable_weight (p : Parameters) (n : ℕ) : Measurable (weight p n) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_energy p _).comp (measurable_reconstruct n))))

theorem weight_gaps (p : Parameters) (n : ℕ) (X : Riesz1.Configuration n.succPNat) :
    weight p n (gaps n X) = ENNReal.ofReal (Real.exp (-p.val.1 * energy p X)) := by
  rw [weight, energy_reconstruct_gaps]

theorem gibbsMeasure_eq_withDensity (p : Parameters) (N : ℕ+) :
    gibbsMeasure p N = (partitionFunction p N)⁻¹ •
      (Riesz1.configurationVolume N).withDensity
        (fun X => ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) := by
  unfold gibbsMeasure partitionFunction energy
  split_ifs
  · rfl
  · rfl

/-- Exact joint Gibbs density in the finite gap chart, for both exponent regimes.
Rotation has uniform measure on `[0,1)` and is independent of the gaps.
The gap normalizer includes the same `N^{-(N-1)}` in both regimes.
This is the density consequence of Subsection 1.7. -/
theorem map_gibbsMeasure_coordinates_density (p : Parameters) (n : ℕ) :
    (gibbsMeasure p n.succPNat).map (fun X => (X.val 0, gaps n X)) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod
        ((partitionFunction p n.succPNat)⁻¹ •
          ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
            (coordinateVolume n).withDensity (weight p n)) := by
  have hF : Measurable (fun X : Riesz1.Configuration n.succPNat => (X.val 0, gaps n X)) :=
    ((measurable_pi_apply 0).comp measurable_subtype_coe).prodMk (measurable_gaps n)
  have hw : (fun X : Riesz1.Configuration n.succPNat =>
      ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) =
        fun X => weight p n (gaps n X) := funext (fun X => (weight_gaps p n X).symm)
  rw [gibbsMeasure_eq_withDensity, Measure.map_smul _ hF.aemeasurable, hw,
    Riesz1.map_withDensity_comp _ hF (g := fun z : ℝ × Domain n => weight p n z.2)
      ((measurable_weight p n).comp measurable_snd),
    map_configurationVolume_gaps, withDensity_smul_measure,
    ← prod_withDensity_right (measurable_weight p n),
    ← Measure.prod_smul_right, ← Measure.prod_smul_right]

/-- The exact positive-domain gap density, with its finite-model normalizer. -/
theorem map_gibbsMeasure_gaps_density (p : Parameters) (n : ℕ) :
    (gibbsMeasure p n.succPNat).map (gaps n) =
      (partitionFunction p n.succPNat)⁻¹ •
        ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
          (coordinateVolume n).withDensity (weight p n) := by
  have h := congrArg (Measure.map Prod.snd) (map_gibbsMeasure_coordinates_density p n)
  have hF : Measurable (fun X : Riesz1.Configuration n.succPNat => (X.val 0, gaps n X)) :=
    ((measurable_pi_apply 0).comp measurable_subtype_coe).prodMk (measurable_gaps n)
  rw [Measure.map_map measurable_snd hF,
    Measure.map_snd_prod, Riesz1.measure_restrict_Ico_univ, one_smul] at h
  exact h

private theorem sum_reflected_lengths {N : ℕ} (hN : 2 ≤ N) (A : Fin (N - 1) → ℝ)
    (hA : ∀ r, A ⟨N - 2 - r.val, by have := r.isLt; omega⟩ = A r) :
    (∑ r, A r) = ∑ r : Fin (N / 2),
      (2 - if 2 * (r.val + 1) = N then (1 : ℝ) else 0) *
        A ⟨r.val, by have := r.isLt; omega⟩ := by
  classical
  let s := Finset.univ.filter (fun r : Fin (N - 1) => r.val + 1 ≤ N / 2)
  let t := Finset.univ.filter (fun r : Fin (N - 1) => N / 2 < r.val + 1)
  have hsplit : Finset.univ = s ∪ t := by
    ext r
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      le_or_gt]
  have hdisjoint : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and] at hr hs
    omega
  have hreflect : (∑ r ∈ t, A r) =
      ∑ r ∈ s with 2 * (r.val + 1) ≠ N, A r := by
    apply Finset.sum_bij (fun r _ => (⟨N - 2 - r.val,
      by have := r.isLt; omega⟩ : Fin (N - 1)))
    · intro r hr
      have := r.isLt
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro r hr q hq heq
      have := r.isLt
      have := q.isLt
      have := congrArg Fin.val heq
      apply Fin.ext
      dsimp at this
      omega
    · intro r hr
      have := r.isLt
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      refine ⟨⟨N - 2 - r.val, by omega⟩, ?_, ?_⟩
      · simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · apply Fin.ext
        dsimp
        omega
    · intro r _
      exact (hA r).symm
  rw [hsplit, Finset.sum_union hdisjoint, hreflect]
  have hterm (r : Fin (N - 1)) :
      (2 - if 2 * (r.val + 1) = N then (1 : ℝ) else 0) * A r =
        A r + if 2 * (r.val + 1) ≠ N then A r else 0 := by
    split_ifs <;> simp_all <;> ring
  have hweight : (∑ r ∈ s, A r) + (∑ r ∈ s with 2 * (r.val + 1) ≠ N, A r) =
      ∑ r ∈ s, (2 - if 2 * (r.val + 1) = N then (1 : ℝ) else 0) * A r := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_filter]
  rw [hweight]
  apply Finset.sum_bij (fun r hr => (⟨r.val, by
    have : r.val + 1 ≤ N / 2 := (Finset.mem_filter.mp hr).2
    omega⟩ : Fin (N / 2)))
  · intro r _
    exact Finset.mem_univ _
  · intro r _ q _ heq
    exact Fin.ext (congrArg (fun k : Fin (N / 2) => k.val) heq)
  · intro r _
    refine ⟨⟨r.val, by have := r.isLt; omega⟩, ?_, rfl⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.succ_le_of_lt r.isLt
  · intro r _
    rfl

private def increment (N : ℕ+) (r : Fin ((N : ℕ) - 1)) : Fin (N : ℕ) :=
  ⟨r.val + 1, by have := r.isLt; omega⟩

private theorem increment_ne_zero (N : ℕ+) (r : Fin ((N : ℕ) - 1)) :
    increment N r ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change r.val + 1 = 0 at hv
  omega

private def incrementEquiv (N : ℕ+) :
    Fin ((N : ℕ) - 1) ≃ {r : Fin (N : ℕ) // r ≠ 0} where
  toFun r := ⟨increment N r, increment_ne_zero N r⟩
  invFun r := ⟨r.val.val - 1, by
    have := r.val.isLt
    have hr : r.val.val ≠ 0 := fun h => r.property (Fin.ext h)
    omega⟩
  left_inv r := Fin.ext (by simp [increment])
  right_inv r := by
    apply Subtype.ext
    apply Fin.ext
    have hr : r.val.val ≠ 0 := fun h => r.property (Fin.ext h)
    dsimp [increment]
    omega

private theorem endpoint_ne (N : ℕ+) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) - 1)) :
    i + increment N r ≠ i := by
  intro h
  apply increment_ne_zero N r
  exact add_left_cancel (h.trans (add_zero i).symm)

private theorem sum_pair_lengths (N : ℕ+)
    (F : (i : Fin (N : ℕ)) → {j : Fin (N : ℕ) // j ≠ i} → ℝ) :
    (∑ i, ∑ j, F i j) = ∑ r : Fin ((N : ℕ) - 1),
      ∑ i, F i ⟨i + increment N r, endpoint_ne N i r⟩ := by
  classical
  have hrow (i : Fin (N : ℕ)) : (∑ j, F i j) =
      ∑ r : Fin ((N : ℕ) - 1), F i ⟨i + increment N r, endpoint_ne N i r⟩ := by
    let e : {r : Fin (N : ℕ) // r ≠ 0} ≃ {j : Fin (N : ℕ) // j ≠ i} :=
      (Equiv.addLeft i).subtypeEquiv (fun r => by simp)
    exact ((incrementEquiv N).trans e).sum_comp (F i) |>.symm
  simp_rw [hrow]
  rw [Finset.sum_comm]

private theorem sum_pair_short_lengths (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (F : (i : Fin (N : ℕ)) → {j : Fin (N : ℕ) // j ≠ i} → ℝ)
    (hF : ∀ i j, F i j = F j.val ⟨i, Ne.symm j.property⟩) :
    (∑ i, ∑ j, F i j) = ∑ r : Fin ((N : ℕ) / 2),
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        ∑ i, F i ⟨i + increment N ⟨r.val, by have := r.isLt; omega⟩,
          endpoint_ne N i _⟩ := by
  rw [sum_pair_lengths]
  apply sum_reflected_lengths hN
  intro r
  let q : Fin ((N : ℕ) - 1) := ⟨(N : ℕ) - 2 - r.val, by have := r.isLt; omega⟩
  have hd : increment N q + increment N r = 0 := by
    apply Fin.ext
    change (((N : ℕ) - 2 - r.val + 1) + (r.val + 1)) % (N : ℕ) = 0
    have hr := r.isLt
    rw [show ((N : ℕ) - 2 - r.val + 1) + (r.val + 1) = (N : ℕ) by omega]
    exact Nat.mod_self _
  change (∑ i, F i ⟨i + increment N q, endpoint_ne N i q⟩) = _
  apply Finset.sum_bij (fun i _ => i + increment N q)
  · intro _ _
    exact Finset.mem_univ _
  · intro i _ j _ heq
    exact add_right_cancel heq
  · intro i _
    refine ⟨i + increment N r, Finset.mem_univ _, ?_⟩
    rw [add_assoc, add_comm (increment N r), hd, add_zero]
  · intro i _
    rw [hF]
    congr 1
    apply Subtype.ext
    change i = (i + increment N q) + increment N r
    rw [add_assoc, hd, add_zero]

/-- Cyclic interval sums are the library's microscopic forward separations. -/
theorem cyclicGapSum_gapVector {N : ℕ+} (X : Riesz1.Configuration N)
    (i : Fin (N : ℕ)) (r : ℕ) :
    cyclicGapSum N i r (gapVector X) = Riesz1.blockLength X i.val r := by
  rw [Riesz1.blockLength_eq_sum]
  unfold cyclicGapSum
  apply Finset.sum_congr rfl
  intro a _
  have hl : Riesz1.labelOf N ((i.val : ℤ) + a) =
      ⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
    apply Fin.ext
    apply (Nat.cast_injective (R := ℤ))
    rw [Riesz1.APG.labelOf_val]
    simp only [Int.natCast_mod, Int.natCast_add]
  change gapVector X _ = gap X _
  rw [gap_eq_gapVector_labelOf, hl]

/-- Actual positive gaps lie in the ambient physical-energy domain. -/
theorem gapVector_mem_gapAmbientDomain {N : ℕ+} (X : Riesz1.Configuration N) :
    WithLp.toLp 2 (gapVector X) ∈ gapAmbientDomain N := by
  intro i r hr hu
  change 0 < cyclicGapSum N i r (gapVector X) ∧
    cyclicGapSum N i r (gapVector X) < (N : ℝ)
  rw [cyclicGapSum_gapVector]
  have hNr : r < (N : ℕ) := by have := N.pos; omega
  have hpos := Riesz1.cyclicLift_strictMono X
    (show (i.val : ℤ) < i.val + r by omega)
  have hlt := Riesz1.cyclicLift_strictMono X
    (show (i.val : ℤ) + r < i.val + (N : ℕ) by exact_mod_cast Nat.add_lt_add_left hNr i.val)
  rw [Riesz1.cyclicLift_add_N] at hlt
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  change 0 < (N : ℝ) * (_ - _) ∧ (N : ℝ) * (_ - _) < N
  constructor
  · exact mul_pos hN (sub_pos.mpr hpos)
  · nlinarith

private theorem kernelAtParameters_even (p : Parameters)
    (x : {x : UnitAddCircle // x ≠ 0}) :
    kernelAtParameters p ⟨-x.val, neg_ne_zero.mpr x.property⟩ =
      kernelAtParameters p x := by
  unfold kernelAtParameters
  split_ifs
  · exact Riesz1.rieszRepresentative_neg _ _
  · exact shortKernel_even _ _

private def interaction (p : Parameters) {N : ℕ+} (X : Riesz1.Configuration N)
    (i : Fin (N : ℕ)) (j : {j : Fin (N : ℕ) // j ≠ i}) : ℝ :=
  kernelAtParameters p ⟨((X.val j.val - X.val i : ℝ) : UnitAddCircle),
    Riesz1.coe_sub_ne_zero_of_mem_orderedDomain X.property j.property⟩

private theorem interaction_symm (p : Parameters) {N : ℕ+} (X : Riesz1.Configuration N)
    (i : Fin (N : ℕ)) (j : {j : Fin (N : ℕ) // j ≠ i}) :
    interaction p X i j = interaction p X j.val ⟨i, Ne.symm j.property⟩ := by
  let x : {x : UnitAddCircle // x ≠ 0} :=
    ⟨((X.val i - X.val j.val : ℝ) : UnitAddCircle),
      Riesz1.coe_sub_ne_zero_of_mem_orderedDomain X.property (Ne.symm j.property)⟩
  have he : (⟨((X.val j.val - X.val i : ℝ) : UnitAddCircle),
      Riesz1.coe_sub_ne_zero_of_mem_orderedDomain X.property j.property⟩ :
        {x : UnitAddCircle // x ≠ 0}) = ⟨-x.val, neg_ne_zero.mpr x.property⟩ := by
    apply Subtype.ext
    change ((X.val j.val - X.val i : ℝ) : UnitAddCircle) =
      -((X.val i - X.val j.val : ℝ) : UnitAddCircle)
    rw [← AddCircle.coe_neg, neg_sub]
  exact (congrArg (kernelAtParameters p) he).trans (kernelAtParameters_even p x)

private theorem energy_eq_interaction (p : Parameters) {N : ℕ+}
    (X : Riesz1.Configuration N) :
    energy p X = (N : ℝ) ^ (-p.val.2) * ∑ i, ∑ j, interaction p X i j := by
  have hr (i : Fin (N : ℕ)) (j : {j : Fin (N : ℕ) // j ≠ i}) :
      interaction p X i j = kernelAtParameters p
        ⟨((X.val i - X.val j.val : ℝ) : UnitAddCircle),
          Riesz1.coe_sub_ne_zero_of_mem_orderedDomain X.property (Ne.symm j.property)⟩ := by
    rw [interaction_symm]
    rfl
  simp_rw [hr]
  unfold energy
  split_ifs with hs
  · unfold Riesz1.energy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [kernelAtParameters, hs, dite_true, Riesz1.rieszKernel]
    exact Finset.sum_subtype (Finset.univ.erase i) (fun j => by simp) _
  · unfold shortEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [kernelAtParameters, hs, dite_false]
    exact (shortKernel_coe _ _).symm

/-- The forward interval has the actual circle separation of its endpoints. -/
theorem circle_cyclicGapSum {N : ℕ+} (X : Riesz1.Configuration N)
    (i : Fin (N : ℕ)) (r : ℕ) :
    ((cyclicGapSum N i r (gapVector X) / (N : ℝ) : ℝ) : UnitAddCircle) =
      ((X.val ⟨(i.val + r) % (N : ℕ), Nat.mod_lt _ N.pos⟩ - X.val i : ℝ) :
        UnitAddCircle) := by
  rw [cyclicGapSum_gapVector]
  unfold Riesz1.blockLength
  rw [mul_div_cancel_left₀ _ (show (N : ℝ) ≠ 0 by exact_mod_cast N.ne_zero)]
  have hl : Riesz1.labelOf N ((i.val : ℤ) + r) =
      ⟨(i.val + r) % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
    apply Fin.ext
    apply (Nat.cast_injective (R := ℤ))
    rw [Riesz1.APG.labelOf_val]
    simp only [Int.natCast_mod, Int.natCast_add]
  have hL := Riesz1.APG.cyclicLift_labelOf X ((i.val : ℤ) + r)
  rw [Riesz1.cyclicLift_natCast, hl] at hL
  rw [hL, Riesz1.cyclicLift_natCast]
  have hz (q : ℤ) : (((q : ℝ) : UnitAddCircle)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨q, by simp⟩
  simp only [AddCircle.coe_sub, AddCircle.coe_add, hz, add_zero]

/-- See Subsection 1.7 of the paper: the short-interval physical gap energy
is exactly the particle energy. Both exponent regimes, the ordered-pair
normalization and the antipodal coefficient are included. -/
theorem physicalAmbientGapEnergy_gapVector (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (X : Riesz1.Configuration N) :
    physicalAmbientGapEnergy p N
      ⟨WithLp.toLp 2 (gapVector X), gapVector_mem_gapAmbientDomain X⟩ = energy p X := by
  symm
  rw [energy_eq_interaction, sum_pair_short_lengths N hN _ (interaction_symm p X)]
  unfold physicalAmbientGapEnergy
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold interaction
  apply congrArg (kernelAtParameters p)
  apply Subtype.ext
  change ((X.val (i + increment N ⟨r.val, by have := r.isLt; omega⟩) - X.val i : ℝ) :
      UnitAddCircle) =
    ((cyclicGapSum N i (r.val + 1) (gapVector X) / (N : ℝ) : ℝ) : UnitAddCircle)
  rw [circle_cyclicGapSum]
  rfl

/-- Completing the first `n` gaps recovers their entire period. -/
theorem gapVector_eq_chart (n : ℕ) (X : Riesz1.Configuration n.succPNat) :
    WithLp.toLp 2 (gapVector X) =
      AffineSimplex.chart n (n + 1) (WithLp.toLp 2 (gaps n X).val) := by
  have hv : gapVector X = Riesz1.anchoredGapVector n (Riesz1.anchorCoords n X.val).2 :=
    Riesz1.gapVector_eq_anchoredGapVector n X
  have hc : (gaps n X).val = difference n (Riesz1.anchorCoords n X.val).2 :=
    congrArg Prod.snd (coordinates_eq n X)
  rw [hc]
  rw [hv]
  exact (completion_difference n (Riesz1.anchorCoords n X.val).2).symm

theorem gaps_reconstruct (n : ℕ) (y : Domain n) : gaps n (reconstruct n y) = y := by
  apply Subtype.ext
  exact congrArg Prod.snd (coordinates_inverse n (0, y.val) ⟨by norm_num, y.property⟩)

/-- The deleted-coordinate chart, certified in the physical domain. -/
def ambientPoint (n : ℕ) (y : Domain n) :
    {y : EuclideanSpace ℝ (Fin (n.succPNat : ℕ)) // y ∈ gapAmbientDomain n.succPNat} :=
  ⟨AffineSimplex.chart n (n + 1) (WithLp.toLp 2 y.val), by
    have h := gapVector_mem_gapAmbientDomain (reconstruct n y)
    rw [gapVector_eq_chart, gaps_reconstruct] at h
    exact h⟩

theorem ambientPoint_gaps (n : ℕ) (X : Riesz1.Configuration n.succPNat) :
    (ambientPoint n (gaps n X)).val = WithLp.toLp 2 (gapVector X) :=
  (gapVector_eq_chart n X).symm

theorem measurable_ambientPoint (n : ℕ) : Measurable (ambientPoint n) := by
  apply Measurable.subtype_mk
  exact (AffineSimplex.continuous_chart n (n + 1)).measurable.comp
    ((PiLp.volume_preserving_toLp (Fin n)).measurable.comp measurable_subtype_coe)

/-- The inverse-chart Gibbs weight is the exponential of the physical
gap energy, with exactly the source temperature and ordered-pair normalization. -/
theorem weight_eq_physical (p : Parameters) (n : ℕ) (hn : 1 ≤ n) (y : Domain n) :
    weight p n y = ENNReal.ofReal (Real.exp
      (-p.val.1 * physicalAmbientGapEnergy p n.succPNat (ambientPoint n y))) := by
  have h := physicalAmbientGapEnergy_gapVector p n.succPNat (by
    simp only [Nat.succPNat_coe]; omega) (reconstruct n y)
  have he : (⟨WithLp.toLp 2 (gapVector (reconstruct n y)),
      gapVector_mem_gapAmbientDomain (reconstruct n y)⟩ :
        {y : EuclideanSpace ℝ (Fin (n.succPNat : ℕ)) // y ∈ gapAmbientDomain n.succPNat}) =
      ambientPoint n y := by
    apply Subtype.ext
    exact (gapVector_eq_chart n (reconstruct n y)).trans
      (congrArg (fun z : Domain n => AffineSimplex.chart n (n + 1)
        (WithLp.toLp 2 z.val)) (gaps_reconstruct n y))
  have hfinal : physicalAmbientGapEnergy p n.succPNat (ambientPoint n y) =
      energy p (reconstruct n y) :=
    (congrArg (physicalAmbientGapEnergy p n.succPNat) he).symm.trans h
  unfold weight
  rw [hfinal]

/-- See Subsection 1.7 of the paper: the finite gap density is the normalized physical
exponential in the exact free-coordinate chart, for both exponent regimes. -/
theorem map_gibbsMeasure_gaps_physical_density (p : Parameters) (n : ℕ) (hn : 1 ≤ n) :
    (gibbsMeasure p n.succPNat).map (gaps n) =
      (partitionFunction p n.succPNat)⁻¹ •
        ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
          (coordinateVolume n).withDensity (fun y => ENNReal.ofReal (Real.exp
            (-p.val.1 * physicalAmbientGapEnergy p n.succPNat (ambientPoint n y)))) := by
  rw [map_gibbsMeasure_gaps_density]
  congr 2
  congr 1
  exact funext (weight_eq_physical p n hn)

/-- The full gap law is the image of the density in its first `n` coordinates. -/
theorem gapLaw_eq_map_gaps (p : Parameters) (n : ℕ) :
    gapLaw p n.succPNat = ((gibbsMeasure p n.succPNat).map (gaps n)).map
      (fun y => WithLp.ofLp (ambientPoint n y).val) := by
  have hF : Measurable (fun y : Domain n => WithLp.ofLp (ambientPoint n y).val) :=
    (PiLp.volume_preserving_ofLp (Fin (n + 1))).measurable.comp
      (measurable_subtype_coe.comp (measurable_ambientPoint n))
  rw [Measure.map_map hF (measurable_gaps n)]
  unfold gapLaw
  congr 1
  funext X
  exact congrArg WithLp.ofLp (ambientPoint_gaps n X).symm

/-- The rotation coordinate is independent and uniform jointly with the literal
full gap vector (Subsection 1.7, density consequence). -/
theorem map_rotation_gapVector (p : Parameters) (n : ℕ) :
    (gibbsMeasure p n.succPNat).map (fun X => (X.val 0, gapVector X)) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (gapLaw p n.succPNat) := by
  let := gibbsMeasure_probability p n.succPNat
  have hcoords : (gibbsMeasure p n.succPNat).map (fun X => (X.val 0, gaps n X)) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod
        ((gibbsMeasure p n.succPNat).map (gaps n)) := by
    rw [map_gibbsMeasure_coordinates_density, map_gibbsMeasure_gaps_density]
  let F : Domain n → (Fin (n.succPNat : ℕ) → ℝ) :=
    fun y => WithLp.ofLp (ambientPoint n y).val
  have hF : Measurable F := (PiLp.volume_preserving_ofLp (Fin (n + 1))).measurable.comp
    (measurable_subtype_coe.comp (measurable_ambientPoint n))
  have hJ : Measurable (fun X : Riesz1.Configuration n.succPNat => (X.val 0, gaps n X)) :=
    ((measurable_pi_apply 0).comp measurable_subtype_coe).prodMk (measurable_gaps n)
  have h := congrArg (Measure.map (Prod.map (id : ℝ → ℝ) F)) hcoords
  have hlaw : ((gibbsMeasure p n.succPNat).map (gaps n)).map F = gapLaw p n.succPNat :=
    (gapLaw_eq_map_gaps p n).symm
  rw [Measure.map_map (measurable_id.prodMap hF) hJ,
    ← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id, hlaw] at h
  have heq : Prod.map (id : ℝ → ℝ) F ∘ (fun X => (X.val 0, gaps n X)) =
      (fun X : Riesz1.Configuration n.succPNat => (X.val 0, gapVector X)) := by
    funext X
    refine Prod.ext rfl ?_
    exact congrArg WithLp.ofLp (ambientPoint_gaps n X)
  rw [heq] at h
  exact h

/-- See Subsection 1.7 of the paper: the particle-volume gap factor relative to intrinsic
Euclidean Hausdorff measure is exactly `N^{-(N-1)} N^{-1/2}`. -/
theorem map_configurationVolume_intrinsic (n : ℕ) :
    (Riesz1.configurationVolume n.succPNat).map
      (fun X : Riesz1.Configuration n.succPNat => (X.val 0, (WithLp.toLp 2 (gapVector X) :
        EuclideanSpace ℝ (Fin (n + 1))))) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod
        (ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
          (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ •
            AffineSimplex.simplexVolume n (n + 1)) := by
  let F : (Fin n → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y => WithLp.toLp 2 (fun i : Fin (n + 1) => Riesz1.anchoredGapVector n y i)
  have hF : Measurable F :=
    (PiLp.volume_preserving_toLp (Fin (n + 1))).measurable.comp
      (Riesz1.measurable_anchoredGapVector n)
  have hfun : (fun X : Riesz1.Configuration n.succPNat =>
      (X.val 0, (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (n + 1))))) =
      Prod.map id F ∘ (fun X => Riesz1.anchorCoords n X.val) := by
    funext X
    refine Prod.ext rfl ?_
    exact congrArg (fun y : Fin (n.succPNat : ℕ) → ℝ => WithLp.toLp 2 y)
      (Riesz1.gapVector_eq_anchoredGapVector n X)
  rw [hfun, ← Measure.map_map (measurable_id.prodMap hF)
    (Riesz1.measurable_anchorCoords_config n), Riesz1.map_anchorCoords_configurationVolume,
    ← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id]
  congr 1
  have hbase := map_toLp_gapSimplexVolume n
  rw [Riesz1.gapSimplexVolume, Measure.map_map
    (PiLp.volume_preserving_toLp (Fin (n + 1))).measurable
    (Riesz1.measurable_anchoredGapVector n)] at hbase
  exact hbase

/-- See Subsection 1.7 of the paper, assembled in one statement. The size is `N=n+1`,
and `hn` is exactly `N≥2`. The parameter subtype covers both exponent
regimes. The last two clauses give the independent rotation and physical Gibbs
density requested by the finite-chart package. -/
theorem finite_gap_chart (p : Parameters) (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (coordinates n) ∧
    range (coordinates n) = Ico (0 : ℝ) 1 ×ˢ
      ((WithLp.toLp 2) ⁻¹' AffineSimplex.chartDomain n (n + 1)) ∧
    (∀ X : Riesz1.Configuration n.succPNat, inverse n (coordinates n X) = X.val) ∧
    (∀ (q : ℝ × (Fin n → ℝ)) (i : Fin (n + 1)), inverse n q i = q.1 +
      Fin.partialSum (WithLp.ofLp
        (AffineSimplex.chart n (n + 1) (WithLp.toLp 2 q.2))) i.castSucc / (n + 1 : ℝ)) ∧
    (∀ X : Riesz1.Configuration n.succPNat,
      physicalAmbientGapEnergy p n.succPNat
        ⟨WithLp.toLp 2 (gapVector X), gapVector_mem_gapAmbientDomain X⟩ = energy p X) ∧
    (Riesz1.configurationVolume n.succPNat).map (coordinates n) =
      ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
        ((volume.restrict (Ico (0 : ℝ) 1)).prod
          (volume.restrict ((WithLp.toLp 2) ⁻¹'
            AffineSimplex.chartDomain n (n + 1)))) ∧
    (Riesz1.configurationVolume n.succPNat).map
      (fun X : Riesz1.Configuration n.succPNat => (X.val 0, (WithLp.toLp 2 (gapVector X) :
        EuclideanSpace ℝ (Fin (n + 1))))) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod
        (ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
          (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ •
            AffineSimplex.simplexVolume n (n + 1)) ∧
    (gibbsMeasure p n.succPNat).map (fun X => (X.val 0, gapVector X)) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (gapLaw p n.succPNat) ∧
    (gibbsMeasure p n.succPNat).map (gaps n) =
      (partitionFunction p n.succPNat)⁻¹ • ENNReal.ofReal ((n + 1 : ℝ) ^ n)⁻¹ •
        (coordinateVolume n).withDensity (fun y => ENNReal.ofReal (Real.exp
          (-p.val.1 * physicalAmbientGapEnergy p n.succPNat (ambientPoint n y)))) := by
  exact ⟨coordinates_injective n, coordinates_range n, inverse_coordinates n,
    inverse_apply n, physicalAmbientGapEnergy_gapVector p n.succPNat (by
      simp only [Nat.succPNat_coe]; omega), map_configurationVolume_coordinates n,
    map_configurationVolume_intrinsic n, map_rotation_gapVector p n,
    map_gibbsMeasure_gaps_physical_density p n hn⟩

end GapChart
end Riesz2
