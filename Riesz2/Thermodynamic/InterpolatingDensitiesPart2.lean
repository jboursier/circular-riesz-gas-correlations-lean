/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolatingDensities
public import Riesz2.Thermodynamic.IntegratedCovariance

/-!
# Exterior disintegration of the two-sided physical tilt

See Subsection 6.1 of the paper. The base of the retained chart is the whole exterior,
and its fibre consists of all but one active gap. The normalized fibre is transported to
the existing Hausdorff simplex measure. Penalties are allowed on arbitrary labels,
including the omitted active coordinate.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz2.InterpolatingDensities

/-- The specified chart places the whole exterior in the base and the
first `m+1` physical gaps in the fibre. This is the block swap, with the
last active gap serving as the deleted coordinate. -/
def exteriorPermutation (n m : ℕ) : Equiv.Perm (Fin (n + m + 1)) :=
  (finAddFlip : Fin (n + (m + 1)) ≃ Fin ((m + 1) + n)).trans (finCongr (by omega))

/-- Exterior base labels in the fixed chart are the original final labels. -/
theorem exteriorPermutation_retained (n m : ℕ) (i : Fin n) :
    exteriorPermutation n m (i.castAdd m).castSucc =
      ⟨m + 1 + i.val, by omega⟩ := by
  apply Fin.ext
  simp only [exteriorPermutation, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  change (finAddFlip (i.castAdd (m + 1))).val = _
  rw [finAddFlip_apply_castAdd]
  rfl

/-- Active fibre labels in the fixed chart are the original first labels. -/
theorem exteriorPermutation_active (n m : ℕ) (i : Fin (m + 1))
    (h : m + 1 ≤ n + m + 1) :
    exteriorPermutation n m (i.natAdd n) = Fin.castLE h i := by
  apply Fin.ext
  simp only [exteriorPermutation, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rw [finAddFlip_apply_natAdd]
  rfl

/-- Reconstruction in the exterior chart preserves every active gap literally. -/
theorem assemble_exterior_active (n m : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin (m + 1)))
    (i : Fin (m + 1)) (h : m + 1 ≤ n + m + 1) :
    RetainedSimplex.assemble n m (exteriorPermutation n m) x u (Fin.castLE h i) = u i := by
  rw [← exteriorPermutation_active n m i h]
  change RetainedSimplex.join n (m + 1) (x, u)
    ((exteriorPermutation n m).symm (exteriorPermutation n m (i.natAdd n))) = _
  rw [Equiv.symm_apply_apply, RetainedSimplex.join_right]

/-- The first-block penalty in the exterior chart is exactly the
two-sided active penalty of Subsection 6.1. -/
theorem exterior_penalty (n m : ℕ) (θ : PhysicalCutoff) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin (m + 1)))
    (h : m + 1 ≤ n + m + 1) :
    (∑ i ∈ Finset.univ.map (Fin.castLEEmb h),
      (θ.val (a * RetainedSimplex.assemble n m (exteriorPermutation n m) x u i) +
        θ.val (a * (RetainedSimplex.assemble n m (exteriorPermutation n m) x u i)⁻¹))) =
      ∑ i, (θ.val (a * u i) + θ.val (a * (u i)⁻¹)) := by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.castLEEmb_apply, assemble_exterior_active]

/-- The physical penalized chart density has exactly the same positive support
as the unpenalized chart density, even when the penalty acts in the fibre. -/
theorem penalized_chart_support (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ProperMarginalChart.penalizedChartDensity p n m σ θ a J b q = 0 ↔
      ProperMarginalChart.chartDensity p n m σ q = 0 := by
  classical
  by_cases hq : q ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  · simp only [ProperMarginalChart.penalizedChartDensity,
      ProperMarginalChart.chartDensity, indicator_of_mem hq,
      ProperMarginalChart.penalizedDensity, mul_eq_zero,
      ENNReal.ofReal_eq_zero, not_le.mpr (Real.exp_pos _), or_false]
  · simp only [ProperMarginalChart.penalizedChartDensity,
      ProperMarginalChart.chartDensity, indicator_of_notMem hq]

/-- A nonnegative physical penalty decreases the unnormalized density. -/
theorem penalized_chart_le (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 ≤ a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ProperMarginalChart.penalizedChartDensity p n m σ θ a J b q ≤
      ProperMarginalChart.chartDensity p n m σ q := by
  classical
  by_cases hq : q ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  · have hs := (RetainedSimplex.chart_mem_simplex n m _ σ q).mpr hq
    have hp : 0 ≤ ∑ i ∈ J,
        (θ.val (a * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q i) +
          if b then θ.val (a * (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q i)⁻¹)
          else 0) := by
      apply Finset.sum_nonneg
      intro i _
      apply add_nonneg (θ.property.2.2.1 _ (mul_nonneg ha (hs.1 i).le))
      split_ifs
      · exact θ.property.2.2.1 _ (mul_nonneg ha (inv_nonneg.mpr (hs.1 i).le))
      · exact le_rfl
    have he : ENNReal.ofReal (Real.exp (-p.val.1 * ∑ i ∈ J,
        (θ.val (a * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q i) +
          if b then θ.val (a * (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q i)⁻¹)
          else 0))) ≤ 1 := by
      exact (ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le) hp))).trans_eq
          (by simp)
    simp only [ProperMarginalChart.penalizedChartDensity,
      ProperMarginalChart.chartDensity, indicator_of_mem hq,
      ProperMarginalChart.penalizedDensity]
    exact (mul_le_mul_right he _).trans_eq (mul_one _)
  · simp only [ProperMarginalChart.penalizedChartDensity,
      ProperMarginalChart.chartDensity, indicator_of_notMem hq, le_refl]

/-- See Subsection 6.1 of the paper, pointwise positive finite conditional mass. Unlike
the exterior law conditioned on active gaps, this permits penalties on the
integrated active gaps themselves. -/
theorem penalized_fibre_mass (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    AffineFibre.fibreMass volume
      (ProperMarginalChart.penalizedChartDensity p n m σ θ a J b) x ≠ 0 ∧
      AffineFibre.fibreMass volume
        (ProperMarginalChart.penalizedChartDensity p n m σ θ a J b) x ≠ ∞ := by
  obtain ⟨h0, ht⟩ := ProperMarginalChart.fibre_mass p n m hn σ hx
  have he : (fun z => ProperMarginalChart.penalizedChartDensity p n m σ θ a J b (x, z))
      =ᵐ[volume] 0 ↔
      (fun z => ProperMarginalChart.chartDensity p n m σ (x, z)) =ᵐ[volume] 0 := by
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun z => penalized_chart_support p n m σ θ a J b (x, z)
  have hw := (ProperMarginalChart.measurable_penalizedChartDensity p n m σ θ ha J b).comp
    (measurable_prodMk_left (x := x))
  have hv := (ProperMarginalChart.measurable_chartDensity p n m σ).comp
    (measurable_prodMk_left (x := x))
  refine ⟨?_, ?_⟩
  · intro hh
    exact h0 ((lintegral_eq_zero_iff hv).mpr
      (he.mp ((lintegral_eq_zero_iff hw).mp hh)))
  · exact ne_top_of_le_ne_top ht
      (lintegral_mono fun z => penalized_chart_le p n m σ θ ha.le J b (x, z))

/-- The two-sided tilt on an active fibre, using the existing normalized
product-density kernel. Its base is the positive exterior carrier. -/
def penalizedFibreKernel (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    Kernel (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (EuclideanSpace ℝ (Fin m)) :=
  AffineFibre.normalizedKernel volume
    ((ProperMarginalChart.measurable_penalizedChartDensity p n m σ θ ha J b).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (fun x => (penalized_fibre_mass p n m hn σ θ ha J b x.property).1)
    (fun x => (penalized_fibre_mass p n m hn σ θ ha J b x.property).2)

instance penalizedFibreKernel_markov (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    IsMarkovKernel (penalizedFibreKernel p n m hn σ θ ha J b) := by
  unfold penalizedFibreKernel
  infer_instance

/-- See Subsection 6.1 of the paper: the physical two-sided density disintegrates over
the full exterior, with a measurable probability kernel on every positive
compatible exterior. The reference base volume is restricted to its actual
carrier. No conditional probability is assigned at impossible exteriors. -/
theorem penalized_product_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    (volume.prod volume).withDensity
        (ProperMarginalChart.penalizedChartDensity p n m σ θ a J b) =
      ((((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin n))).withDensity
        (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => AffineFibre.fibreMass volume
          (ProperMarginalChart.penalizedChartDensity p n m σ θ a J b) x.val)) ⊗ₘ
        penalizedFibreKernel p n m hn σ θ ha J b).map (fun q => (q.1.val, q.2)) := by
  rw [AffineFibre.withDensity_eq_map_subtypeProd volume volume
    (AffineSimplex.isOpen_chartDomain n ((n + m : ℕ) + 1)).measurableSet
    (ProperMarginalChart.measurable_penalizedChartDensity p n m σ θ ha J b) ?_]
  · congr 1
    exact AffineFibre.withDensity_eq_compProd volume _ _ _ _
  · intro x hx z
    have hq : (x, z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
      intro hh
      apply hx
      rw [← RetainedSimplex.fst_image_domain n m ((n + m : ℕ) + 1)]
      exact ⟨(x, z), hh, rfl⟩
    exact indicator_of_notMem hq _

/-- See Subsection 6.1 of the paper: the normalized coordinate fibre
is exactly the density relative to intrinsic Hausdorff measure at its varying
length `N - ∑ y`. The positive constant area factor cancels. -/
theorem penalized_fibre_hausdorff (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let L := ((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i
    let w := fun u => ProperMarginalChart.penalizedDensity p (n + m) θ a J b
      (RetainedSimplex.assemble n m σ x.val u)
    ∃ h0 ht,
      AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume m L) w h0 ht =
        (penalizedFibreKernel p n m hn σ θ ha J b x).map (AffineSimplex.chart m L) := by
  intro L w
  have hw : Measurable w :=
    (ProperMarginalChart.measurable_penalizedDensity p (n + m) θ ha J b).comp
      (RetainedSimplex.continuous_assemble n m σ x.val).measurable
  have he : (fun z => ProperMarginalChart.penalizedChartDensity p n m σ θ a J b (x.val, z)) =
      (AffineSimplex.chartDomain m L).indicator (fun z => w (AffineSimplex.chart m L z)) := by
    funext z
    have hdom : (x.val, z) ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1) ↔
        z ∈ AffineSimplex.chartDomain m L := by
      exact Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z
    by_cases hz : z ∈ AffineSimplex.chartDomain m L
    · simp only [ProperMarginalChart.penalizedChartDensity, indicator_of_mem (hdom.mpr hz),
        indicator_of_mem hz, w, L, RetainedSimplex.assemble_chart]
    · simp only [ProperMarginalChart.penalizedChartDensity,
        indicator_of_notMem (fun h => hz (hdom.mp h)), indicator_of_notMem hz]
  obtain ⟨h0, ht⟩ := penalized_fibre_mass p n m hn σ θ ha J b x.property
  have hm : AffineFibre.fibreMass volume
      (ProperMarginalChart.penalizedChartDensity p n m σ θ a J b) x.val =
      ∫⁻ z in AffineSimplex.chartDomain m L, w (AffineSimplex.chart m L z) := by
    unfold AffineFibre.fibreMass
    rw [he, lintegral_indicator (AffineSimplex.isOpen_chartDomain m L).measurableSet]
  rw [hm] at h0 ht
  refine ⟨_, _, (AffineFibre.SumChart.normalizedMeasure_simplexVolume m L hw h0 ht).trans ?_⟩
  congr 1
  change _ = AffineFibre.normalizedMeasure volume
    (fun z => ProperMarginalChart.penalizedChartDensity p n m σ θ a J b (x.val, z)) _ _
  simpa only [AffineFibre.normalizedMeasure_eq_smul, he] using
    (AffineFibre.normalizedMeasure_indicator volume
      (AffineSimplex.isOpen_chartDomain m L).measurableSet _ h0 ht).symm

/-- Joint continuity of the varying-length deleted-coordinate chart. -/
theorem continuous_fibre_chart (n m : ℕ) (M : ℝ) :
    Continuous (fun q : AffineSimplex.chartDomain n M × EuclideanSpace ℝ (Fin m) =>
      AffineSimplex.chart m (M - ∑ i, q.1.val i) q.2) := by
  exact (AffineFibre.SumChart.totalChart m).continuous.comp
    ((continuous_const.sub (continuous_finsetSum _ fun i _ =>
      (PiLp.continuous_apply 2 _ i).comp (continuous_subtype_val.comp continuous_fst))).prodMk
        continuous_snd)

/-- The fixed-exterior conditional kernel on all active gaps, including the
omitted one. Its changing mass is determined by the exterior itself. -/
def simplexFibreKernel (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    Kernel (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (EuclideanSpace ℝ (Fin (m + 1))) where
  toFun x := (penalizedFibreKernel p n m hn σ θ ha J b x).map
    (AffineSimplex.chart m (((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i))
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    have h := Kernel.measurable_kernel_prodMk_left
      (κ := penalizedFibreKernel p n m hn σ θ ha J b)
      ((continuous_fibre_chart n m ((n + m : ℕ) + 1)).measurable hs)
    convert h using 1
    funext x
    exact Measure.map_apply
      (AffineSimplex.continuous_chart m _).measurable hs

instance simplexFibreKernel_markov (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    IsMarkovKernel (simplexFibreKernel p n m hn σ θ ha J b) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure ((penalizedFibreKernel p n m hn σ θ ha J b x).map _)
    exact (Measure.isProbabilityMeasure_map_iff
      (AffineSimplex.continuous_chart m _).measurable.aemeasurable).mpr inferInstance

/-- See Subsection 6.1 of the paper, finite positive Hausdorff normalization and exact
conditional density on the active simplex of length `N - ∑ y`. -/
theorem simplexFibreKernel_density (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let L := ((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i
    let w := fun u => ProperMarginalChart.penalizedDensity p (n + m) θ a J b
      (RetainedSimplex.assemble n m σ x.val u)
    (0 < L) ∧ ∃ h0 ht,
      simplexFibreKernel p n m hn σ θ ha J b x =
        AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume m L) w h0 ht := by
  refine ⟨sub_pos.mpr x.property.2, ?_⟩
  obtain ⟨h0, ht, he⟩ := penalized_fibre_hausdorff p n m hn σ θ ha J b x
  exact ⟨h0, ht, he.symm⟩

/-- See Subsection 6.1 of the paper, disintegration of the actual tilted
particle law. In particular, retaining every exterior gap and integrating
the free active coordinates gives its active conditional. There is no
requirement that penalized coordinates be retained. -/
theorem tilted_coordinates_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (r : ℕ+)
    (hr : (r : ℕ) ≤ ((n + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    (tiltedParticleMeasure p (n + m).succPNat r hr θ ε b).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (tiltNormalizer p (n + m).succPNat r hr θ ε b)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            ((((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
              ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
                EuclideanSpace ℝ (Fin n))).withDensity
                  (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
                    AffineFibre.fibreMass volume
                      (ProperMarginalChart.penalizedChartDensity p n m σ θ ((r : ℝ) ^ (-ε))
                        (Finset.univ.map (Fin.castLEEmb hr)) b) x.val)) ⊗ₘ
              penalizedFibreKernel p n m hn σ θ
                (Real.rpow_pos_of_pos (show (0 : ℝ) < r by exact_mod_cast r.pos) (-ε))
                (Finset.univ.map (Fin.castLEEmb hr)) b).map (fun q => (q.1.val, q.2)) := by
  rw [ProperMarginalChart.map_tiltedParticleMeasure_coordinates p n m hn σ r hr θ ε b]
  exact congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) =>
    (tiltNormalizer p (n + m).succPNat r hr θ ε b)⁻¹ •
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ • μ)
    (penalized_product_disintegration p n m hn σ θ (Real.rpow_pos_of_pos
      (show (0 : ℝ) < r by exact_mod_cast r.pos) (-ε)) _ b)

/-- Every compatible positive active fibre assembles into the actual full
mass simplex in the exterior-first chart. -/
theorem assemble_exterior_mem (n m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (u : EuclideanSpace ℝ (Fin (m + 1)))
    (hu : u ∈ AffineSimplex.massSimplex m (((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i)) :
    RetainedSimplex.assemble n m (exteriorPermutation n m) x.val u ∈
      AffineSimplex.massSimplex (n + m) ((n + m : ℕ) + 1) := by
  let L := ((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i
  have hi := AffineSimplex.chart_coordinates m L hu.2
  have hc : AffineSimplex.coordinates m u ∈ AffineSimplex.chartDomain m L :=
    (AffineSimplex.chart_mem_simplex_iff m L _).mp (hi.symm ▸ hu)
  have hd : (x.val, AffineSimplex.coordinates m u) ∈
      RetainedSimplex.domain n m ((n + m : ℕ) + 1) :=
    (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) _).mpr hc
  have hh := (RetainedSimplex.chart_mem_simplex n m _ (exteriorPermutation n m) _).mpr hd
  rw [← RetainedSimplex.assemble_chart, hi] at hh
  exact hh

/-- See Subsection 6.1 of the paper: the fibre weight is the exact physical energy
plus the two-sided first-block penalty, including at the omitted active
coordinate. No exterior penalty or replacement energy is inserted. -/
theorem exterior_fibre_weight (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (a : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (u : EuclideanSpace ℝ (Fin (m + 1)))
    (hu : u ∈ AffineSimplex.massSimplex m (((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i))
    (h : m + 1 ≤ n + m + 1) :
    ProperMarginalChart.penalizedDensity p (n + m) θ a
      (Finset.univ.map (Fin.castLEEmb h)) true
      (RetainedSimplex.assemble n m (exteriorPermutation n m) x.val u) =
      ENNReal.ofReal (Real.exp (-p.val.1 *
        (physicalAmbientGapEnergy p (n + m).succPNat
          ⟨RetainedSimplex.assemble n m (exteriorPermutation n m) x.val u,
            ProperMarginalChart.simplex_ambient _ (assemble_exterior_mem n m x u hu)⟩ +
          ∑ i, (θ.val (a * u i) + θ.val (a * (u i)⁻¹))))) := by
  classical
  rw [ProperMarginalChart.penalizedDensity, ProperMarginalChart.density,
    dite_eq_left (assemble_exterior_mem n m x u hu)]
  simp only [ite_true]
  rw [exterior_penalty n m θ a x.val u h,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- See Subsection 6.1 of the paper, all clauses. The specified exterior chart
disintegrates the two-sided tilted law, with positive finite
Hausdorff-normalized conditional densities on every compatible exterior.
Every pair of compatible positive exteriors at this active size has the
closed intrinsic scalar/vector realizations, positive tangent Hessian and
Helffer--Sjöstrand covariance interface. No typicality premise occurs. -/
theorem conditional_laws (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε) :
    let r := m.succPNat
    let hr : (r : ℕ) ≤ ((n + m).succPNat : ℕ) := by
      change m + 1 ≤ n + m + 1
      omega
    let a := (r : ℝ) ^ (-ε)
    let ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast r.pos) (-ε)
    let σ := exteriorPermutation n m
    let J := Finset.univ.map (Fin.castLEEmb hr)
    let B := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let μ : Measure B := volume.comap Subtype.val
    ((tiltedParticleMeasure p (n + m).succPNat r hr θ ε true).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (tiltNormalizer p (n + m).succPNat r hr θ ε true)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            (μ.withDensity (fun x => AffineFibre.fibreMass volume
              (ProperMarginalChart.penalizedChartDensity p n m σ θ a J true) x.val) ⊗ₘ
              penalizedFibreKernel p n m hn σ θ ha J true).map (fun q => (q.1.val, q.2))) ∧
    (∀ x : B,
      let L := ((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i
      let w := fun u => ProperMarginalChart.penalizedDensity p (n + m) θ a J true
        (RetainedSimplex.assemble n m σ x.val u)
      0 < L ∧ ∃ h0 ht, simplexFibreKernel p n m hn σ θ ha J true x =
        AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume m L) w h0 ht) ∧
    ∀ k l : ℕ,
      ∀ (σ' : Equiv.Perm (Fin ((m + 1) + k + 1)))
        (τ' : Equiv.Perm (Fin ((m + 1) + l + 1))) (L : ℝ) (_hL : 0 < L)
        (y : EuclideanSpace ℝ (Fin (k + 1))) (hy : ∀ j, 0 < y j)
        (z : EuclideanSpace ℝ (Fin (l + 1))) (hz : ∀ j, 0 < z j)
        (hcompatY : L + ∑ j, y j = ((m + 1 + k : ℕ) + 1 : ℝ))
        (hcompatZ : L + ∑ j, z j = ((m + 1 + l : ℕ) + 1 : ℝ)),
      let Ω := AffineSimplex.centredChart m L ⁻¹' AffineSimplex.massSimplex m L
      let P := fun w : AffineSimplex.Tangent m => ∑ i,
        (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * AffineSimplex.centredChart m L w i) +
          θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (AffineSimplex.centredChart m L w i)⁻¹))
      ∃ Ky Kz : AffineSimplex.Tangent m → ℝ,
        (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (m + 1 + k).succPNat
          ⟨RetainedSimplex.assemble (m + 1) k σ' (AffineSimplex.centredChart m L w) y,
            PhysicalEnergy.simplex_subset_ambient _ _ (by
              have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem m k σ' y
                hy hcompatY hw
              rw [AffineSimplex.massSimplex_physical] at hh
              exact hh)⟩) ∧
        (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (m + 1 + l).succPNat
          ⟨RetainedSimplex.assemble (m + 1) l τ' (AffineSimplex.centredChart m L w) z,
            PhysicalEnergy.simplex_subset_ambient _ _ (by
              have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem m l τ' z
                hz hcompatZ hw
              rw [AffineSimplex.massSimplex_physical] at hh
              exact hh)⟩) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
          let V := fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
          ∃ ρ : Measure (AffineSimplex.Tangent m),
            IsEuclideanGibbsPotential volume ρ Ω V ∧
            (∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent m,
              (2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 ≤
                fderiv ℝ (fderiv ℝ V) w u u) ∧
            (∀ w ∈ Ω, (Metric.infDist w (frontier Ω))⁻¹ ^ 2 - C ≤
              ‖gradient V w‖ ^ 2 / 4 - Laplacian.laplacian V w / 2) ∧
            ∀ e : AffineSimplex.Tangent m ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m),
              let ρ' := ρ.map e
              let U := e '' Ω
              let W := V ∘ e.symm
              ∃ hW : IsEuclideanGibbsPotential volume ρ' U W,
                let hU := e.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen m L)
                let hB := e.isometry.lipschitzWith.isBounded_image
                  (ConditionalWellPosedness.fibre_isBounded m L)
                ConditionalWellPosedness.EuclideanWellPosed hU hB hW := by
  intro r hr a ha σ J B μ
  refine ⟨tilted_coordinates_disintegration p n m hn σ r hr θ ε true,
    fun x => simplexFibreKernel_density p n m hn σ θ ha J true x, ?_⟩
  intro k l σ' τ' L hL y hy z hz hcompatY hcompatZ
  exact IntegratedCovariance.conditional_intrinsic_equations p m k l hm σ' τ' hL
    y hy z hz hcompatY hcompatZ θ ε hε

end Riesz2.InterpolatingDensities
