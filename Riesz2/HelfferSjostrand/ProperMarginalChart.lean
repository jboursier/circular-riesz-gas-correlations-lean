/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.RetainedSimplexCharts
public import Riesz2.ToMathlib.ProductDensityKernel
public import Riesz2.HelfferSjostrand.RemovableGapBarrier
public import Riesz2.HelfferSjostrand.PhysicalCollision
public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.Frozen.ProperMarginalDomain
public import Riesz2.Sanity.TiltedLaws
public import Riesz2.DecayShort.LocalLaw
import all Riesz2.DecayShort.LocalLaw

/-!
# Physical laws in retained-coordinate affine charts

The density below is the actual physical Gibbs factor, extended by zero off its
positive mass simplex. This is a density extension, not an extension of the energy.
All energy evaluations use the ambient-domain subtype.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Riesz2.ProperMarginalChart

theorem simplex_ambient (k : ℕ) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ AffineSimplex.massSimplex k (k + 1)) : y ∈ gapAmbientDomain k.succPNat := by
  apply PhysicalEnergy.simplex_subset_ambient k.succPNat (WithLp.ofLp y)
  refine ⟨hy.1, ?_⟩
  change (∑ i : Fin (k + 1), y i) = ((k + 1 : ℕ) : ℝ)
  rw [Nat.cast_add, Nat.cast_one]
  exact hy.2


/-- The Gibbs factor on the physical mass simplex, zero off its support. -/
def density (p : Parameters) (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 1))) : ℝ≥0∞ := by
  classical
  exact if h : y ∈ AffineSimplex.massSimplex k (k + 1) then
    ENNReal.ofReal (Real.exp (-p.val.1 * physicalAmbientGapEnergy p k.succPNat
      ⟨y, simplex_ambient k h⟩))
  else 0

private theorem density_eq_indicator (p : Parameters) (k : ℕ)
    {W : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hW : ∀ y : {y : EuclideanSpace ℝ (Fin (k + 1)) // y ∈ gapAmbientDomain k.succPNat},
      W y.val = physicalAmbientGapEnergy p k.succPNat y) :
    density p k = (AffineSimplex.massSimplex k (k + 1)).indicator
      (fun y => ENNReal.ofReal (Real.exp (-p.val.1 * W y))) := by
  classical
  funext y
  by_cases hy : y ∈ AffineSimplex.massSimplex k (k + 1)
  · simp only [density, dite_eq_left hy, indicator_of_mem hy]
    rw [hW ⟨y, simplex_ambient k hy⟩]
    rfl
  · simp [density, hy]

/-- The supported physical Gibbs factor is measurable in both exponent regimes. -/
theorem measurable_density (p : Parameters) (k : ℕ) : Measurable (density p k) := by
  classical
  obtain ⟨W, hW, hval, _⟩ := PhysicalEnergy.ambient_derivatives p k.succPNat
  rw [density_eq_indicator p k hval]
  have hc : ContinuousOn (fun y => ENNReal.ofReal (Real.exp (-p.val.1 * W y)))
      (AffineSimplex.massSimplex k (k + 1)) := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    exact (continuousOn_const.mul (hW.continuousOn.mono
      (fun y hy => simplex_ambient k hy))).rexp
  exact hc.measurable_piecewise continuousOn_const (RetainedSimplex.measurableSet_simplex k _)

/-- Particle volume transported to the full Euclidean gap vector. -/
theorem map_configurationVolume_full (k : ℕ) :
    (Riesz1.configurationVolume k.succPNat).map
      (fun X : Riesz1.Configuration k.succPNat =>
        (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) =
      ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹ •
        (ENNReal.ofReal (Real.sqrt (k + 1)))⁻¹ •
          AffineSimplex.simplexVolume k (k + 1) := by
  have : SFinite (AffineSimplex.simplexVolume k (k + 1)) := by
    rw [AffineSimplex.simplexVolume_eq]
    infer_instance
  have h := congrArg (Measure.map Prod.snd) (GapChart.map_configurationVolume_intrinsic k)
  have hm : Measurable (fun X : Riesz1.Configuration k.succPNat =>
      (X.val 0, (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1))))) :=
    ((measurable_pi_apply 0).comp measurable_subtype_coe).prodMk
      ((PiLp.volume_preserving_toLp (Fin (k + 1))).measurable.comp (Riesz1.measurable_gapVector k.succPNat))
  rw [Measure.map_map measurable_snd hm, Measure.map_snd_prod,
    Riesz1.measure_restrict_Ico_univ, one_smul] at h
  exact h

/-- The actual particle Gibbs weight is the supported physical gap density. -/
theorem density_gapVector (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (X : Riesz1.Configuration k.succPNat) :
    density p k (WithLp.toLp 2 (gapVector X)) =
      ENNReal.ofReal (Real.exp (-p.val.1 * energy p X)) := by
  classical
  have hs : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.massSimplex k (k + 1) :=
    (GapChart.gapVector_eq_chart k X).symm ▸
      (AffineSimplex.chart_mem_simplex_iff k (k + 1) _).mpr (GapChart.gaps k X).property
  change (if h : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.massSimplex k (k + 1) then
    ENNReal.ofReal (Real.exp (-p.val.1 * physicalAmbientGapEnergy p k.succPNat
      ⟨WithLp.toLp 2 (gapVector X), simplex_ambient k h⟩)) else 0) = _
  split_ifs
  exact congrArg (fun t => ENNReal.ofReal (Real.exp (-p.val.1 * t)))
      (GapChart.physicalAmbientGapEnergy_gapVector p k.succPNat
        (by simp only [Nat.succPNat_coe]; omega) X)

/-- Full physical density with the particle and intrinsic Jacobians explicit. -/
theorem map_gibbsMeasure_full (p : Parameters) (k : ℕ) (hk : 1 ≤ k) :
    (gibbsMeasure p k.succPNat).map
      (fun X : Riesz1.Configuration k.succPNat =>
        (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) =
      (partitionFunction p k.succPNat)⁻¹ • ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹ •
        (ENNReal.ofReal (Real.sqrt (k + 1)))⁻¹ •
          (AffineSimplex.simplexVolume k (k + 1)).withDensity (density p k) := by
  have hm : Measurable (fun X : Riesz1.Configuration k.succPNat =>
      (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) :=
    (PiLp.volume_preserving_toLp (Fin (k + 1))).measurable.comp (Riesz1.measurable_gapVector k.succPNat)
  rw [GapChart.gibbsMeasure_eq_withDensity, Measure.map_smul _ hm.aemeasurable]
  have he : (fun X : Riesz1.Configuration k.succPNat =>
      ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) =
      fun X : Riesz1.Configuration k.succPNat => density p k (WithLp.toLp 2 (gapVector X)) :=
    funext (fun X => (density_gapVector p k hk X).symm)
  rw [he, Riesz1.map_withDensity_comp _ hm (measurable_density p k),
    map_configurationVolume_full, withDensity_smul_measure, withDensity_smul_measure]

/-- The supported Gibbs factor in the retained/exterior free coordinates. -/
def chartDensity (p : Parameters) (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1))) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
  (RetainedSimplex.domain n m ((n + m : ℕ) + 1)).indicator
    (fun q => density p (n + m)
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q))

theorem measurable_chartDensity (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) : Measurable (chartDensity p n m σ) :=
  ((measurable_density p (n + m)).comp
    (RetainedSimplex.continuous_chart n m _ σ).measurable).indicator
      (RetainedSimplex.isOpen_domain n m _).measurableSet

private theorem chartDensity_eq_exp (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ}
    (hW : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) :
    chartDensity p n m σ = fun q => ENNReal.ofReal
      ((RetainedSimplex.domain n m ((n + m : ℕ) + 1)).indicator
        (fun q => Real.exp (-p.val.1 * W
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q))) q) := by
  classical
  have he := density_eq_indicator p (n + m) hW
  funext q
  by_cases hq : q ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  · have hs := (RetainedSimplex.chart_mem_simplex n m _ σ q).mpr hq
    simp only [chartDensity, he, indicator_of_mem hq, indicator_of_mem hs]
  · simp only [chartDensity, indicator_of_notMem hq, ENNReal.ofReal_zero]

/-- Every interior physical exterior fibre has strictly positive finite mass,
including the point fibre when only one gap is exterior. -/
theorem fibre_mass (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    AffineFibre.fibreMass volume (chartDensity p n m σ) x ≠ 0 ∧
      AffineFibre.fibreMass volume (chartDensity p n m σ) x ≠ ∞ := by
  obtain ⟨W, _, hval, _, _, hconv⟩ :=
    RemovableGapBarrier.selected_gap_barrier_convex p (n + m).succPNat
      (by simp only [Nat.succPNat_coe]; omega)
  have hs (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (hq : q ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)) :
      WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q) ∈
        Riesz1.gapSimplex (n + m).succPNat := by
    have h := (RetainedSimplex.chart_mem_simplex n m _ σ q).mpr hq
    exact ⟨h.1, by
      change (∑ i : Fin (n + m + 1), RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q i) =
        ((n + m + 1 : ℕ) : ℝ)
      simpa only [Nat.cast_add, Nat.cast_one] using h.2⟩
  have hc : ConvexOn ℝ (RetainedSimplex.domain n m ((n + m : ℕ) + 1))
      (fun q => p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q)) := by
    refine ⟨RetainedSimplex.convex_domain n m _, fun u hu v hv a b ha hb hab => ?_⟩
    calc
      _ = p.val.1 * W (a • RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ u +
          b • RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ v) :=
        congrArg (fun y : EuclideanSpace ℝ (Fin (n + m + 1)) => p.val.1 * W y)
          (RetainedSimplex.chart_convex_combination n m _ σ u v hab)
      _ ≤ _ := (hconv.smul p.property.1.le).2 (hs u hu) (hs v hv) ha hb hab
  have hx' : x ∈ Prod.fst '' RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
    rw [RetainedSimplex.fst_image_domain]
    exact hx
  have h := AffineFibre.convex_fibre_mass (RetainedSimplex.isOpen_domain n m _)
    (RetainedSimplex.isBounded_domain n m _) hc hx'
  rw [chartDensity_eq_exp p n m σ hval]
  simpa only [neg_mul] using h

/-- The physical exterior conditional on each interior retained point. -/
def conditionalMeasure (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  AffineFibre.normalizedMeasure volume (fun z => chartDensity p n m σ (x.val, z))
    (fibre_mass p n m hn σ x.property).1 (fibre_mass p n m hn σ x.property).2

theorem conditionalMeasure_probability (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    IsProbabilityMeasure (conditionalMeasure p n m hn σ x) :=
  AffineFibre.isProbabilityMeasure_normalizedMeasure _
    ((measurable_chartDensity p n m σ).comp measurable_prodMk_left) _ _

/-- The actual Gibbs law in arbitrary retained/exterior free coordinates.
The intrinsic square-root factor cancels the inverse area factor from particles. -/
theorem map_gibbsMeasure_coordinates (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    (gibbsMeasure p (n + m).succPNat).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
          (volume.prod volume).withDensity (chartDensity p n m σ) := by
  have hm : Measurable (fun X : Riesz1.Configuration (n + m).succPNat =>
      (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (n + m + 1)))) :=
    (PiLp.volume_preserving_toLp _).measurable.comp
      (Riesz1.measurable_gapVector (n + m).succPNat)
  have hc : Measurable (RetainedSimplex.coordinates n m σ) :=
    (RetainedSimplex.continuous_coordinates n m σ).measurable
  have he := congrArg (Measure.map (RetainedSimplex.coordinates n m σ))
    (map_gibbsMeasure_full p (n + m) (by omega))
  rw [Measure.map_map hc hm, Measure.map_smul _ hc.aemeasurable,
    Measure.map_smul _ hc.aemeasurable, Measure.map_smul _ hc.aemeasurable,
    RetainedSimplex.map_coordinates_withDensity n m _ σ (measurable_density p (n + m))] at he
  simp only [Nat.cast_add, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
      (Real.sqrt_pos.mpr (show (0 : ℝ) < n + m + 1 by positivity)))
      ENNReal.ofReal_ne_top, mul_one] at he
  convert he using 1 <;> simp only [Nat.cast_add, smul_smul, chartDensity, Function.comp_def]

/-- Every proper active pushforward has the physical fibre-integral density.
The retained labels are exactly `σ ((i.castAdd m).castSucc)`. -/
theorem map_gibbsMeasure_retained (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    (gibbsMeasure p (n + m).succPNat).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1) =
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
          volume.withDensity (AffineFibre.fibreMass volume (chartDensity p n m σ)) := by
  have h := congrArg (Measure.map Prod.fst) (map_gibbsMeasure_coordinates p n m hn σ)
  have hm : Measurable (fun X : Riesz1.Configuration (n + m).succPNat =>
      RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m σ).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp
        (Riesz1.measurable_gapVector (n + m).succPNat))
  rw [Measure.map_map measurable_fst hm, Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable,
    AffineFibre.map_fst_withDensity volume volume (measurable_chartDensity p n m σ)] at h
  exact h

/-- The conditional laws form a Markov kernel on the retained interior. -/
def conditionalKernel (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ProbabilityTheory.Kernel (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (EuclideanSpace ℝ (Fin m)) :=
  AffineFibre.normalizedKernel volume
    ((measurable_chartDensity p n m σ).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (fun x => (fibre_mass p n m hn σ x.property).1)
    (fun x => (fibre_mass p n m hn σ x.property).2)

theorem conditionalKernel_apply (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    conditionalKernel p n m hn σ x = conditionalMeasure p n m hn σ x := rfl

instance conditionalKernel_markov (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ProbabilityTheory.IsMarkovKernel (conditionalKernel p n m hn σ) :=
  AffineFibre.normalizedKernel_markov _ _ _ _

private theorem chartDensity_support (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∉ AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (z : EuclideanSpace ℝ (Fin m)) : chartDensity p n m σ (x, z) = 0 := by
  have hq : (x, z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
    intro h
    apply hx
    rw [← RetainedSimplex.fst_image_domain n m ((n + m : ℕ) + 1)]
    exact ⟨(x, z), h, rfl⟩
  exact indicator_of_notMem hq _

/-- Disintegration of the actual physical law as an equality of measures, using
explicit conditionals at every interior retained point. -/
theorem gibbs_coordinates_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    (gibbsMeasure p (n + m).succPNat).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
          (((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
              ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
                EuclideanSpace ℝ (Fin n))).withDensity
                  (fun x => AffineFibre.fibreMass volume (chartDensity p n m σ) x.val) ⊗ₘ
            conditionalKernel p n m hn σ).map (fun q => (q.1.val, q.2)) := by
  rw [map_gibbsMeasure_coordinates p n m hn σ]
  congr 2
  rw [AffineFibre.withDensity_eq_map_subtypeProd volume volume
    (AffineSimplex.isOpen_chartDomain n _).measurableSet
      (measurable_chartDensity p n m σ) (chartDensity_support p n m σ)]
  congr 1
  exact AffineFibre.withDensity_eq_compProd _ _ _ _ _

/-- The point fibre is a point mass, with no exceptional retained points. -/
theorem conditionalMeasure_point (p : Parameters) (n : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + 0 + 1)))
    (x : AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)) :
    conditionalMeasure p n 0 hn σ x = Measure.dirac 0 := by
  have := conditionalMeasure_probability p n 0 hn σ x
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    ∫⁻ z, f z ∂conditionalMeasure p n 0 hn σ x =
        ∫⁻ _, f 0 ∂conditionalMeasure p n 0 hn σ x :=
      lintegral_congr (fun z => congrArg f (Subsingleton.elim z 0))
    _ = f 0 := by simp
    _ = _ := by simp

/-- The supported physical Gibbs factor with an allowed selected-coordinate
penalty. Its value off the positive simplex is zero. -/
def penalizedDensity (p : Parameters) (k : ℕ) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (k + 1))) (b : Bool)
    (y : EuclideanSpace ℝ (Fin (k + 1))) : ℝ≥0∞ :=
  density p k y * ENNReal.ofReal (Real.exp (-p.val.1 *
    ∑ i ∈ J, (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0)))

private theorem penalty_continuousOn (k : ℕ) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (k + 1))) (b : Bool) :
    ContinuousOn (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
      ∑ i ∈ J, (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0))
        (AffineSimplex.massSimplex k (k + 1)) := by
  apply continuousOn_finsetSum
  intro i _
  have he : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (k + 1)) => y i)
      (AffineSimplex.massSimplex k (k + 1)) := (PiLp.continuous_apply 2 _ i).continuousOn
  have hup := θ.property.1.continuousOn.comp (continuousOn_const.mul he)
    (fun y (hy : y ∈ AffineSimplex.massSimplex k (k + 1)) =>
      mul_nonneg ha.le (hy.1 i).le)
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def, Pi.mul_apply] using hup
  · have hdown := θ.property.1.continuousOn.comp
      (continuousOn_const.mul (he.inv₀ (fun y hy => (hy.1 i).ne')))
      (fun y (hy : y ∈ AffineSimplex.massSimplex k (k + 1)) =>
        mul_nonneg ha.le (inv_nonneg.mpr (hy.1 i).le))
    convert hup.add hdown using 1
    funext y
    rfl

/-- Both allowed penalties have measurable supported physical Gibbs factors. -/
theorem measurable_penalizedDensity (p : Parameters) (k : ℕ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1))) (b : Bool) :
    Measurable (penalizedDensity p k θ a J b) := by
  classical
  obtain ⟨W, hW, hval, _⟩ := PhysicalEnergy.ambient_derivatives p k.succPNat
  have hc : ContinuousOn (fun y => ENNReal.ofReal (Real.exp (-p.val.1 * W y)))
      (AffineSimplex.massSimplex k (k + 1)) := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    exact (continuousOn_const.mul (hW.continuousOn.mono
      (fun y hy => simplex_ambient k hy))).rexp
  have hp : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
      ENNReal.ofReal (Real.exp (-p.val.1 * ∑ i ∈ J,
        (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0))))
      (AffineSimplex.massSimplex k (k + 1)) := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    exact (continuousOn_const.mul (penalty_continuousOn k θ ha J b)).rexp
  have he : penalizedDensity p k θ a J b =
      (AffineSimplex.massSimplex k (k + 1)).indicator (fun y =>
        ENNReal.ofReal (Real.exp (-p.val.1 * W y)) * ENNReal.ofReal (Real.exp
          (-p.val.1 * ∑ i ∈ J, (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0)))) := by
    funext y
    rw [penalizedDensity, density_eq_indicator p k hval]
    by_cases hy : y ∈ AffineSimplex.massSimplex k (k + 1)
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, zero_mul]
  rw [he]
  exact (hc.ennreal_mul hp (fun _ _ => Or.inr ENNReal.ofReal_ne_top)
    (fun _ _ => Or.inr ENNReal.ofReal_ne_top)).measurable_piecewise continuousOn_const
    (RetainedSimplex.measurableSet_simplex k _)

/-- Both penalties in the actual retained chart. -/
def penalizedChartDensity (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
  (RetainedSimplex.domain n m ((n + m : ℕ) + 1)).indicator
    (fun q => penalizedDensity p (n + m) θ a J b
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q))

theorem measurable_penalizedChartDensity (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool) :
    Measurable (penalizedChartDensity p n m σ θ a J b) :=
  ((measurable_penalizedDensity p (n + m) θ ha J b).comp
    (RetainedSimplex.continuous_chart n m _ σ).measurable).indicator
      (RetainedSimplex.isOpen_domain n m _).measurableSet

/-- Active penalties are constant on each exterior fibre. The coefficient is
evaluated at zero exterior free coordinates, which preserves all retained gaps. -/
theorem penalizedChartDensity_eq_mul (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc)
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) :
    penalizedChartDensity p n m σ θ a J b (x, z) =
      ENNReal.ofReal (Real.exp (-p.val.1 * ∑ i ∈ J,
        (θ.val (a * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, 0) i) +
          if b then θ.val (a * (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, 0) i)⁻¹)
          else 0))) * chartDensity p n m σ (x, z) := by
  classical
  have he : (∑ i ∈ J, (θ.val (a * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, z) i) +
      if b then θ.val (a * (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, z) i)⁻¹) else 0)) =
      ∑ i ∈ J, (θ.val (a * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, 0) i) +
      if b then θ.val (a * (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, 0) i)⁻¹) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨j, rfl⟩ := hJ i hi
    rw [RetainedSimplex.chart_retained, RetainedSimplex.chart_retained]
  by_cases hq : (x, z) ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  · simp only [penalizedChartDensity, chartDensity, indicator_of_mem hq, penalizedDensity, he]
    exact mul_comm _ _
  · simp only [penalizedChartDensity, chartDensity, indicator_of_notMem hq, mul_zero]

/-- Allowed penalties preserve finite positive mass at every retained interior point. -/
theorem penalized_fibre_mass (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    AffineFibre.fibreMass volume (penalizedChartDensity p n m σ θ a J b) x ≠ 0 ∧
      AffineFibre.fibreMass volume (penalizedChartDensity p n m σ θ a J b) x ≠ ∞ := by
  obtain ⟨h0, ht⟩ := fibre_mass p n m hn σ hx
  unfold AffineFibre.fibreMass
  simp_rw [penalizedChartDensity_eq_mul p n m σ θ a J b hJ]
  rw [lintegral_const_mul _ (show Measurable (fun z => chartDensity p n m σ (x, z)) from
    (measurable_chartDensity p n m σ).comp measurable_prodMk_left)]
  exact ⟨mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) h0,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht⟩

/-- The exterior conditional of either allowed active penalty is exactly the
unpenalized physical exterior conditional, pointwise throughout the interior. -/
theorem penalized_conditionalMeasure (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    AffineFibre.normalizedMeasure volume
      (fun z => penalizedChartDensity p n m σ θ a J b (x.val, z))
      (penalized_fibre_mass p n m hn σ θ a J b hJ x.property).1
      (penalized_fibre_mass p n m hn σ θ a J b hJ x.property).2 =
        conditionalMeasure p n m hn σ x := by
  simp_rw [penalizedChartDensity_eq_mul p n m σ θ a J b hJ]
  exact AffineFibre.normalizedMeasure_mul_const volume
    (measurable_chartDensity p n m σ) x.val _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top

/-- The tilt factor supported on the physical simplex. -/
def penaltyWeight (p : Parameters) (k : ℕ) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (k + 1))) (b : Bool) : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞ :=
  (AffineSimplex.massSimplex k (k + 1)).indicator (fun y => ENNReal.ofReal (Real.exp
    (-p.val.1 * ∑ i ∈ J, (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0))))

theorem measurable_penaltyWeight (p : Parameters) (k : ℕ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1))) (b : Bool) :
    Measurable (penaltyWeight p k θ a J b) := by
  classical
  have hp : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
      ENNReal.ofReal (Real.exp (-p.val.1 * ∑ i ∈ J,
        (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0))))
      (AffineSimplex.massSimplex k (k + 1)) := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    exact (continuousOn_const.mul (penalty_continuousOn k θ ha J b)).rexp
  exact hp.measurable_piecewise continuousOn_const (RetainedSimplex.measurableSet_simplex k _)

private theorem penalizedDensity_eq_mul (p : Parameters) (k : ℕ) (θ : PhysicalCutoff)
    (a : ℝ) (J : Finset (Fin (k + 1))) (b : Bool) :
    penalizedDensity p k θ a J b = density p k * penaltyWeight p k θ a J b := by
  classical
  funext y
  by_cases hy : y ∈ AffineSimplex.massSimplex k (k + 1)
  · simp only [penalizedDensity, Pi.mul_apply, penaltyWeight, indicator_of_mem hy]
  · simp only [penalizedDensity, Pi.mul_apply, penaltyWeight, indicator_of_notMem hy,
      density, dite_eq_right hy, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The first-block penalty weight is the same supported gap weight. -/
theorem penaltyWeight_frozen_gapVector (p : Parameters) (k : ℕ) (r : ℕ+)
    (hr : (r : ℕ) ≤ (k.succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (b : Bool)
    (X : Riesz1.Configuration k.succPNat) :
    penaltyWeight p k θ ((r : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb hr)) b
      (WithLp.toLp 2 (gapVector X)) =
        ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty k.succPNat r hr θ ε b X)) := by
  have hs : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.massSimplex k (k + 1) :=
    (GapChart.gapVector_eq_chart k X).symm ▸
      (AffineSimplex.chart_mem_simplex_iff k (k + 1) _).mpr (GapChart.gaps k X).property
  simp only [penaltyWeight, indicator_of_mem hs, Finset.sum_map,
    Fin.castLEEmb_apply, physicalGapPenalty, gapVector]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Full gap density of both tilted laws, for every block size. -/
theorem map_tiltedParticleMeasure_full (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ+) (hr : (r : ℕ) ≤ (k.succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    (tiltedParticleMeasure p k.succPNat r hr θ ε b).map
      (fun X : Riesz1.Configuration k.succPNat =>
        (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) =
      (tiltNormalizer p k.succPNat r hr θ ε b)⁻¹ •
        (partitionFunction p k.succPNat)⁻¹ • ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹ •
          (ENNReal.ofReal (Real.sqrt (k + 1)))⁻¹ •
            (AffineSimplex.simplexVolume k (k + 1)).withDensity
              (penalizedDensity p k θ ((r : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb hr)) b) := by
  have hm : Measurable (fun X : Riesz1.Configuration k.succPNat =>
      (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) :=
    (PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector k.succPNat)
  have hw := measurable_penaltyWeight p k θ (Real.rpow_pos_of_pos
    (show (0 : ℝ) < r by exact_mod_cast r.pos) (-ε))
    (Finset.univ.map (Fin.castLEEmb hr)) b
  have he : (fun X : Riesz1.Configuration k.succPNat => ENNReal.ofReal
      (Real.exp (-p.val.1 * physicalGapPenalty k.succPNat r hr θ ε b X))) =
      fun X : Riesz1.Configuration k.succPNat => penaltyWeight p k θ ((r : ℝ) ^ (-ε))
        (Finset.univ.map (Fin.castLEEmb hr)) b (WithLp.toLp 2 (gapVector X)) :=
    funext (fun X => (penaltyWeight_frozen_gapVector p k r hr θ ε b X).symm)
  unfold tiltedParticleMeasure
  rw [Measure.map_smul _ hm.aemeasurable, he, Riesz1.map_withDensity_comp _ hm hw,
    map_gibbsMeasure_full p k hk, withDensity_smul_measure, withDensity_smul_measure,
    withDensity_smul_measure, ← withDensity_mul _ (measurable_density p k) hw,
    ← penalizedDensity_eq_mul]

private theorem penalizedChartDensity_support (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) (a : ℝ)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∉ AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (z : EuclideanSpace ℝ (Fin m)) : penalizedChartDensity p n m σ θ a J b (x, z) = 0 := by
  have hq : (x, z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
    intro h
    apply hx
    rw [← RetainedSimplex.fst_image_domain n m ((n + m : ℕ) + 1)]
    exact ⟨(x, z), h, rfl⟩
  exact indicator_of_notMem hq _

/-- Both physical penalty densities disintegrate with the same pointwise
exterior kernel. The base density includes the active penalty. -/
theorem penalized_product_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc) :
    (volume.prod volume).withDensity (penalizedChartDensity p n m σ θ a J b) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin n))).withDensity
              (fun x => AffineFibre.fibreMass volume (penalizedChartDensity p n m σ θ a J b) x.val) ⊗ₘ
        conditionalKernel p n m hn σ).map (fun q => (q.1.val, q.2)) := by
  let w : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) × EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
    fun q => penalizedChartDensity p n m σ θ a J b (q.1.val, q.2)
  have hw : Measurable w := (measurable_penalizedChartDensity p n m σ θ ha J b).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have h0 (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
      AffineFibre.fibreMass volume w x ≠ 0 :=
    (penalized_fibre_mass p n m hn σ θ a J b hJ x.property).1
  have ht (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
      AffineFibre.fibreMass volume w x ≠ ∞ :=
    (penalized_fibre_mass p n m hn σ θ a J b hJ x.property).2
  have heK : AffineFibre.normalizedKernel volume hw h0 ht = conditionalKernel p n m hn σ := by
    apply DFunLike.ext
    intro x
    exact penalized_conditionalMeasure p n m hn σ θ a J b hJ x
  rw [AffineFibre.withDensity_eq_map_subtypeProd volume volume
    (AffineSimplex.isOpen_chartDomain n _).measurableSet
    (measurable_penalizedChartDensity p n m σ θ ha J b)
    (penalizedChartDensity_support p n m σ θ a J b)]
  congr 1
  exact (AffineFibre.withDensity_eq_compProd volume _ hw h0 ht).trans
    (congrArg (fun K => _ ⊗ₘ K) heK)

/-- Tonelli disintegration for every nonnegative measurable physical chart test. -/
theorem lintegral_penalized_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc)
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q, f q ∂(volume.prod volume).withDensity (penalizedChartDensity p n m σ θ a J b) =
      ∫⁻ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        (∫⁻ z, f (x.val, z) ∂conditionalMeasure p n m hn σ x)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin n))).withDensity
              (fun x => AffineFibre.fibreMass volume (penalizedChartDensity p n m σ θ a J b) x.val) := by
  have hm : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  rw [penalized_product_disintegration p n m hn σ θ ha J b hJ, lintegral_map hf hm]
  have hf' : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => f (q.1.val, q.2)) := hf.comp hm
  exact Measure.lintegral_compProd hf' 

/-- Bochner disintegration for every integrable physical chart test. -/
theorem integral_penalized_disintegration {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) (b : Bool)
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc)
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → E}
    (hf : Integrable f ((volume.prod volume).withDensity (penalizedChartDensity p n m σ θ a J b))) :
    ∫ q, f q ∂(volume.prod volume).withDensity (penalizedChartDensity p n m σ θ a J b) =
      ∫ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        (∫ z, f (x.val, z) ∂conditionalMeasure p n m hn σ x)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin n))).withDensity
              (fun x => AffineFibre.fibreMass volume (penalizedChartDensity p n m σ θ a J b) x.val) := by
  rw [penalized_product_disintegration p n m hn σ θ ha J b hJ] at hf ⊢
  have hm : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact Measure.integral_compProd
    ((integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hf)

set_option backward.isDefEq.respectTransparency false in
/-- Both tilted particle laws in every retained-coordinate affine chart. -/
theorem map_tiltedParticleMeasure_coordinates (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (r : ℕ+)
    (hr : (r : ℕ) ≤ ((n + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    (tiltedParticleMeasure p (n + m).succPNat r hr θ ε b).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (tiltNormalizer p (n + m).succPNat r hr θ ε b)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            (volume.prod volume).withDensity
              (penalizedChartDensity p n m σ θ ((r : ℝ) ^ (-ε))
                (Finset.univ.map (Fin.castLEEmb hr)) b) := by
  have hm : Measurable (fun X : Riesz1.Configuration (n + m).succPNat =>
      (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (n + m + 1)))) :=
    (PiLp.volume_preserving_toLp _).measurable.comp
      (Riesz1.measurable_gapVector (n + m).succPNat)
  have hc : Measurable (RetainedSimplex.coordinates n m σ) :=
    (RetainedSimplex.continuous_coordinates n m σ).measurable
  have he := congrArg (Measure.map (RetainedSimplex.coordinates n m σ))
    (map_tiltedParticleMeasure_full p (n + m) (by omega) r hr θ ε b)
  rw [Measure.map_map hc hm, Measure.map_smul _ hc.aemeasurable,
    Measure.map_smul _ hc.aemeasurable, Measure.map_smul _ hc.aemeasurable,
    Measure.map_smul _ hc.aemeasurable,
    RetainedSimplex.map_coordinates_withDensity n m _ σ
      (measurable_penalizedDensity p (n + m) θ (Real.rpow_pos_of_pos
        (show (0 : ℝ) < r by exact_mod_cast r.pos) (-ε)) _ b)] at he
  simp only [Nat.cast_add, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
      (Real.sqrt_pos.mpr (show (0 : ℝ) < n + m + 1 by positivity)))
      ENNReal.ofReal_ne_top, mul_one] at he
  convert he using 1 <;> simp only [Nat.cast_add, smul_smul, penalizedChartDensity, Function.comp_def]

/-- The retained marginal of each tilt has its explicit fibre density. -/
theorem map_tiltedParticleMeasure_retained (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (r : ℕ+)
    (hr : (r : ℕ) ≤ ((n + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    (tiltedParticleMeasure p (n + m).succPNat r hr θ ε b).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1) =
      (tiltNormalizer p (n + m).succPNat r hr θ ε b)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            volume.withDensity (AffineFibre.fibreMass volume
              (penalizedChartDensity p n m σ θ ((r : ℝ) ^ (-ε))
                (Finset.univ.map (Fin.castLEEmb hr)) b)) := by
  have h := congrArg (Measure.map Prod.fst)
    (map_tiltedParticleMeasure_coordinates p n m hn σ r hr θ ε b)
  have hm : Measurable (fun X : Riesz1.Configuration (n + m).succPNat =>
      RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m σ).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp
        (Riesz1.measurable_gapVector (n + m).succPNat))
  rw [Measure.map_map measurable_fst hm, Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_smul _ measurable_fst.aemeasurable,
    AffineFibre.map_fst_withDensity volume volume
      (measurable_penalizedChartDensity p n m σ θ (Real.rpow_pos_of_pos
        (show (0 : ℝ) < r by exact_mod_cast r.pos) (-ε)) _ b)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The proper active law, with the actual normalization factors.
The exterior dimension is `m`, so `m = 0` is included. -/
theorem activeTiltedGapLaw_density (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε b =
      (tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε b)⁻¹ •
        (partitionFunction p ((n : ℕ) + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ ((n : ℕ) + m))⁻¹ •
            volume.withDensity (AffineFibre.fibreMass volume
              (penalizedChartDensity p n m (Equiv.refl _) θ ((n : ℝ) ^ (-ε))
                (Finset.univ.map (Fin.castLEEmb hn)) b)) := by
  have h := map_tiltedParticleMeasure_retained p n m n.pos (Equiv.refl _) n hn θ ε b
  have he : (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      (RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))).1) =
      fun X => WithLp.toLp 2 (finiteGapBlock X) := by
    funext X
    ext i
    rw [RetainedSimplex.coordinates_retained]
    rfl
  rw [he] at h
  exact h

/-- The active chart interior is the proper-marginal domain. -/
theorem baseDomain_eq_properMarginalDomain (n : ℕ+) (m : ℕ) :
    AffineSimplex.chartDomain n (((n : ℕ) + m : ℕ) + 1) =
      properMarginalDomain n ((n : ℕ) + m).succPNat := by
  ext x
  change ((∀ i, 0 < x i) ∧ (∑ i, x i) < ((n : ℕ) + m : ℕ) + 1) ↔
    ((∀ i, 0 < x i) ∧ (∑ i, x i) < (((n : ℕ) + m).succPNat : ℝ))
  simp only [Nat.succPNat_coe, Nat.cast_succ]

set_option backward.isDefEq.respectTransparency false in
/-- The same marginal statement directly on the full gap law. -/
theorem map_gapLaw_retained (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    (gapLaw p (n + m).succPNat).map
      (fun g : Fin ((n + m).succPNat : ℕ) → ℝ =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 g)).1) =
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
          volume.withDensity (AffineFibre.fibreMass volume (chartDensity p n m σ)) := by
  have hm : Measurable (fun g : Fin ((n + m).succPNat : ℕ) → ℝ =>
      (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 g)).1) :=
    ((RetainedSimplex.continuous_coordinates n m σ).measurable.comp
      (PiLp.volume_preserving_toLp _).measurable).fst
  have hg : Measurable (@gapVector (n + m).succPNat) :=
    Riesz1.measurable_gapVector (n + m).succPNat
  rw [gapLaw, Measure.map_map hm hg]
  exact map_gibbsMeasure_retained p n m hn σ

/-- The free exterior support is precisely the exterior mass-simplex support. -/
theorem fibre_chartDensity (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (fun z => chartDensity p n m σ (x, z)) =
      (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x i)).indicator
        (fun z => density p (n + m) (RetainedSimplex.assemble n m σ x
          (AffineSimplex.chart m (((n + m : ℕ) + 1) - ∑ i, x i) z))) := by
  classical
  funext z
  have he := Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ hx) z
  by_cases hz : z ∈ AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x i)
  · have hq : (x, z) ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := he.mpr hz
    simp only [chartDensity, indicator_of_mem hz, indicator_of_mem hq,
      RetainedSimplex.assemble_chart]
  · have hq : (x, z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) :=
      fun h => hz (he.mp h)
    simp only [chartDensity, indicator_of_notMem hz, indicator_of_notMem hq]

/-- Exact intrinsic exterior normalizer, retaining the exterior area factor. -/
theorem exterior_mass_eq (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (∫⁻ y, density p (n + m) (RetainedSimplex.assemble n m σ x y)
      ∂AffineSimplex.simplexVolume m (((n + m : ℕ) + 1) - ∑ i, x i)) =
      ENNReal.ofReal (Real.sqrt (m + 1)) *
        AffineFibre.fibreMass volume (chartDensity p n m σ) x := by
  rw [AffineSimplex.lintegral_simplexVolume]
  congr 1
  rw [← lintegral_indicator (AffineSimplex.isOpen_chartDomain m _).measurableSet,
    ← fibre_chartDensity p n m σ hx]

/-- Strict positivity and finiteness of the intrinsic physical exterior normalizer. -/
theorem exterior_mass_valid (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (∫⁻ y, density p (n + m) (RetainedSimplex.assemble n m σ x y)
      ∂AffineSimplex.simplexVolume m (((n + m : ℕ) + 1) - ∑ i, x i)) ≠ 0 ∧
    (∫⁻ y, density p (n + m) (RetainedSimplex.assemble n m σ x y)
      ∂AffineSimplex.simplexVolume m (((n + m : ℕ) + 1) - ∑ i, x i)) ≠ ∞ := by
  rw [exterior_mass_eq p n m σ hx]
  obtain ⟨h0, ht⟩ := fibre_mass p n m hn σ hx
  exact ⟨mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))) h0,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht⟩

/-- The actual conditional, expressed using intrinsic exterior simplex volume.
The exterior square-root factor cancels from the normalized law. -/
theorem conditionalMeasure_exterior (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    AffineFibre.normalizedMeasure
      (AffineSimplex.simplexVolume m (((n + m : ℕ) + 1) - ∑ i, x.val i))
      (fun y => density p (n + m) (RetainedSimplex.assemble n m σ x.val y))
      (exterior_mass_valid p n m hn σ x.property).1
      (exterior_mass_valid p n m hn σ x.property).2 =
      (conditionalMeasure p n m hn σ x).map
        (AffineSimplex.chart m (((n + m : ℕ) + 1) - ∑ i, x.val i)) := by
  let L : ℝ := ((n + m : ℕ) + 1) - ∑ i, x.val i
  let w : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞ :=
    fun y => density p (n + m) (RetainedSimplex.assemble n m σ x.val y)
  have hw : Measurable w := (measurable_density p (n + m)).comp
    (RetainedSimplex.continuous_assemble n m σ x.val).measurable
  have he : (∫⁻ z in AffineSimplex.chartDomain m L, w (AffineSimplex.chart m L z)) =
      AffineFibre.fibreMass volume (chartDensity p n m σ) x.val := by
    rw [← lintegral_indicator (AffineSimplex.isOpen_chartDomain m L).measurableSet]
    rw [← fibre_chartDensity p n m σ x.property]
  have h0 : (∫⁻ z in AffineSimplex.chartDomain m L, w (AffineSimplex.chart m L z)) ≠ 0 :=
    he.trans_ne (fibre_mass p n m hn σ x.property).1
  have ht : (∫⁻ z in AffineSimplex.chartDomain m L, w (AffineSimplex.chart m L z)) ≠ ∞ :=
    he.trans_ne (fibre_mass p n m hn σ x.property).2
  have hc : conditionalMeasure p n m hn σ x =
      AffineFibre.normalizedMeasure (volume.restrict (AffineSimplex.chartDomain m L))
        (fun z => w (AffineSimplex.chart m L z)) h0 ht := by
    unfold conditionalMeasure
    simp_rw [fibre_chartDensity p n m σ x.property]
    exact AffineFibre.normalizedMeasure_indicator volume
      (AffineSimplex.isOpen_chartDomain m L).measurableSet _ h0 ht
  rw [hc]
  exact AffineFibre.SumChart.normalizedMeasure_simplexVolume m L hw h0 ht

/-- Actual tilted-law disintegration. Every penalized coordinate must be
retained. The exterior kernel is the same unpenalized physical kernel. -/
theorem tilted_coordinates_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (r : ℕ+)
    (hr : (r : ℕ) ≤ ((n + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (b : Bool)
    (hJ : ∀ i ∈ Finset.univ.map (Fin.castLEEmb hr),
      ∃ j : Fin n, i = σ (j.castAdd m).castSucc) :
    (tiltedParticleMeasure p (n + m).succPNat r hr θ ε b).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (tiltNormalizer p (n + m).succPNat r hr θ ε b)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            (((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
              ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
                EuclideanSpace ℝ (Fin n))).withDensity
                  (fun x => AffineFibre.fibreMass volume
                    (penalizedChartDensity p n m σ θ ((r : ℝ) ^ (-ε))
                      (Finset.univ.map (Fin.castLEEmb hr)) b) x.val) ⊗ₘ
              conditionalKernel p n m hn σ).map (fun q => (q.1.val, q.2)) := by
  rw [map_tiltedParticleMeasure_coordinates p n m hn σ r hr θ ε b]
  exact congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) =>
    (tiltNormalizer p (n + m).succPNat r hr θ ε b)⁻¹ •
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ • μ)
    (penalized_product_disintegration p n m hn σ θ (Real.rpow_pos_of_pos
      (show (0 : ℝ) < r by exact_mod_cast r.pos) (-ε)) _ b hJ)

/-- The active-law density formula has a finite positive normalizer and
is a probability, for both penalties and every proper size. -/
theorem activeTiltedGapLaw_density_valid (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    0 < tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε b ∧
      tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε b < ∞ ∧
      IsProbabilityMeasure (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε b) ∧
      activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε b =
        (tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε b)⁻¹ •
          (partitionFunction p ((n : ℕ) + m).succPNat)⁻¹ •
            ENNReal.ofReal ((n + m + 1 : ℝ) ^ ((n : ℕ) + m))⁻¹ •
              volume.withDensity (AffineFibre.fibreMass volume
                (penalizedChartDensity p n m (Equiv.refl _) θ ((n : ℝ) ^ (-ε))
                  (Finset.univ.map (Fin.castLEEmb hn)) b)) := by
  obtain ⟨hz, hle⟩ := DefinitionSanity.tilt_normalizer_valid p _ n hn θ ε b
  exact ⟨hz, hle.trans_lt (by simp), DefinitionSanity.active_tilted_probability p _ n hn θ ε b,
    activeTiltedGapLaw_density p n m hn θ ε b⟩

/-- The intrinsic exterior integral and free-coordinate fibre integral differ
by exactly `sqrt(m+1)`, independent of the retained point. -/
theorem fibreMass_eq_exterior_mass (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    AffineFibre.fibreMass volume (chartDensity p n m σ) x =
      (ENNReal.ofReal (Real.sqrt (m + 1)))⁻¹ *
        ∫⁻ y, density p (n + m) (RetainedSimplex.assemble n m σ x y)
          ∂AffineSimplex.simplexVolume m (((n + m : ℕ) + 1) - ∑ i, x i) := by
  rw [exterior_mass_eq p n m σ hx, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
      (Real.sqrt_pos.mpr (by positivity))) ENNReal.ofReal_ne_top, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The actual arbitrary-set upper penalty factors through the supported gap weight. -/
theorem penaltyWeight_upper_gapVector (p : Parameters) (k : ℕ) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (k + 1)))
    (X : Riesz1.Configuration k.succPNat) :
    penaltyWeight p k θ R.val⁻¹ J false (WithLp.toLp 2 (gapVector X)) =
      ENNReal.ofReal (Real.exp (-p.val.1 *
        DecayShort.upperGapPenalty (N := k.succPNat) θ R J X)) := by
  have hs : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.massSimplex k (k + 1) :=
    (GapChart.gapVector_eq_chart k X).symm ▸
      (AffineSimplex.chart_mem_simplex_iff k (k + 1) _).mpr (GapChart.gaps k X).property
  rw [penaltyWeight, indicator_of_mem hs]
  congr 2
  congr 1
  unfold DecayShort.upperGapPenalty
  apply Finset.sum_congr rfl
  intro i _
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, gapVector, div_eq_mul_inv]
  exact congrArg θ.val (mul_comm R.val⁻¹ (gap X i.val))

set_option backward.isDefEq.respectTransparency false in
/-- Full intrinsic physical density of the arbitrary-set upper tilt. -/
theorem map_upperTiltedParticleMeasure_full (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (J : Finset (Fin (k + 1))) :
    (DecayShort.upperTiltedParticleMeasure p k.succPNat θ R J).map
      (fun X : Riesz1.Configuration k.succPNat =>
        (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) =
      (DecayShort.upperGapNormalizer p k.succPNat θ R J)⁻¹ •
        (partitionFunction p k.succPNat)⁻¹ • ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹ •
          (ENNReal.ofReal (Real.sqrt (k + 1)))⁻¹ •
            (AffineSimplex.simplexVolume k (k + 1)).withDensity
              (penalizedDensity p k θ R.val⁻¹ J false) := by
  have hm : Measurable (fun X : Riesz1.Configuration k.succPNat =>
      (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (k + 1)))) :=
    (PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector k.succPNat)
  have hw := measurable_penaltyWeight p k θ (inv_pos.mpr R.property) J false
  have he : (fun X : Riesz1.Configuration k.succPNat => ENNReal.ofReal
      (Real.exp (-p.val.1 * DecayShort.upperGapPenalty (N := k.succPNat) θ R J X))) =
      fun X : Riesz1.Configuration k.succPNat =>
        penaltyWeight p k θ R.val⁻¹ J false (WithLp.toLp 2 (gapVector X)) :=
    funext (fun X => (penaltyWeight_upper_gapVector p k θ R J X).symm)
  unfold DecayShort.upperTiltedParticleMeasure
  rw [Measure.map_smul _ hm.aemeasurable, he, Riesz1.map_withDensity_comp _ hm hw,
    map_gibbsMeasure_full p k hk, withDensity_smul_measure, withDensity_smul_measure,
    withDensity_smul_measure, ← withDensity_mul _ (measurable_density p k) hw,
    ← penalizedDensity_eq_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The arbitrary-set upper law in every retained-coordinate chart. -/
theorem map_upperTiltedParticleMeasure_coordinates (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (n + m + 1))) :
    (DecayShort.upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (DecayShort.upperGapNormalizer p (n + m).succPNat θ R J)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            (volume.prod volume).withDensity (penalizedChartDensity p n m σ θ R.val⁻¹ J false) := by
  have hm : Measurable (fun X : Riesz1.Configuration (n + m).succPNat =>
      (WithLp.toLp 2 (gapVector X) : EuclideanSpace ℝ (Fin (n + m + 1)))) :=
    (PiLp.volume_preserving_toLp _).measurable.comp
      (Riesz1.measurable_gapVector (n + m).succPNat)
  have hc : Measurable (RetainedSimplex.coordinates n m σ) :=
    (RetainedSimplex.continuous_coordinates n m σ).measurable
  have he := congrArg (Measure.map (RetainedSimplex.coordinates n m σ))
    (map_upperTiltedParticleMeasure_full p (n + m) (by omega) θ R J)
  rw [Measure.map_map hc hm, Measure.map_smul _ hc.aemeasurable,
    Measure.map_smul _ hc.aemeasurable, Measure.map_smul _ hc.aemeasurable,
    Measure.map_smul _ hc.aemeasurable,
    RetainedSimplex.map_coordinates_withDensity n m _ σ
      (measurable_penalizedDensity p (n + m) θ (inv_pos.mpr R.property) J false)] at he
  simp only [Nat.cast_add, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
      (Real.sqrt_pos.mpr (show (0 : ℝ) < n + m + 1 by positivity)))
      ENNReal.ofReal_ne_top, mul_one] at he
  convert he using 1 <;> simp only [Nat.cast_add, smul_smul, penalizedChartDensity, Function.comp_def]

/-- The arbitrary-set retained marginal has the physical fibre density. -/
theorem map_upperTiltedParticleMeasure_retained (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (n + m + 1))) :
    (DecayShort.upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1) =
      (DecayShort.upperGapNormalizer p (n + m).succPNat θ R J)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            volume.withDensity (AffineFibre.fibreMass volume
              (penalizedChartDensity p n m σ θ R.val⁻¹ J false)) := by
  have h := congrArg (Measure.map Prod.fst)
    (map_upperTiltedParticleMeasure_coordinates p n m hn σ θ R J)
  have hm : Measurable (fun X : Riesz1.Configuration (n + m).succPNat =>
      RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m σ).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp
        (Riesz1.measurable_gapVector (n + m).succPNat))
  rw [Measure.map_map measurable_fst hm, Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_smul _ measurable_fst.aemeasurable,
    AffineFibre.map_fst_withDensity volume volume
      (measurable_penalizedChartDensity p n m σ θ (inv_pos.mpr R.property) J false)] at h
  exact h

/-- Actual arbitrary-set upper-tilt disintegration, using the physical exterior
conditional at every interior retained point. -/
theorem upper_coordinates_disintegration (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (n + m + 1)))
    (hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc) :
    (DecayShort.upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))) =
      (DecayShort.upperGapNormalizer p (n + m).succPNat θ R J)⁻¹ •
        (partitionFunction p (n + m).succPNat)⁻¹ •
          ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
            (((volume : Measure (EuclideanSpace ℝ (Fin n))).comap
              ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
                EuclideanSpace ℝ (Fin n))).withDensity
                  (fun x => AffineFibre.fibreMass volume
                    (penalizedChartDensity p n m σ θ R.val⁻¹ J false) x.val) ⊗ₘ
              conditionalKernel p n m hn σ).map (fun q => (q.1.val, q.2)) := by
  rw [map_upperTiltedParticleMeasure_coordinates p n m hn σ θ R J]
  exact congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) =>
    (DecayShort.upperGapNormalizer p (n + m).succPNat θ R J)⁻¹ •
      (partitionFunction p (n + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ • μ)
    (penalized_product_disintegration p n m hn σ θ (inv_pos.mpr R.property) J false hJ)

/-- The arbitrary-set upper marginal formula has finite positive tilt normalization. -/
theorem upper_retained_density_valid (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (n + m + 1))) :
    0 < DecayShort.upperGapNormalizer p (n + m).succPNat θ R J ∧
      DecayShort.upperGapNormalizer p (n + m).succPNat θ R J < ∞ ∧
      IsProbabilityMeasure (DecayShort.upperTiltedParticleMeasure p (n + m).succPNat θ R J) ∧
      (DecayShort.upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
        (fun X : Riesz1.Configuration (n + m).succPNat =>
          (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1) =
        (DecayShort.upperGapNormalizer p (n + m).succPNat θ R J)⁻¹ •
          (partitionFunction p (n + m).succPNat)⁻¹ •
            ENNReal.ofReal ((n + m + 1 : ℝ) ^ (n + m))⁻¹ •
              volume.withDensity (AffineFibre.fibreMass volume
                (penalizedChartDensity p n m σ θ R.val⁻¹ J false)) := by
  obtain ⟨hz, hle⟩ := DecayShort.upperGapNormalizer_valid p (n + m).succPNat θ R J
  exact ⟨hz, hle.trans_lt (by simp),
    DecayShort.upperTiltedParticleMeasure_probability p (n + m).succPNat θ R J,
    map_upperTiltedParticleMeasure_retained p n m hn σ θ R J⟩

end Riesz2.ProperMarginalChart
