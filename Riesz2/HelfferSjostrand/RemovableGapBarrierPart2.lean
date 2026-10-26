/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.RemovableGapBarrier
public import Riesz2.ToMathlib.SimplexFirstCoordinate
public import Riesz2.ToMathlib.ConvexIntervalMarginal

/-!
# One-gap densities after removing the nearest-gap singularity

The product chart is obtained from the free gap chart by separating
its first coordinate.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology ENNReal ContDiff

namespace Riesz2.RemovableGapBarrier

private theorem convexOn_chart_pullback {n : ℕ} {L : ℝ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : ConvexOn ℝ (AffineSimplex.massSimplex n L) f) :
    ConvexOn ℝ (AffineSimplex.chartDomain n L)
      (fun x => f (AffineSimplex.chart n L x)) := by
  refine ⟨AffineSimplex.convex_chartDomain n L, ?_⟩
  intro x hx y hy a b ha hb hab
  dsimp only
  rw [AffineSimplex.chart_convex_combination n L x y hab]
  exact hf.2 ((AffineSimplex.chart_mem_simplex_iff n L x).mpr hx)
    ((AffineSimplex.chart_mem_simplex_iff n L y).mpr hy) ha hb hab

/-- See the proof of Lemma 2.1 in the paper, the density and residual-density
clauses for the first gap, in both exponent regimes and for `N = n + 2`.
The density law uses the Gibbs measure. -/
theorem first_gap_density (p : Parameters) (n : ℕ) :
    ∃ f h : ℝ → ℝ,
      (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X 0) =
        (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))).withDensity
          (fun u => ENNReal.ofReal (f u)) ∧
      ContinuousOn f (Ioo (0 : ℝ) (n + 2 : ℝ)) ∧
      (∀ u ∈ Ioo (0 : ℝ) (n + 2 : ℝ), 0 < f u ∧ 0 < h u) ∧
      (∀ u ∈ Ioo (0 : ℝ) (n + 2 : ℝ),
        f u = Real.exp (-(2 * p.val.1) * u ^ (-p.val.2)) * h u) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun u => Real.log (f u)) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun u => Real.log (h u)) := by
  let N := (n + 1).succPNat
  let e := AffineSimplex.splitFirst n
  let k : (ℝ × EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    e.symm.trans (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
  let Q := k ⁻¹' AffineSimplex.chartDomain (n + 1) (n + 2)
  let C := fun q => AffineSimplex.chart (n + 1) (n + 2) (k q)
  have hk := k.toLinearMap.continuous_of_finiteDimensional
  have hQo : IsOpen Q := (AffineSimplex.isOpen_chartDomain _ _).preimage hk
  have hQc : Convex ℝ Q := (AffineSimplex.convex_chartDomain _ _).linear_preimage k.toLinearMap
  have hQb : Bornology.IsBounded Q := by
    have hb := (k.symm.toContinuousLinearEquiv.toContinuousLinearMap.lipschitzWith.isBounded_image
      (AffineSimplex.isBounded_chartDomain (n + 1) (n + 2)))
    apply hb.subset
    intro q hq
    exact ⟨k q, hq, k.symm_apply_apply q⟩
  have hproj : Prod.fst '' Q = Ioo (0 : ℝ) (n + 2 : ℝ) :=
    AffineSimplex.fst_image_splitFirst_domain n (n + 2)
  have hC (q) (hq : q ∈ Q) : C q ∈ AffineSimplex.massSimplex (n + 1) (n + 2) :=
    (AffineSimplex.chart_mem_simplex_iff _ _ _).mpr hq
  have hC0 (q) : C q (0 : Fin (n + 2)) = q.1 := by
    change AffineSimplex.chart (n + 1) (n + 2) (k q) (Fin.castSucc 0) = q.1
    rw [AffineSimplex.chart_castSucc]
    rfl
  obtain ⟨W, _, hval, _, hres, hW⟩ := selected_gap_barrier_convex p N (by simp [N])
  have hsimplex : (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) =
      AffineSimplex.massSimplex (n + 1) (n + 2) :=
    by
      ext y
      change ((∀ i, 0 < y i) ∧ ∑ i, y i = ((N : ℕ) : ℝ)) ↔
        ((∀ i, 0 < y i) ∧ ∑ i, y i = (n + 2 : ℝ))
      simp only [N, Nat.succPNat_coe, Nat.cast_succ, add_assoc, one_add_one_eq_two]
  rw [hsimplex] at hW hres
  let V := fun q => p.val.1 * W (C q)
  let R := fun q => p.val.1 * (W (C q) - 2 * q.1 ^ (-p.val.2))
  have hV : ConvexOn ℝ Q V := by
    exact (convexOn_chart_pullback hW).comp_linearMap k.toLinearMap |>.smul p.property.1.le
  have hR : ConvexOn ℝ Q R := by
    have ht := ((convexOn_chart_pullback (hres 0)).comp_linearMap k.toLinearMap).smul
      p.property.1.le
    apply ht.congr
    intro q _
    simp only [Function.comp_apply, smul_eq_mul]
    rfl
  let T := fun X : Riesz1.Configuration N => e (GapChart.gaps (n + 1) X).val
  have hTm : Measurable T := e.toLinearMap.continuous_of_finiteDimensional.measurable.comp
    (measurable_subtype_coe.comp (GapChart.measurable_gaps (n + 1)))
  have hTQ (X : Riesz1.Configuration N) : T X ∈ Q := by
    change WithLp.toLp 2 (e.symm (e (GapChart.gaps (n + 1) X).val)) ∈
      AffineSimplex.chartDomain (n + 1) (n + 2)
    rw [e.symm_apply_apply]
    simpa only [N, Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (GapChart.gaps (n + 1) X).property
  have hCT (X : Riesz1.Configuration N) : C (T X) = WithLp.toLp 2 (gapVector X) := by
    change AffineSimplex.chart (n + 1) (n + 2)
      (WithLp.toLp 2 (e.symm (e (GapChart.gaps (n + 1) X).val))) = _
    rw [e.symm_apply_apply]
    simpa only [N, Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (GapChart.gapVector_eq_chart (n + 1) X).symm
  have henergy (X : Riesz1.Configuration N) : W (C (T X)) = energy p X := by
    rw [hCT]
    exact (hval ⟨_, GapChart.gapVector_mem_gapAmbientDomain X⟩).trans
      (GapChart.physicalAmbientGapEnergy_gapVector p N (by simp [N]) X)
  let D : ℝ≥0∞ := ENNReal.ofReal ((n + 2 : ℝ) ^ (n + 1))⁻¹
  have hvol : (Riesz1.configurationVolume N).map T = D • volume.restrict Q := by
    have hcoords := congrArg (Measure.map Prod.snd)
      (GapChart.map_configurationVolume_coordinates (n + 1))
    rw [Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod,
      Riesz1.measure_restrict_Ico_univ, one_smul,
      Measure.map_map measurable_snd (GapChart.measurable_coordinates (n + 1))] at hcoords
    have hfree : (Riesz1.configurationVolume N).map
        (fun X => (GapChart.gaps (n + 1) X).val) = D •
          volume.restrict ((WithLp.toLp 2) ⁻¹' AffineSimplex.chartDomain (n + 1) (n + 2)) := by
      simpa only [N, D, GapChart.gaps, Function.comp_def, Nat.cast_add,
        Nat.cast_one, add_assoc, one_add_one_eq_two] using hcoords
    have hmap : (volume.restrict ((WithLp.toLp 2) ⁻¹'
        AffineSimplex.chartDomain (n + 1) (n + 2))).map e = volume.restrict Q := by
      have hpre : e ⁻¹' Q = ((WithLp.toLp 2) ⁻¹'
          AffineSimplex.chartDomain (n + 1) (n + 2)) := by
        ext x
        change WithLp.toLp 2 (e.symm (e x)) ∈ AffineSimplex.chartDomain (n + 1) (n + 2) ↔
          WithLp.toLp 2 x ∈ AffineSimplex.chartDomain (n + 1) (n + 2)
        rw [e.symm_apply_apply]
      rw [← hpre, ← Measure.restrict_map
        (AffineSimplex.measurePreserving_splitFirst n).measurable hQo.measurableSet,
        (AffineSimplex.measurePreserving_splitFirst n).map_eq]
    have hem : Measurable (e : (Fin (n + 1) → ℝ) → _) :=
      e.toLinearMap.continuous_of_finiteDimensional.measurable
    have hfm : Measurable (fun X : Riesz1.Configuration N =>
        (GapChart.gaps (n + 1) X).val) :=
      measurable_subtype_coe.comp (GapChart.measurable_gaps (n + 1))
    calc
      _ = ((Riesz1.configurationVolume N).map
          (fun X => (GapChart.gaps (n + 1) X).val)).map e :=
        (Measure.map_map hem hfm).symm
      _ = _ := by rw [hfree, Measure.map_smul _ hem.aemeasurable, hmap]
  let w := Q.indicator (fun q => Real.exp (-V q))
  have hwm : Measurable w := Riesz1.measurable_exp_indicator hQo hV
  have hweight : (fun X : Riesz1.Configuration N => ENNReal.ofReal
      (Real.exp (-p.val.1 * energy p X))) = fun X => ENNReal.ofReal (w (T X)) := by
    funext X
    rw [show w (T X) = Real.exp (-V (T X)) from indicator_of_mem (hTQ X) _]
    simp only [V, henergy, neg_mul]
  let A : ℝ≥0∞ := (partitionFunction p N)⁻¹ * D
  have hA0 : A ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr (finiteModel_valid p N).2.2.2.ne)
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  have hAt : A ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (finiteModel_valid p N).2.2.1.ne')
    (ENNReal.ofReal_ne_top)
  let c := A.toReal
  have hc : 0 < c := ENNReal.toReal_pos hA0 hAt
  have hlaw : (gibbsMeasure p N).map T =
      ENNReal.ofReal c • volume.withDensity (fun q => ENNReal.ofReal (w q)) := by
    rw [GapChart.gibbsMeasure_eq_withDensity, hweight,
      Measure.map_smul _ hTm.aemeasurable, Riesz1.map_withDensity_comp _ hTm hwm.ennreal_ofReal,
      hvol, withDensity_smul_measure, smul_smul]
    change A • (volume.restrict Q).withDensity (fun q => ENNReal.ofReal (w q)) = _
    rw [ENNReal.ofReal_toReal hAt]
    congr 1
    have he : (fun q => ENNReal.ofReal (w q)) =
        Q.indicator (fun q => ENNReal.ofReal (Real.exp (-V q))) := by
      ext q
      by_cases hq : q ∈ Q <;> simp [w, hq]
    simp only [he, withDensity_indicator hQo.measurableSet,
      Measure.restrict_restrict hQo.measurableSet, inter_self]
  let f := fun u => c * ∫ z, w (u, z)
  let h := fun u => c * ∫ z, Q.indicator (fun q => Real.exp (-R q)) (u, z)
  have han := convex_interval_marginal hQo hQb hV hR
    (fun u => 2 * p.val.1 * u ^ (-p.val.2)) (fun q _ => by dsimp [V, R]; ring) hc
  rw [hproj] at han
  refine ⟨f, h, ?_, han.1, han.2.1, fun u _ => ?_, han.2.2.2.1, han.2.2.2.2⟩
  · have hT0 : (fun X : Riesz1.Configuration N => Riesz1.gap X 0) = Prod.fst ∘ T := by
      funext X
      change gapVector X 0 = (T X).1
      rw [← hC0 (T X), hCT]
      rfl
    rw [hT0, ← Measure.map_map measurable_fst hTm, hlaw,
      Measure.map_smul _ measurable_fst.aemeasurable,
      show (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) = volume.prod volume from rfl,
      AffineFibre.map_fst_withDensity volume volume hwm.ennreal_ofReal]
    have he : (AffineFibre.fibreMass volume (fun q => ENNReal.ofReal (w q))) =
        fun u => ENNReal.ofReal (∫ z, w (u, z)) := by
      funext u
      exact (ofReal_integral_eq_lintegral_ofReal
        (Riesz1.integrable_fiber_exp_indicator hQo hQb hV u)
        (Filter.Eventually.of_forall (fun z => indicator_nonneg
          (fun _ _ => (Real.exp_pos _).le) (u, z)))).symm
    rw [he, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    have hs : (fun u => ENNReal.ofReal c * ENNReal.ofReal (∫ z, w (u, z))) =
        (Ioo (0 : ℝ) (n + 2 : ℝ)).indicator (fun u => ENNReal.ofReal (f u)) := by
      funext u
      rw [← ENNReal.ofReal_mul hc.le]
      by_cases hu : u ∈ Ioo (0 : ℝ) (n + 2 : ℝ)
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu]
        have hz : ∀ z, w (u, z) = 0 := by
          intro z
          apply indicator_of_notMem
          intro hq
          exact hu (hproj.subset ⟨(u, z), hq, rfl⟩)
        simp only [hz, integral_zero, mul_zero, ENNReal.ofReal_zero]
    change volume.withDensity (fun u => ENNReal.ofReal c *
      ENNReal.ofReal (∫ z, w (u, z))) = _
    rw [hs, withDensity_indicator measurableSet_Ioo]
  · convert han.2.2.1 u using 1
    congr 2
    ring

private theorem gap_label_law (p : Parameters) (n : ℕ) (j : ℤ) :
    (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X j) =
      (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X 0) := by
  have hstep (j : ℤ) :
      (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X (j + 1)) =
        (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X j) := by
    have ht := congrArg (Measure.map (fun X => Riesz1.gap X j))
      (GapSymmetries.gibbsMeasure_map_cycleConfig p n)
    rw [Measure.map_map (Riesz1.measurable_gap j) GapSymmetries.measurable_cycleConfig] at ht
    have he : (fun X => Riesz1.gap X j) ∘ GapSymmetries.cycleConfig =
        fun X : Riesz1.Configuration (n + 1).succPNat => Riesz1.gap X (j + 1) := by
      funext X
      exact GapSymmetries.gap_cycleConfig X j
    rw [he] at ht
    exact ht
  refine Int.induction_on j rfl ?_ ?_
  · intro k ih
    exact (hstep k).trans ih
  · intro k ih
    have ht := hstep (-(k : ℤ) - 1)
    rw [sub_add_cancel] at ht
    exact ht.symm.trans ih

/-- See the proof of Lemma 2.1 in the paper, all density clauses, for every
integer label and both exponent regimes. Includes the two-particle gas. -/
theorem gap_density (p : Parameters) (n : ℕ) (j : ℤ) :
    ∃ f h : ℝ → ℝ,
      (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X j) =
        (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))).withDensity
          (fun u => ENNReal.ofReal (f u)) ∧
      ContinuousOn f (Ioo (0 : ℝ) (n + 2 : ℝ)) ∧
      (∀ u ∈ Ioo (0 : ℝ) (n + 2 : ℝ), 0 < f u ∧ 0 < h u) ∧
      (∀ u ∈ Ioo (0 : ℝ) (n + 2 : ℝ),
        f u = Real.exp (-(2 * p.val.1) * u ^ (-p.val.2)) * h u) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun u => Real.log (f u)) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun u => Real.log (h u)) := by
  rw [gap_label_law p n j]
  exact first_gap_density p n

/-- See the proof of Lemma 2.1 in the paper, log-concavity of the actual
survival probability on its full positive support, for both exponent regimes. -/
theorem gap_survival (p : Parameters) (n : ℕ) (j : ℤ) :
    ConcaveOn ℝ (Iio (n + 2 : ℝ)) (fun u => Real.log
      ((((gibbsMeasure p (n + 1).succPNat).map
        (fun X => Riesz1.gap X j)) (Ici u)).toReal)) := by
  obtain ⟨f, _, hν, hf, hp, _, hc, _⟩ := gap_density p n j
  have := gibbsMeasure_probability p (n + 1).succPNat
  exact interval_density_log_survival (by positivity) hf
    (fun u hu => (hp u hu).1) hc hν

/-- See the proof of Lemma 2.1 in the paper. The realization agrees with the
physical energy throughout its ambient domain. Removing all or any selected
nearest-gap barriers leaves a convex residual. Each gap coordinate has a
positive continuous density with the nearest-gap singularity factored out,
a log-concave survival function, and integrable mean one. -/
theorem single_gap_tails_barrier (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y - 2 * ∑ i, (y i) ^ (-p.val.2)) ∧
      (∀ i : Fin (N : ℕ), ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y - 2 * (y i) ^ (-p.val.2))) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) W) ∧
    ∀ i : Fin (N : ℕ),
      (∃ f h : ℝ → ℝ,
        (gapLaw p N).map (fun y => y i) =
          (volume.restrict (Ioo (0 : ℝ) (N : ℝ))).withDensity
            (fun u => ENNReal.ofReal (f u)) ∧
        ContinuousOn f (Ioo (0 : ℝ) (N : ℝ)) ∧
        (∀ u ∈ Ioo (0 : ℝ) (N : ℝ), 0 < f u ∧ 0 < h u) ∧
        (∀ u ∈ Ioo (0 : ℝ) (N : ℝ),
          f u = Real.exp (-(2 * p.val.1) * u ^ (-p.val.2)) * h u) ∧
        ConcaveOn ℝ (Ioo (0 : ℝ) (N : ℝ)) (fun u => Real.log (f u)) ∧
        ConcaveOn ℝ (Ioo (0 : ℝ) (N : ℝ)) (fun u => Real.log (h u))) ∧
      ConcaveOn ℝ (Iio (N : ℝ)) (fun u => Real.log
        ((((gapLaw p N).map (fun y => y i)) (Ici u)).toReal)) ∧
      Integrable (fun y : Fin (N : ℕ) → ℝ => y i) (gapLaw p N) ∧
      (∫ y, y i ∂gapLaw p N) = 1 := by
  refine ⟨selected_gap_barrier_convex p N hN, fun i => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat :=
    ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  have hmap : (gapLaw p (n + 1).succPNat).map (fun y => y i) =
      (gibbsMeasure p (n + 1).succPNat).map (fun X => Riesz1.gap X (i : ℕ)) := by
    have hgm : Measurable (@gapVector (n + 1).succPNat) := Riesz1.measurable_gapVector _
    rw [gapLaw, Measure.map_map (measurable_pi_apply i) hgm]
    rfl
  have hcast : (((n + 1).succPNat : ℕ) : ℝ) = n + 2 := by
    simp only [Nat.succPNat_coe, Nat.cast_succ, add_assoc, one_add_one_eq_two]
  refine ⟨?_, ?_, gap_mean_one p (n + 1).succPNat hN i⟩
  · rw [hmap, hcast]
    exact gap_density p n (i : ℕ)
  · rw [hmap, hcast]
    exact gap_survival p n (i : ℕ)

end Riesz2.RemovableGapBarrier

end
