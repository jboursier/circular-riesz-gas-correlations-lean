/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.TwoVolumeComparison
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart8
public import Riesz2.Thermodynamic.LengthDerivative
public import Riesz2.Thermodynamic.CompatibleComparison
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Bayes identity for the common-length exterior law

The coordinate and conditional-expectation step in Proposition 6.6. All conditionals are
the physical kernels.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.TwoVolumeComparison

/-- See Subsection 6.1 of the paper: reconstruction in the active-first chart retains
every exterior coordinate, including the dependent final gap. -/
theorem exterior_chart_particle (n m : ℕ)
    (X : Riesz1.Configuration ((n + 1) + m).succPNat) :
    AffineSimplex.chart m (((n + 1 + m : ℕ) + 1 : ℝ) -
        ∑ i, (RetainedSimplex.coordinates (n + 1) m (Equiv.refl _)
          (WithLp.toLp 2 (gapVector X))).1 i)
      (RetainedSimplex.coordinates (n + 1) m (Equiv.refl _)
        (WithLp.toLp 2 (gapVector X))).2 =
      WithLp.toLp 2 (fun i : Fin (m + 1) => gap X ((n + 1 : ℕ) + i.val)) := by
  have hu : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.massSimplex (n + 1 + m)
      (((n + 1 + m : ℕ) + 1 : ℝ)) :=
    (GapChart.gapVector_eq_chart _ X).symm ▸
      (AffineSimplex.chart_mem_simplex_iff _ _ _).mpr (GapChart.gaps _ X).property
  have he := InterpolantLocalLaws.retained_chart_coordinates (n + 1) m _
    (Equiv.refl _) _ hu
  rw [← RetainedSimplex.assemble_chart] at he
  ext i
  have hi := congrArg (fun v => v (i.natAdd (n + 1))) he
  change RetainedSimplex.join (n + 1) (m + 1) _ (i.natAdd (n + 1)) = _ at hi
  rw [RetainedSimplex.join_right] at hi
  change _ = gap X (((n + 1 : ℕ) + i.val) : ℤ)
  rw [gap_eq_gapVector_labelOf]
  have hl := Riesz1.labelOf_natCast ((n + 1) + m).succPNat (i.natAdd (n + 1))
  have hl' : Riesz1.labelOf ((n + 1) + m).succPNat
      (((n + 1 : ℕ) + i.val) : ℤ) = i.natAdd (n + 1) := by
    simpa only [Fin.val_natAdd, Nat.cast_add] using hl
  rw [hl']
  exact hi

section ExteriorCarrier

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

/-- The existing full exterior kernel pulled back to the actual compatible
exterior carrier of `physicalExteriorLaw`. See Subsection 6.1. -/
def chartedExteriorKernel :
    Kernel (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
      (AffineSimplex.chartDomain (m + 1) ((m + 1 + n : ℕ) + 1)) :=
  (lengthExteriorKernel p n m θ ε).comapRight
    (MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet)

/-- The reconstructed full exterior lies on the exterior-first carrier at
every interior length, including null fibres. See Subsection 6.1. -/
theorem exterior_carrier_ae
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ y ∂lengthExteriorKernel p n m θ ε L,
      y ∈ AffineSimplex.chartDomain (m + 1) ((m + 1 + n : ℕ) + 1) := by
  filter_upwards [exterior_positive_ae p n m θ ε L,
    exterior_mass_ae p n m θ ε L] with y hy hs
  refine ⟨hy, ?_⟩
  rw [hs]
  have hN : ((n + 1 + m : ℕ) + 1 : ℝ) = ((m + 1 + n : ℕ) + 1 : ℝ) := by
    norm_cast; omega
  linarith [L.property.1]

instance chartedExteriorKernel_markov : IsMarkovKernel (chartedExteriorKernel p n m θ ε) := by
  apply Kernel.IsMarkovKernel.comapRight
  intro L
  rw [Subtype.range_coe_subtype]
  have hh := congrArg (fun μ => μ univ)
    (Measure.restrict_eq_self_of_ae_mem (exterior_carrier_ae p n m θ ε L))
  simpa only [Measure.restrict_apply_univ, measure_univ, mem_ofPred_eq, ofPred_mem_eq] using hh

/-- The carrier pullback loses no exterior mass. See Subsection 6.1. -/
theorem map_chartedExteriorKernel
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (chartedExteriorKernel p n m θ ε L).map Subtype.val =
      lengthExteriorKernel p n m θ ε L := by
  rw [chartedExteriorKernel, Kernel.comapRight_apply,
    map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (exterior_carrier_ae p n m θ ε L)

/-- See Proposition 6.6 of the paper: the compatible-carrier exterior
mixture has the original full exterior mixture as its inclusion image,
for every base measure. -/
theorem map_chartedExteriorKernel_comp
    (ρ : Measure (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))) :
    (chartedExteriorKernel p n m θ ε ∘ₘ ρ).map Subtype.val =
      lengthExteriorKernel p n m θ ε ∘ₘ ρ := by
  rw [Measure.map_comp _ _ measurable_subtype_coe]
  have he : (chartedExteriorKernel p n m θ ε).map Subtype.val =
      lengthExteriorKernel p n m θ ε := by
    ext L S hS
    rw [Kernel.map_apply _ measurable_subtype_coe]
    exact congrArg (fun σ => σ S) (map_chartedExteriorKernel p n m θ ε L)
  rw [he]

/-- See Subsection 6.1 of the paper: the residual active length as a map from the
whole compatible exterior carrier to the physical open length interval. -/
def exteriorLength
    (y : AffineSimplex.chartDomain (m + 1) ((m + 1 + n : ℕ) + 1)) :
    Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) :=
  ⟨((m + 1 + n : ℕ) + 1 : ℝ) - ∑ i, y.val i,
    sub_pos.mpr y.property.2, by
      have hs : 0 < ∑ i, y.val i := Finset.sum_pos (fun i _ => y.property.1 i)
        Finset.univ_nonempty
      have hN : ((m + 1 + n : ℕ) + 1 : ℝ) = ((n + 1 + m : ℕ) + 1 : ℝ) := by
        norm_cast; omega
      linarith⟩

theorem measurable_exteriorLength : Measurable (exteriorLength n m) :=
  (measurable_const.sub (Finset.measurable_sum _ fun i _ =>
    (PiLp.continuous_apply 2 _ i).measurable.comp measurable_subtype_coe)).subtype_mk

/-- The pulled-back exterior has the prescribed active length, for every
interior length. See Proposition 6.6. -/
theorem exteriorLength_ae
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ y ∂chartedExteriorKernel p n m θ ε L, exteriorLength n m y = L := by
  have hh := exterior_mass_ae p n m θ ε L
  rw [← map_chartedExteriorKernel p n m θ ε L] at hh
  have hs := (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
      (PiLp.continuous_apply 2 _ i).measurable) measurable_const)).mp hh
  filter_upwards [hs] with y hy
  apply Subtype.ext
  change ((m + 1 + n : ℕ) + 1 : ℝ) - ∑ i, y.val i = L.val
  rw [hy]
  have hN : ((m + 1 + n : ℕ) + 1 : ℝ) = ((n + 1 + m : ℕ) + 1 : ℝ) := by
    norm_cast; omega
  rw [hN]
  ring

end ExteriorCarrier

/-- See Subsection 6.1 of the paper: the active-first retained coordinates are the
active gap block. -/
theorem active_coordinates_particle (n m : ℕ)
    (X : Riesz1.Configuration ((n + 1) + m).succPNat) :
    (RetainedSimplex.coordinates (n + 1) m (Equiv.refl _)
      (WithLp.toLp 2 (gapVector X))).1 =
        WithLp.toLp 2 (finiteGapBlock (K := n.succPNat) X) := by
  ext i
  rw [RetainedSimplex.coordinates_retained]
  change gapVector X ((i.castAdd m).castSucc) = gap X (i.val : ℤ)
  rw [gap_eq_gapVector_labelOf]
  exact congrArg (gapVector X) (Riesz1.labelOf_natCast ((n + 1) + m).succPNat ((i.castAdd m).castSucc)).symm

/-- See Proposition 6.6 of the paper: the length-first joint law and the
particle law agree for every nonnegative joint test of full exterior and
active block. -/
theorem length_joint_lintegral (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    {f : EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ L, ∫⁻ q, f (exteriorChart n m q, q.1.val)
      ∂lengthChartKernel p n m θ ε L ∂LengthAveragingFibres.lengthMeasure p n m θ ε) =
    ∫⁻ X, f (WithLp.toLp 2 (fun i : Fin (m + 1) => gap X ((n + 1 : ℕ) + i.val)),
      WithLp.toLp 2 (finiteGapBlock (K := n.succPNat) X))
      ∂tiltedParticleMeasure p ((n + 1) + m).succPNat n.succPNat (by simp only [Nat.succPNat_coe]; omega) θ ε true := by
  let g := fun q : EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin m) =>
    f (AffineSimplex.chart m (((n + 1 + m : ℕ) + 1 : ℝ) - ∑ i, q.1 i) q.2, q.1)
  have hg : Measurable g := hf.comp
    (((AffineFibre.SumChart.totalChart m).continuous.measurable.comp
      ((measurable_const.sub (Finset.measurable_sum _ fun i _ =>
        (PiLp.continuous_apply 2 _ i).measurable.comp measurable_fst)).prodMk measurable_snd)).prodMk
      measurable_fst)
  have hm := physical_lengthChart_disintegration p n m θ ε
  have hcoords : Measurable (fun X : Riesz1.Configuration ((n + 1) + m).succPNat =>
      RetainedSimplex.coordinates (n + 1) m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates _ _ _).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have he := congrArg (fun μ => ∫⁻ q, g q ∂μ) hm
  rw [lintegral_map hg hcoords, lintegral_map (g := fun q :
      AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
        EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) hg
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd),
    Measure.lintegral_bind (f := fun q :
      AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
        EuclideanSpace ℝ (Fin m) => g (q.1.val, q.2)) (Kernel.aemeasurable _) (hg.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)).aemeasurable] at he
  refine he.symm.trans (lintegral_congr fun X => ?_)
  dsimp only [g]
  rw [exterior_chart_particle, active_coordinates_particle]

/-- See Proposition 6.6 of the paper: the exterior-first physical chart
describes the same full exterior and active block as the length-first law.
 -/
theorem exterior_first_joint_lintegral (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    {f : EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞}
    (hf : Measurable f) :
    let h : n + 1 ≤ m + 1 + n + 1 := by omega
    let κ := InterpolatingDensities.simplexFibreKernel p (m + 1) n (by omega)
      (InterpolatingDensities.exteriorPermutation (m + 1) n) θ
      (Real.rpow_pos_of_pos ((by positivity) : (0 : ℝ) < (n + 1 : ℕ)) (-ε))
      (Finset.univ.map (Fin.castLEEmb h)) true
    (∫⁻ L, ∫⁻ q, f (exteriorChart n m q, q.1.val)
      ∂lengthChartKernel p n m θ ε L ∂LengthAveragingFibres.lengthMeasure p n m θ ε) =
      ∫⁻ y, ∫⁻ u, f (y.val, u) ∂κ y
        ∂InterpolantLocalLaws.physicalExteriorLaw p (m + 1) n θ ε := by
  intro h κ
  rw [length_joint_lintegral p n m θ ε hf]
  have he := (InterpolantLocalLaws.physical_exterior_disintegration p (m + 1) n
    (by omega) θ ε).2 f hf
  have he' : (∫⁻ X, f (WithLp.toLp 2 (fun i : Fin (m + 1) =>
        gap X ((n + 1 : ℕ) + i.val)), WithLp.toLp 2 (finiteGapBlock (K := n.succPNat) X))
      ∂tiltedParticleMeasure p (m + 1 + n).succPNat n.succPNat (by simp only [Nat.succPNat_coe]; omega) θ ε true) =
      ∫⁻ y, ∫⁻ u, f (y.val, u) ∂κ y
        ∂InterpolantLocalLaws.physicalExteriorLaw p (m + 1) n θ ε := by
    refine (lintegral_congr fun X => ?_).trans he
    apply congrArg f
    apply Prod.ext
    · ext i
      rw [InterpolantLocalLaws.exterior_coordinates_gap]
    · rfl
  let V := {N : ℕ+ // n + 1 ≤ (N : ℕ)}
  have hV : (⟨(m + 1 + n).succPNat, by simp only [Nat.succPNat_coe]; omega⟩ : V) =
      ⟨(n + 1 + m).succPNat, by simp only [Nat.succPNat_coe]; omega⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    change m + 1 + n + 1 = n + 1 + m + 1
    omega
  have hh := congrArg (fun v : V => ∫⁻ X, f
    (WithLp.toLp 2 (fun i : Fin (m + 1) => gap X ((n + 1 : ℕ) + i.val)),
      WithLp.toLp 2 (finiteGapBlock (K := n.succPNat) X))
    ∂tiltedParticleMeasure p v.val n.succPNat v.property θ ε true) hV
  exact hh.symm.trans he'

section Bayes

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

local notation "D" => AffineSimplex.chartDomain (m + 1) ((m + 1 + n : ℕ) + 1)
local notation "I" => Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)
local notation "Kphys" => InterpolatingDensities.simplexFibreKernel p (m + 1) n (by omega)
  (InterpolatingDensities.exteriorPermutation (m + 1) n) θ
  (Real.rpow_pos_of_pos ((by positivity) : (0 : ℝ) < (n + 1 : ℕ)) (-ε))
  (Finset.univ.map (Fin.castLEEmb ((by omega) : n + 1 ≤ m + 1 + n + 1))) true
local notation "exteriorLaw" => InterpolantLocalLaws.physicalExteriorLaw p (m + 1) n θ ε
local notation "lengthLaw" => LengthAveragingFibres.lengthMeasure p n m θ ε

/-- See Proposition 6.6 of the paper: the reconstructed exterior mixture,
on its actual carrier, is exactly `physicalExteriorLaw`. -/
theorem chartedExteriorKernel_comp_lengthMeasure :
    chartedExteriorKernel p n m θ ε ∘ₘ lengthLaw = exteriorLaw := by
  apply Measure.ext_of_lintegral
  intro f hf
  obtain ⟨g, hg, he⟩ := (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain _ _).measurableSet).exists_measurable_extend hf
      (fun _ => inferInstance)
  rw [← he]
  change (∫⁻ y : D, g y.val ∂chartedExteriorKernel p n m θ ε ∘ₘ lengthLaw) =
    ∫⁻ y : D, g y.val ∂exteriorLaw
  rw [Measure.lintegral_bind (f := fun y : D => g y.val) (Kernel.aemeasurable _) (hg.comp measurable_subtype_coe).aemeasurable]
  have hj := exterior_first_joint_lintegral p n m θ ε (f := fun q => g q.1)
    (hg.comp measurable_fst)
  simp only [lintegral_const, measure_univ, mul_one] at hj
  rw [← hj]
  apply lintegral_congr
  intro L
  rw [← lintegral_map hg measurable_subtype_coe, map_chartedExteriorKernel,
    lengthExteriorKernel, Kernel.lintegral_map _ (measurable_exteriorChart n m) L hg]

/-- Integrating an active test in the joint length chart recovers the
existing coarea fibre kernel. See Lemma 6.5. -/
theorem lengthChartKernel_active_lintegral {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞}
    (hg : Measurable g) (L : I) :
    (∫⁻ q, g q.1.val ∂lengthChartKernel p n m θ ε L) =
      ∫⁻ u, g u ∂LengthAveragingFibres.fibreKernel p n m θ ε L := by
  rw [lengthChartKernel, Kernel.lintegral_comp (g := fun q :
      AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
        EuclideanSpace ℝ (Fin m) => g q.1.val) _ _ L
    (hg.comp (measurable_subtype_coe.comp measurable_fst))]
  have hi (x : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :
      (∫⁻ q, g q.1.val ∂(Kernel.id ×ₖ ProperMarginalChart.conditionalKernel p
        (n + 1) m (by omega) (Equiv.refl _)) x) = g x.val := by
    rw [Kernel.lintegral_id_prod (f := fun q :
      AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
        EuclideanSpace ℝ (Fin m) => g q.1.val)
      (hg.comp (measurable_subtype_coe.comp measurable_fst))]
    simp
  simp_rw [hi]
  rw [← lintegral_map hg measurable_subtype_coe,
    LengthAveragingFibres.map_retainedKernel]

/-- See Proposition 6.6 of the paper: weighted Bayes identity for every
measurable nonnegative active test and every measurable length weight. -/
theorem weighted_bayes_lintegral
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hg : Measurable g)
    {w : I → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ L, w L * (∫⁻ y, ∫⁻ u, g u ∂Kphys y ∂chartedExteriorKernel p n m θ ε L) ∂lengthLaw) =
      ∫⁻ L, w L * (∫⁻ u, g u ∂LengthAveragingFibres.fibreKernel p n m θ ε L) ∂lengthLaw := by
  let a := fun y : D => ∫⁻ u, g u ∂Kphys y
  have ha : Measurable a := hg.lintegral_kernel
  obtain ⟨W, hW, he⟩ := (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain _ _).measurableSet).exists_measurable_extend
      (hw.comp (measurable_exteriorLength n m)) (fun _ => inferInstance)
  have hWeq (y : D) : W y.val = w (exteriorLength n m y) := congrFun he y
  have hWL (L : I) : ∀ᵐ y ∂chartedExteriorKernel p n m θ ε L, W y.val = w L := by
    filter_upwards [exteriorLength_ae p n m θ ε L] with y hy
    rw [hWeq, hy]
  have hWq (L : I) : ∀ᵐ q ∂lengthChartKernel p n m θ ε L,
      W (exteriorChart n m q) = w L := by
    have hh := (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_eq_fun hW measurable_const)).mpr (hWL L)
    rw [map_chartedExteriorKernel, lengthExteriorKernel,
      Kernel.map_apply _ (measurable_exteriorChart n m)] at hh
    exact (ae_map_iff (measurable_exteriorChart n m).aemeasurable
      (measurableSet_eq_fun hW measurable_const)).mp hh
  calc
    _ = ∫⁻ L, ∫⁻ y, W y.val * a y ∂chartedExteriorKernel p n m θ ε L ∂lengthLaw := by
      apply lintegral_congr
      intro L
      rw [← lintegral_const_mul _ ha]
      exact lintegral_congr_ae ((hWL L).mono fun y hy => congrArg (fun t => t * a y) hy.symm)
    _ = ∫⁻ y, W y.val * a y ∂exteriorLaw := by
      rw [← Measure.lintegral_bind (f := fun y : D => W y.val * a y)
        (Kernel.aemeasurable (chartedExteriorKernel p n m θ ε))
        ((hW.comp measurable_subtype_coe).mul ha).aemeasurable,
        chartedExteriorKernel_comp_lengthMeasure]
    _ = ∫⁻ L, ∫⁻ q, W (exteriorChart n m q) * g q.1.val
        ∂lengthChartKernel p n m θ ε L ∂lengthLaw := by
      have hh := exterior_first_joint_lintegral p n m θ ε
        (f := fun q => W q.1 * g q.2) ((hW.comp measurable_fst).mul (hg.comp measurable_snd))
      simp_rw [lintegral_const_mul _ hg] at hh
      exact hh.symm
    _ = _ := by
      apply lintegral_congr
      intro L
      rw [← lengthChartKernel_active_lintegral p n m θ ε hg L,
        ← lintegral_const_mul (f := fun q :
          AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
            EuclideanSpace ℝ (Fin m) => g q.1.val) _
          (hg.comp (measurable_subtype_coe.comp measurable_fst))]
      exact lintegral_congr_ae ((hWq L).mono fun q hq => congrArg (fun t => t * g q.1.val) hq)

/-- See Proposition 6.6 of the paper: Bayes' identity holds almost
everywhere for the original physical length law. The test may be unbounded. Both sides are nonnegative integrals. -/
theorem bayes_lintegral_ae
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hg : Measurable g) :
    ∀ᵐ L ∂lengthLaw, (∫⁻ y, ∫⁻ u, g u ∂Kphys y ∂chartedExteriorKernel p n m θ ε L) =
      ∫⁻ u, g u ∂LengthAveragingFibres.fibreKernel p n m θ ε L := by
  have := LengthAveragingFibres.lengthMeasure_probability p n m θ ε
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    ((hg.lintegral_kernel (κ := Kphys)).lintegral_kernel)
    (hg.lintegral_kernel (κ := LengthAveragingFibres.fibreKernel p n m θ ε))
  intro S hS _
  have hh := weighted_bayes_lintegral p n m θ ε hg
    (w := S.indicator (fun _ => 1)) (measurable_const.indicator hS)
  have hind (a : I → ℝ≥0∞) :
      (∫⁻ L in S, a L ∂lengthLaw) =
        ∫⁻ L, S.indicator (fun _ => (1 : ℝ≥0∞)) L * a L ∂lengthLaw := by
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro L
    by_cases hL : L ∈ S <;> simp [hL]
  exact (hind _).trans (hh.trans (hind _).symm)

/-- See Proposition 6.6 of the paper: any common length measure absolutely
continuous with respect to the original length law has the same Bayes
identity. In particular this applies to a law dominated by a finite
multiple of the original law. -/
theorem bayes_lintegral_common
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hg : Measurable g)
    (ρ : Measure I) (hρ : ρ ≪ lengthLaw) :
    (∫⁻ L, ∫⁻ y, ∫⁻ u, g u ∂Kphys y ∂chartedExteriorKernel p n m θ ε L ∂ρ) =
      ∫⁻ L, ∫⁻ u, g u ∂LengthAveragingFibres.fibreKernel p n m θ ε L ∂ρ :=
  lintegral_congr_ae (hρ.ae_le (bayes_lintegral_ae p n m θ ε hg))

/-- See Subsection 6.1 of the paper: sampling the fixed-exterior active kernel
after the length-conditioned exterior returns the prescribed active mass
simplex, at every interior length. -/
theorem composed_active_support (L : I) :
    ∀ᵐ u ∂(Kphys ∘ₖ chartedExteriorKernel p n m θ ε) L,
      u ∈ AffineSimplex.massSimplex n L.val := by
  apply Kernel.ae_comp_of_ae_ae (RetainedSimplex.measurableSet_simplex n L.val)
  filter_upwards [exteriorLength_ae p n m θ ε L] with y hy
  have he : ((m + 1 + n : ℕ) + 1 : ℝ) - ∑ i, y.val i = L.val :=
    congrArg Subtype.val hy
  have hh := InterpolantLocalLaws.ae_mem_exterior_simplex p (m + 1) n (by omega)
    (InterpolatingDensities.exteriorPermutation (m + 1) n) θ
    (Real.rpow_pos_of_pos ((by positivity) : (0 : ℝ) < (n + 1 : ℕ)) (-ε))
    (Finset.univ.map (Fin.castLEEmb (show n + 1 ≤ m + 1 + n + 1 by omega))) true y
  filter_upwards [hh] with u hu
  exact ⟨hu.1, hu.2.trans he⟩

/-- Boundary check for Proposition 6.6: constants are
preserved by Bayes averaging at every length, also when either chart has
zero free dimension. -/
theorem bayes_constant (c : ℝ) (L : I) :
    (∫ y, ∫ _u, c ∂Kphys y ∂chartedExteriorKernel p n m θ ε L) = c := by
  simp

/-- Boundary check for Proposition 6.6: the active mass
observable averages to the prescribed length under the exterior-first
composition, at every interior length. -/
theorem bayes_active_mass (L : I) :
    (∫ y, ∫ u, ∑ i, u i ∂Kphys y ∂chartedExteriorKernel p n m θ ε L) = L.val := by
  have hu (y : D) :
      (∫ u, ∑ i, u i ∂Kphys y) = (exteriorLength n m y).val := by
    have hs := InterpolantLocalLaws.ae_mem_exterior_simplex p (m + 1) n (by omega)
      (InterpolatingDensities.exteriorPermutation (m + 1) n) θ
      (Real.rpow_pos_of_pos ((by positivity) : (0 : ℝ) < (n + 1 : ℕ)) (-ε))
      (Finset.univ.map (Fin.castLEEmb (show n + 1 ≤ m + 1 + n + 1 by omega))) true y
    calc
      _ = ∫ _u, (exteriorLength n m y).val ∂Kphys y :=
        integral_congr_ae (hs.mono fun u hu => hu.2)
      _ = _ := by simp
  simp_rw [hu]
  calc
    _ = ∫ _y, L.val ∂chartedExteriorKernel p n m θ ε L :=
      integral_congr_ae ((exteriorLength_ae p n m θ ε L).mono fun y hy =>
        congrArg Subtype.val hy)
    _ = _ := by simp

/-- See Proposition 6.6 of the paper: the composed active law integrates
every block observable. This excludes a junk signed integral in
the Bayes identity. -/
theorem composed_observable_integrable (G : BlockObservable n.succPNat) (L : I) :
    Integrable (fun u => G.val (WithLp.ofLp u))
      ((Kphys ∘ₖ chartedExteriorKernel p n m θ ε) L) := by
  have hg : Measurable (fun u : EuclideanSpace ℝ (Fin (n + 1)) =>
      G.val (WithLp.ofLp u)) := G.property.choose_spec.continuous.measurable.comp
        (WithLp.measurable_ofLp 2 _)
  apply (integrable_const (|G.val 0| + blockDerivativeNorm G * L.val)).mono'
    hg.aestronglyMeasurable
  filter_upwards [composed_active_support p n m θ ε L] with u hu
  exact (Real.norm_eq_abs _).trans_le (CompatibleComparison.block_bound_on_simplex n
    L.property.1 G u hu)

/-- See Proposition 6.6 of the paper: the signed Bayes identity for the
block observable and the every-length coarea average,
almost everywhere under the original length law. -/
theorem bayes_integral_ae (G : BlockObservable n.succPNat) :
    ∀ᵐ L ∂lengthLaw,
      (∫ y, ∫ u, G.val (WithLp.ofLp u) ∂Kphys y ∂chartedExteriorKernel p n m θ ε L) =
        LengthDerivative.averagedObservable p n m θ ε G L := by
  let g := fun u : EuclideanSpace ℝ (Fin (n + 1)) => G.val (WithLp.ofLp u)
  have hg : Measurable g := G.property.choose_spec.continuous.measurable.comp
    (WithLp.measurable_ofLp 2 _)
  have hp := bayes_lintegral_ae p n m θ ε hg.ennreal_ofReal
  have hn := bayes_lintegral_ae p n m θ ε hg.neg.ennreal_ofReal
  filter_upwards [hp, hn] with L hp hn
  simp only [Pi.neg_apply] at hn
  have hi : Integrable g ((Kphys ∘ₖ chartedExteriorKernel p n m θ ε) L) :=
    composed_observable_integrable p n m θ ε G L
  have hf : Integrable g (LengthAveragingFibres.fibreKernel p n m θ ε L) :=
    LengthDerivative.observable_integrable_fibre p n m θ ε G L
  change (∫ y, ∫ u, g u ∂Kphys y ∂chartedExteriorKernel p n m θ ε L) =
    ∫ u, g u ∂LengthAveragingFibres.fibreKernel p n m θ ε L
  rw [← Kernel.integral_comp hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    Kernel.lintegral_comp _ _ L hg.ennreal_ofReal,
    Kernel.lintegral_comp (g := fun u : EuclideanSpace ℝ (Fin (n + 1)) =>
      ENNReal.ofReal (-g u)) _ _ L hg.neg.ennreal_ofReal, hp, hn]

/-- See Proposition 6.6 of the paper: changing to any absolutely continuous
common length law preserves the signed conditional-expectation identity. -/
theorem bayes_integral_common (G : BlockObservable n.succPNat)
    (ρ : Measure I) (hρ : ρ ≪ lengthLaw) :
    (∫ L, ∫ y, ∫ u, G.val (WithLp.ofLp u) ∂Kphys y
      ∂chartedExteriorKernel p n m θ ε L ∂ρ) =
        ∫ L, LengthDerivative.averagedObservable p n m θ ε G L ∂ρ :=
  integral_congr_ae (hρ.ae_le (bayes_integral_ae p n m θ ε G))

/-- A bounded-simplex expectation bound for the observable.
This internal helper is used only to certify finite integrals in the
Bayes step of Proposition 6.6. -/
theorem block_average_bound_internal (G : BlockObservable n.succPNat)
    (σ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) [IsProbabilityMeasure σ]
    {L B : ℝ} (hL : 0 < L) (hLB : L ≤ B)
    (hs : ∀ᵐ u ∂σ, u ∈ AffineSimplex.massSimplex n L) :
    Integrable (fun u => G.val (WithLp.ofLp u)) σ ∧
      |∫ u, G.val (WithLp.ofLp u) ∂σ| ≤ |G.val 0| + blockDerivativeNorm G * B := by
  have hg : Measurable (fun u : EuclideanSpace ℝ (Fin (n + 1)) =>
      G.val (WithLp.ofLp u)) := G.property.choose_spec.continuous.measurable.comp
        (WithLp.measurable_ofLp 2 _)
  have hD : 0 ≤ blockDerivativeNorm G :=
    Finset.sum_nonneg fun i _ => NNReal.coe_nonneg (coordinateDerivativeNorm G i)
  have hb : ∀ᵐ u ∂σ, ‖G.val (WithLp.ofLp u)‖ ≤
      |G.val 0| + blockDerivativeNorm G * B := by
    filter_upwards [hs] with u hu
    rw [Real.norm_eq_abs]
    exact (CompatibleComparison.block_bound_on_simplex n hL G u hu).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hLB hD))
  refine ⟨(integrable_const _).mono' hg.aestronglyMeasurable hb, ?_⟩
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (f := fun u : EuclideanSpace ℝ (Fin (n + 1)) =>
      G.val (WithLp.ofLp u)) hb

/-- See Proposition 6.6 of the paper: the fixed-exterior conditional
expectation is uniformly bounded on its whole compatible exterior carrier. -/
theorem fixed_exterior_average_bound (G : BlockObservable n.succPNat) (y : D) :
    Integrable (fun u => G.val (WithLp.ofLp u)) (Kphys y) ∧
      |∫ u, G.val (WithLp.ofLp u) ∂Kphys y| ≤
        |G.val 0| + blockDerivativeNorm G * ((n + 1 + m : ℕ) + 1 : ℝ) := by
  apply block_average_bound_internal n G (Kphys y)
    (exteriorLength n m y).property.1 (exteriorLength n m y).property.2.le
  exact InterpolantLocalLaws.ae_mem_exterior_simplex p (m + 1) n (by omega)
    (InterpolatingDensities.exteriorPermutation (m + 1) n) θ
    (Real.rpow_pos_of_pos ((by positivity) : (0 : ℝ) < (n + 1 : ℕ)) (-ε))
    (Finset.univ.map (Fin.castLEEmb (show n + 1 ≤ m + 1 + n + 1 by omega))) true y

/-- See Proposition 6.6 of the paper: Bayes' identity for a dominated
common length law, stated on the actual mixed full-exterior law. Both
expectations are integrable, so the signed equality has no junk value. -/
theorem bayes_dominated_common (G : BlockObservable n.succPNat)
    (ρ : Measure I) [IsFiniteMeasure ρ] (C : ℝ≥0∞) (hρ : ρ ≤ C • lengthLaw) :
    Integrable (fun y => ∫ u, G.val (WithLp.ofLp u) ∂Kphys y)
      (chartedExteriorKernel p n m θ ε ∘ₘ ρ) ∧
    Integrable (LengthDerivative.averagedObservable p n m θ ε G) ρ ∧
    (∫ y, ∫ u, G.val (WithLp.ofLp u) ∂Kphys y
      ∂chartedExteriorKernel p n m θ ε ∘ₘ ρ) =
        ∫ L, LengthDerivative.averagedObservable p n m θ ε G L ∂ρ := by
  let g := fun u : EuclideanSpace ℝ (Fin (n + 1)) => G.val (WithLp.ofLp u)
  let F := fun y : D => ∫ u, g u ∂Kphys y
  have hg : Measurable g := G.property.choose_spec.continuous.measurable.comp
    (WithLp.measurable_ofLp 2 _)
  have hFmeas : Measurable F :=
    (hg.stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'.measurable
  let B := |G.val 0| + blockDerivativeNorm G * ((n + 1 + m : ℕ) + 1 : ℝ)
  have hF : Integrable F (chartedExteriorKernel p n m θ ε ∘ₘ ρ) := by
    apply (integrable_const B).mono' hFmeas.aestronglyMeasurable
    exact ae_of_all _ fun y => (Real.norm_eq_abs _).trans_le
      (fixed_exterior_average_bound p n m θ ε G y).2
  have hm : Integrable (LengthDerivative.averagedObservable p n m θ ε G) ρ := by
    apply (integrable_const B).mono'
      (LengthDerivative.measurable_averagedObservable p n m θ ε G).aestronglyMeasurable
    apply ae_of_all
    intro L
    exact (Real.norm_eq_abs _).trans_le (block_average_bound_internal n G
      (LengthAveragingFibres.fibreKernel p n m θ ε L) L.property.1 L.property.2.le
      (LengthDerivative.mem_simplex_ae_fibre p n m θ ε L)).2
  refine ⟨hF, hm, ?_⟩
  calc
    _ = ∫ L, ∫ y, F y ∂chartedExteriorKernel p n m θ ε L ∂ρ := by
      change (∫ y, F y ∂chartedExteriorKernel p n m θ ε ∘ₘ ρ) = _
      rw [Measure.comp_eq_comp_const_apply] at hF ⊢
      simpa only [Kernel.const_apply] using Kernel.integral_comp hF
    _ = _ := bayes_integral_common p n m θ ε G ρ
      (Measure.absolutelyContinuous_of_le_smul hρ)

end Bayes

end Riesz2.TwoVolumeComparison
