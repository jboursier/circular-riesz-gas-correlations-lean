/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.BlockObservable
public import Riesz2.Frozen.ConvergesInLawAlong
public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.GapSecondMoments
public import Riesz2.Frozen.HasIntensity
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.IsMesoscopicSequence
public import Riesz2.Frozen.IsStationary
public import Riesz2.Frozen.LineConfiguration
public import Riesz2.Frozen.LocalConverges
public import Riesz2.Frozen.OffLattice
public import Riesz2.Frozen.OrderedPointDomain
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.RootedConfiguration
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.UniqueRieszLimit
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.ConfigurationMeasure
public import Riesz2.Frozen.ConvergenceRate
public import Riesz2.Frozen.CoordinateDerivativeNorm
public import Riesz2.Frozen.CorrelationFactor
public import Riesz2.Frozen.Count
public import Riesz2.Frozen.DerivativeSup
public import Riesz2.Frozen.Energy
public import Riesz2.Frozen.ExponentA
public import Riesz2.Frozen.ExponentB
public import Riesz2.Frozen.FiniteGapBlock
public import Riesz2.Frozen.Gap
public import Riesz2.Frozen.GapCorrelation
public import Riesz2.Frozen.GapDerivativeNorm
public import Riesz2.Frozen.GapLaw
public import Riesz2.Frozen.GapVector
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.HyperuniformityRatio
public import Riesz2.Frozen.IntervalCount
public import Riesz2.Frozen.LimitingRieszProcess
public import Riesz2.Frozen.LongParameters
public import Riesz2.Frozen.MicroscopicConfiguration
public import Riesz2.Frozen.MicroscopicLaw
public import Riesz2.Frozen.NumberVariance
public import Riesz2.Frozen.OfLong
public import Riesz2.Frozen.OfShort
public import Riesz2.Frozen.OrderedPoint
public import Riesz2.Frozen.PalmKernel
public import Riesz2.Frozen.PalmMeasure
public import Riesz2.Frozen.PalmSpanVariance
public import Riesz2.Frozen.RepulsionProbability
public import Riesz2.Frozen.RestrictConfiguration
public import Riesz2.Frozen.RootedConfigurations
public import Riesz2.Frozen.RootedGap
public import Riesz2.Frozen.RootedGapBlock
public import Riesz2.Frozen.RootedPalmMeasure
public import Riesz2.Frozen.RootedPoint
public import Riesz2.Frozen.ShortEnergy
public import Riesz2.Frozen.ShortGibbsMeasure
public import Riesz2.Frozen.ShortGibbsWeight
public import Riesz2.Frozen.ShortKernel
public import Riesz2.Frozen.ShortKernelLift
public import Riesz2.Frozen.ShortPartitionFunction
public import Riesz2.Frozen.TotalVariation
public import Riesz2.Frozen.TranslateConfiguration



/-!
# Measurability of Campbell rooting

Bounded configuration counts give measurable restricted counting measures. Measurability
of sections for these finite measures yields joint translation measurability, by bounded
exhaustion, and then measurability of the Palm kernel on the original count sigma-algebra.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Riesz2.FrozenSanity

local instance : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- The configuration sigma-algebra makes every bounded Borel count measurable. -/
lemma measurable_count (B : Set ℝ) (hm : MeasurableSet B) (hb : Bornology.IsBounded B) :
    Measurable (fun C : LineConfiguration => count C B) :=
  Measurable.of_comap_le (le_iSup_of_le B (le_iSup_of_le hm (le_iSup_of_le hb le_rfl)))

/-- Evaluation of the associated counting measure agrees with the atom-set count. -/
lemma configurationMeasure_apply (C : LineConfiguration) (B : Set ℝ)
    (hB : MeasurableSet B) : configurationMeasure C B = count C B := by
  unfold configurationMeasure count
  rw [Measure.sum_apply _ hB]
  simp_rw [Measure.dirac_apply' _ hB]
  change (∑' x : C.val, {x : C.val | x.val ∈ B}.indicator (fun _ => (1 : ℝ≥0∞)) x) = _
  rw [← tsum_subtype]
  rw [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Local finiteness makes counts finite on every bounded set, including non-Borel sets. -/
lemma count_lt_top_of_bounded (C : LineConfiguration) (B : Set ℝ)
    (hB : Bornology.IsBounded B) : count C B < ⊤ := by
  obtain ⟨r, hr⟩ := hB.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr
  have hf : (C.val ∩ B).Finite := (C.property (-r) r).subset (by
    intro x hx
    exact ⟨hx.1, hr hx.2⟩)
  unfold count
  rw [← hf.cast_ncard_eq]
  simp

/-- Counting measures restricted to a bounded Borel window form a measurable kernel. -/
lemma measurable_configurationMeasure_restrict (W : Set ℝ) (hW : MeasurableSet W)
    (hb : Bornology.IsBounded W) :
    Measurable (fun C : LineConfiguration => (configurationMeasure C).restrict W) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp_rw [Measure.restrict_apply hB, configurationMeasure_apply _ _ (hB.inter hW)]
  exact measurable_count _ (hB.inter hW) (hb.subset inter_subset_right)

private lemma measurable_counting_section {α : Type*} [MeasurableSpace α]
    (f : α → LineConfiguration) (hf : Measurable f)
    (W : Set ℝ) (hW : MeasurableSet W) (hb : Bornology.IsBounded W)
    (T : Set (α × ℝ)) (hT : MeasurableSet T) :
    Measurable (fun a => configurationMeasure (f a) ((Prod.mk a ⁻¹' T) ∩ W)) := by
  let κ : ProbabilityTheory.Kernel α ℝ :=
    ⟨fun a => (configurationMeasure (f a)).restrict W,
      (measurable_configurationMeasure_restrict W hW hb).comp hf⟩
  have hfinite (a : α) : IsFiniteMeasure (κ a) := by
    constructor
    change (configurationMeasure (f a)).restrict W univ < ⊤
    rw [Measure.restrict_apply_univ, configurationMeasure_apply _ _ hW]
    exact count_lt_top_of_bounded _ _ hb
  have hm :=
    ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hT hfinite
  change Measurable (fun a => (configurationMeasure (f a)).restrict W (Prod.mk a ⁻¹' T)) at hm
  simpa only [Measure.restrict_apply (measurable_prodMk_left hT)] using hm

private lemma count_translate (t : ℝ) (C : LineConfiguration) (B : Set ℝ)
    (hB : MeasurableSet B) :
    count (translateConfiguration t C) B =
      configurationMeasure C ((fun x : ℝ => x - t) ⁻¹' B) := by
  rw [configurationMeasure_apply C ((fun x : ℝ => x - t) ⁻¹' B)
    ((measurable_id.sub_const t) hB)]
  unfold count translateConfiguration
  congr 1
  apply Set.encard_congr
  exact
    { toFun := fun x => ⟨x.val + t, x.property.1, by simpa using x.property.2⟩
      invFun := fun x => ⟨x.val - t, by simpa using x.property.1, x.property.2⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }

/-- Translation is jointly measurable in its displacement and its configuration. -/
lemma measurable_translateConfiguration :
    Measurable (fun p : ℝ × LineConfiguration => translateConfiguration p.1 p.2) := by
  apply Measurable.of_le_map
  change (⨆ (B : Set ℝ) (_ : MeasurableSet B) (_ : Bornology.IsBounded B),
    MeasurableSpace.comap (fun C : LineConfiguration => count C B) inferInstance) ≤ _
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun _hb => ?_
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  rw [MeasurableSpace.map_comp]
  apply Measurable.le_map
  have hm (n : ℕ) : Measurable (fun p : ℝ × LineConfiguration =>
      configurationMeasure p.2 (((fun x : ℝ => x - p.1) ⁻¹' B) ∩
        Metric.closedBall 0 (n : ℝ))) := by
    exact measurable_counting_section Prod.snd measurable_snd
      (Metric.closedBall 0 (n : ℝ)) measurableSet_closedBall Metric.isBounded_closedBall
      {q : (ℝ × LineConfiguration) × ℝ | q.2 - q.1.1 ∈ B}
      ((measurable_snd.sub measurable_fst.fst) hB)
  have he (p : ℝ × LineConfiguration) :
      count (translateConfiguration p.1 p.2) B =
        ⨆ n : ℕ, configurationMeasure p.2 (((fun x : ℝ => x - p.1) ⁻¹' B) ∩
          Metric.closedBall 0 (n : ℝ)) := by
    rw [count_translate _ _ _ hB]
    have hmono : Monotone (fun n : ℕ =>
        ((fun x : ℝ => x - p.1) ⁻¹' B) ∩ Metric.closedBall 0 (n : ℝ)) := by
      intro n m hnm
      exact inter_subset_inter_right _ (Metric.closedBall_subset_closedBall (by exact_mod_cast hnm))
    rw [← hmono.measure_iUnion, ← inter_iUnion, Metric.iUnion_closedBall_nat, inter_univ]
  simpa only [Function.comp_def, he] using Measurable.iSup hm

private lemma palmKernel_apply (C : LineConfiguration) (A : Set LineConfiguration)
    (hA : MeasurableSet A) :
    palmKernel C A = configurationMeasure C
      ((fun x : ℝ => translateConfiguration x C) ⁻¹' A ∩ Ico 0 1) := by
  have ht : Measurable (fun x : ℝ => translateConfiguration x C) :=
    measurable_translateConfiguration.comp (measurable_id.prodMk measurable_const)
  rw [configurationMeasure_apply _ _ ((ht hA).inter measurableSet_Ico)]
  unfold palmKernel count
  rw [Measure.sum_apply _ hA]
  simp_rw [Measure.dirac_apply' _ hA]
  change (∑' x : {x : ℝ // x ∈ C.val ∩ Ico (0 : ℝ) 1},
    {x : {x : ℝ // x ∈ C.val ∩ Ico (0 : ℝ) 1} |
      translateConfiguration x.val C ∈ A}.indicator (fun _ => (1 : ℝ≥0∞)) x) = _
  rw [← tsum_subtype]
  rw [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun x => ⟨x.val.val, x.val.property.1, x.property, x.val.property.2⟩
      invFun := fun x => ⟨⟨x.val, x.property.1, x.property.2.2⟩, x.property.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The finite Campbell rooting kernel is measurable for the bounded-count sigma-algebra. -/
lemma measurable_palmKernel : Measurable palmKernel := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [palmKernel_apply _ _ hA]
  exact measurable_counting_section id measurable_id
    (Ico 0 1) measurableSet_Ico (Metric.isBounded_Ico 0 1)
    {p : LineConfiguration × ℝ | translateConfiguration p.2 p.1 ∈ A}
    ((measurable_translateConfiguration.comp measurable_swap) hA)

end Riesz2.FrozenSanity
