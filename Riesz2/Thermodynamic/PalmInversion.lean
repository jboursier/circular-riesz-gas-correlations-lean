/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.ConfigurationOperations
public import Riesz2.Preliminaries.GapSymmetries
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Reconstruction and Palm inversion

The reconstruction of Subsection 6.3 is defined only on positive gap sequences whose
partial sums diverge in both directions. In particular no configuration is assigned to a
sequence with a finite accumulation point. The suspension construction of Subsection 6.3
uses the configuration sigma-algebra and translation convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

local instance : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See Subsection 6.3 of the paper: the signed finite sum locating the point with label `i`.
The two interval sums give the forward and backward formulas on the whole carrier. -/
def gapPosition (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) : ℝ :=
  (∑ j ∈ Finset.Ico 0 i, (y j : ℝ)) - ∑ j ∈ Finset.Ico i 0, (y j : ℝ)

/-- The distinguished point is at the origin. -/
theorem gapPosition_zero (y : ℤ → Ioi (0 : ℝ)) : gapPosition y 0 = 0 := by
  simp [gapPosition]

/-- Consecutive reconstructed positions have exactly the prescribed gap. -/
theorem gapPosition_add_one (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) :
    gapPosition y (i + 1) = gapPosition y i + (y i : ℝ) := by
  classical
  by_cases hi : 0 ≤ i
  · have h := Finset.sum_Ico_add_eq_sum_Ico_add_one hi (fun j => (y j : ℝ))
    simpa [gapPosition, Finset.Ico_eq_empty_of_le hi,
      Finset.Ico_eq_empty_of_le (by omega : 0 ≤ i + 1)] using h.symm
  · have hi' : i + 1 ≤ 0 := by omega
    have he : Finset.Ico i 0 = insert i (Finset.Ico (i + 1) 0) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hn : i ∉ Finset.Ico (i + 1) 0 := by simp
    simp only [gapPosition, Finset.Ico_eq_empty_of_le (by omega : i ≤ 0),
      Finset.Ico_eq_empty_of_le hi', Finset.sum_empty, zero_sub, he, Finset.sum_insert hn]
    ring

/-- Positivity makes the reconstructed enumeration strictly increasing. -/
theorem gapPosition_strictMono (y : ℤ → Ioi (0 : ℝ)) : StrictMono (gapPosition y) := by
  apply strictMono_int_of_lt_succ
  intro i
  rw [gapPosition_add_one]
  exact lt_add_of_pos_right _ (y i).property

/-- Every individual point position is a measurable finite sum of coordinates. -/
theorem measurable_gapPosition (i : ℤ) : Measurable (fun y : ℤ → Ioi (0 : ℝ) => gapPosition y i) := by
  unfold gapPosition
  exact (Finset.measurable_sum _ fun j _ =>
    measurable_subtype_coe.comp (measurable_pi_apply j)).sub
      (Finset.measurable_sum _ fun j _ =>
        measurable_subtype_coe.comp (measurable_pi_apply j))

/-- See Subsection 6.3 of the paper: precisely the positive sequences whose reconstructed
positions are unbounded in both directions. -/
def reconstructibleGapSequences : Set (ℤ → Ioi (0 : ℝ)) :=
  {y | (∀ r : ℝ, ∃ i : ℤ, r < gapPosition y i) ∧
    ∀ r : ℝ, ∃ i : ℤ, gapPosition y i < r}

/-- Divergence is a Borel condition, tested using integer thresholds. -/
theorem measurableSet_reconstructibleGapSequences : MeasurableSet reconstructibleGapSequences := by
  have he : reconstructibleGapSequences =
      (⋂ n : ℤ, ⋃ i : ℤ, {y | (n : ℝ) < gapPosition y i}) ∩
        (⋂ n : ℤ, ⋃ i : ℤ, {y | gapPosition y i < (n : ℝ)}) := by
    ext y
    simp only [reconstructibleGapSequences, mem_ofPred_eq, mem_inter_iff,
      mem_iInter, mem_iUnion]
    constructor
    · exact fun h => ⟨fun n => h.1 n, fun n => h.2 n⟩
    · rintro ⟨hp, hm⟩
      constructor
      · intro r
        obtain ⟨n, hn⟩ := exists_int_gt r
        obtain ⟨i, hi⟩ := hp n
        exact ⟨i, hn.trans hi⟩
      · intro r
        obtain ⟨n, hn⟩ := exists_int_lt r
        obtain ⟨i, hi⟩ := hm n
        exact ⟨i, hi.trans hn⟩
  rw [he]
  exact (MeasurableSet.iInter fun n : ℤ => MeasurableSet.iUnion fun i : ℤ =>
    measurableSet_lt measurable_const (measurable_gapPosition i)).inter
      (MeasurableSet.iInter fun n : ℤ => MeasurableSet.iUnion fun i : ℤ =>
        measurableSet_lt (measurable_gapPosition i) measurable_const)

/-- See Subsection 6.3 of the paper: reconstruction on its actual domain. -/
def reconstructConfiguration (y : reconstructibleGapSequences) : LineConfiguration :=
  ⟨range (gapPosition y.val), fun a b => by
    obtain ⟨i, hi⟩ := y.property.2 a
    obtain ⟨j, hj⟩ := y.property.1 b
    apply ((Finset.Icc i j).finite_toSet.image (gapPosition y.val)).subset
    rintro x ⟨⟨k, rfl⟩, hk⟩
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · exact le_of_lt ((gapPosition_strictMono y.val).lt_iff_lt.mp (hi.trans_le hk.1))
    · exact le_of_lt ((gapPosition_strictMono y.val).lt_iff_lt.mp (hk.2.trans_lt hj))⟩

/-- The reconstruction lies in the bi-infinite rooted carrier. -/
theorem reconstructConfiguration_mem_rootedConfigurations (y : reconstructibleGapSequences) :
    reconstructConfiguration y ∈ rootedConfigurations := by
  refine ⟨⟨0, gapPosition_zero y.val⟩, ?_, ?_⟩
  · intro r
    obtain ⟨i, hi⟩ := y.property.1 r
    exact ⟨gapPosition y.val i, ⟨i, rfl⟩, hi⟩
  · intro r
    obtain ⟨i, hi⟩ := y.property.2 r
    exact ⟨gapPosition y.val i, ⟨i, rfl⟩, hi⟩

/-- Rooted version of the same reconstruction, using the carrier. -/
def reconstructRootedConfiguration (y : reconstructibleGapSequences) : RootedConfiguration :=
  ⟨reconstructConfiguration y, reconstructConfiguration_mem_rootedConfigurations y⟩

/-- Counts of the reconstruction are sums over its distinct labelled points. -/
theorem count_reconstructConfiguration (y : reconstructibleGapSequences) (B : Set ℝ) :
    count (reconstructConfiguration y) B =
      ∑' i : ℤ, B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y.val i) := by
  classical
  have he : (fun i : ℤ => B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y.val i)) =
      {i : ℤ | gapPosition y.val i ∈ B}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext i
    by_cases hi : gapPosition y.val i ∈ B <;> simp [hi]
  rw [he, ← tsum_subtype, ENNReal.tsum_one]
  unfold count
  congr 1
  symm
  apply ENat.card_congr
  exact Equiv.ofBijective
    (fun i : {i : ℤ | gapPosition y.val i ∈ B} =>
      (⟨gapPosition y.val i.val, ⟨i.val, rfl⟩, i.property⟩ :
        {x : ℝ // x ∈ (reconstructConfiguration y).val ∩ B}))
    ⟨fun i j h => Subtype.ext ((gapPosition_strictMono y.val).injective
      (congrArg Subtype.val h)), fun ⟨x, ⟨i, hi⟩, hx⟩ =>
        ⟨⟨i, by change gapPosition y.val i ∈ B; rw [hi]; exact hx⟩, Subtype.ext hi⟩⟩

/-- See Subsection 6.3 of the paper: reconstruction is measurable for the bounded-count sigma-algebra. -/
theorem measurable_reconstructConfiguration : Measurable reconstructConfiguration := by
  apply measurable_configuration_of_counts
  intro B hB _
  simp_rw [count_reconstructConfiguration]
  exact Measurable.tsum fun i =>
    (measurable_const.indicator hB).comp
      ((measurable_gapPosition i).comp measurable_subtype_coe)

/-- The same reconstruction is measurable with values in the rooted carrier. -/
theorem measurable_reconstructRootedConfiguration : Measurable reconstructRootedConfiguration :=
  measurable_reconstructConfiguration.subtype_mk

/-- Reindexing a gap sequence subtracts the position of its new root. -/
theorem gapPosition_reindex (y : ℤ → Ioi (0 : ℝ)) (a i : ℤ) :
    gapPosition (fun j => y (j + a)) i = gapPosition y (i + a) - gapPosition y a := by
  induction i using Int.induction_on with
  | zero => simp [gapPosition_zero]
  | succ i hi =>
    rw [gapPosition_add_one, hi]
    rw [show i + 1 + a = (i + a) + 1 by omega, gapPosition_add_one]
    ring
  | pred i hi =>
    have h1 := gapPosition_add_one (fun j => y (j + a)) (-(i : ℤ) - 1)
    have h2 := gapPosition_add_one y (-(i : ℤ) - 1 + a)
    simp only [sub_add_cancel, show -(i : ℤ) - 1 + a + 1 = -(i : ℤ) + a by omega] at h1 h2
    rw [hi] at h1
    linarith

/-- Every integer reindexing preserves the reconstruction domain. -/
theorem reindex_mem_reconstructibleGapSequences (y : reconstructibleGapSequences) (a : ℤ) :
    (fun j => y.val (j + a)) ∈ reconstructibleGapSequences := by
  constructor
  · intro r
    obtain ⟨i, hi⟩ := y.property.1 (r + gapPosition y.val a)
    refine ⟨i - a, ?_⟩
    rw [gapPosition_reindex, sub_add_cancel]
    linarith
  · intro r
    obtain ⟨i, hi⟩ := y.property.2 (r + gapPosition y.val a)
    refine ⟨i - a, ?_⟩
    rw [gapPosition_reindex, sub_add_cancel]
    linarith

/-- Integer reindexing on the true reconstruction carrier. -/
def reindexReconstructibleGaps (a : ℤ) (y : reconstructibleGapSequences) :
    reconstructibleGapSequences :=
  ⟨fun j => y.val (j + a), reindex_mem_reconstructibleGapSequences y a⟩

/-- Reindexing on the reconstruction carrier is measurable. -/
theorem measurable_reindexReconstructibleGaps (a : ℤ) : Measurable (reindexReconstructibleGaps a) :=
  (show Measurable (fun y : reconstructibleGapSequences => fun i => y.val (i + a)) from
    measurable_pi_iff.mpr fun i =>
      (measurable_pi_apply (i + a)).comp measurable_subtype_coe).subtype_mk

/-- See the proof of Theorem 3 in the paper: the deterministic root-shift
identity underlying stationarity and the Campbell computation. -/
theorem reconstructConfiguration_reindex (y : reconstructibleGapSequences) (a : ℤ) :
    reconstructConfiguration (reindexReconstructibleGaps a y) =
      translateConfiguration (gapPosition y.val a) (reconstructConfiguration y) := by
  apply Subtype.ext
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change gapPosition (fun j => y.val (j + a)) i + gapPosition y.val a ∈
      range (gapPosition y.val)
    rw [gapPosition_reindex, sub_add_cancel]
    exact ⟨i + a, rfl⟩
  · rintro ⟨i, hi⟩
    refine ⟨i - a, ?_⟩
    change gapPosition (fun j => y.val (j + a)) (i - a) = x
    rw [gapPosition_reindex, sub_add_cancel]
    change gapPosition y.val i = x + gapPosition y.val a at hi
    linarith

/-- The measurable suspension strip, with a half-open convention at gap endpoints. -/
def gapSuspensionStrip : Set (reconstructibleGapSequences × ℝ) :=
  {p | p.2 ∈ Ico (0 : ℝ) (p.1.val 0 : ℝ)}

/-- The moving upper endpoint of the suspension strip is measurable. -/
theorem measurableSet_gapSuspensionStrip : MeasurableSet gapSuspensionStrip := by
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd
      (measurable_subtype_coe.comp ((measurable_pi_apply 0).comp
        (measurable_subtype_coe.comp measurable_fst))))

/-- Spatial configuration seen at an offset inside the distinguished gap. -/
def gapSuspensionConfiguration (p : reconstructibleGapSequences × ℝ) : LineConfiguration :=
  translateConfiguration p.2 (reconstructConfiguration p.1)

/-- Joint measurability of the offset and the reconstructed configuration. -/
theorem measurable_gapSuspensionConfiguration : Measurable gapSuspensionConfiguration :=
  measurable_translateConfiguration.comp
    (measurable_snd.prodMk (measurable_reconstructConfiguration.comp measurable_fst))

/-- See Subsection 6.3 of the paper: the suspension measure, before normalization.
It has its full meaning for every measure on the actual reconstruction carrier. -/
def gapSuspensionMeasure (q : Measure reconstructibleGapSequences) : Measure LineConfiguration :=
  ((q.prod volume).restrict gapSuspensionStrip).map gapSuspensionConfiguration

/-- See Subsection 6.3 of the paper: the nonnegative expectation formula for suspension. -/
theorem lintegral_gapSuspensionMeasure (q : Measure reconstructibleGapSequences) [SFinite q]
    (f : LineConfiguration → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ C, f C ∂gapSuspensionMeasure q) =
      ∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        f (translateConfiguration u (reconstructConfiguration y)) ∂volume ∂q := by
  rw [gapSuspensionMeasure, lintegral_map hf measurable_gapSuspensionConfiguration,
    ← lintegral_indicator measurableSet_gapSuspensionStrip]
  change (∫⁻ p, (gapSuspensionStrip.indicator (f ∘ gapSuspensionConfiguration)) p
    ∂q.prod volume) = _
  rw [lintegral_prod _ ((hf.comp measurable_gapSuspensionConfiguration).indicator
    measurableSet_gapSuspensionStrip).aemeasurable]
  apply lintegral_congr
  intro y
  exact lintegral_indicator
    (measurableSet_Ico : MeasurableSet (Ico (0 : ℝ) (y.val 0 : ℝ))) _

/-- See Subsection 6.3 of the paper: the mass is the expected length of the distinguished gap. -/
theorem gapSuspensionMeasure_univ (q : Measure reconstructibleGapSequences) [SFinite q] :
    gapSuspensionMeasure q univ = ∫⁻ y, ENNReal.ofReal (y.val 0 : ℝ) ∂q := by
  have h := lintegral_gapSuspensionMeasure q (fun _ => 1) measurable_const
  simpa only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero] using h

/-- Mean one normalizes the suspension, with integrability stated explicitly. -/
theorem gapSuspensionMeasure_probability (q : Measure reconstructibleGapSequences) [SFinite q]
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) :
    IsProbabilityMeasure (gapSuspensionMeasure q) := by
  constructor
  rw [gapSuspensionMeasure_univ, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => (y.val 0).property.le), hm, ENNReal.ofReal_one]

/-- The normalized candidate in the point-process carrier. See Subsection 6.3 of the paper. -/
def gapSuspensionProcess (q : Measure reconstructibleGapSequences) [SFinite q]
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) : PointProcess :=
  ⟨gapSuspensionMeasure q, gapSuspensionMeasure_probability q hi hm⟩

/-- Translation composes according to addition, with the negative-sign convention. -/
theorem translateConfiguration_add (a b : ℝ) (C : LineConfiguration) :
    translateConfiguration a (translateConfiguration b C) = translateConfiguration (a + b) C := by
  apply Subtype.ext
  ext x
  change (x + a) + b ∈ C.val ↔ x + (a + b) ∈ C.val
  rw [add_assoc]

/-- Translation by zero fixes every configuration. -/
theorem translateConfiguration_zero (C : LineConfiguration) : translateConfiguration 0 C = C := by
  apply Subtype.ext
  ext x
  change x + 0 ∈ C.val ↔ x ∈ C.val
  rw [add_zero]

private theorem suspension_lintegral_Ico_add (f : ℝ → ℝ≥0∞) (a b c : ℝ) :
    (∫⁻ u in Ico a b, f (u + c) ∂volume) =
      ∫⁻ u in Ico (a + c) (b + c), f u ∂volume := by
  rw [← lintegral_indicator measurableSet_Ico,
    ← lintegral_indicator measurableSet_Ico]
  have he : (fun u => (Ico a b).indicator (fun u => f (u + c)) u) =
      fun u => (Ico (a + c) (b + c)).indicator f (u + c) := by
    ext u
    simp only [indicator_apply, mem_Ico]
    congr 1
    exact propext ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
      fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  rw [he, lintegral_add_right_eq_self]

private theorem suspension_lintegral_Ico_balance (f : ℝ → ℝ≥0∞) (a r : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) :
    (∫⁻ u in Ico a (r + a), f u ∂volume) + (∫⁻ u in Ico 0 a, f u ∂volume) =
      (∫⁻ u in Ico 0 r, f u ∂volume) + (∫⁻ u in Ico r (r + a), f u ∂volume) := by
  have h1 := lintegral_union (μ := volume) (f := f)
    (A := Ico (0 : ℝ) a) (B := Ico a (r + a)) measurableSet_Ico Ico_disjoint_Ico_same
  have h2 := lintegral_union (μ := volume) (f := f)
    (A := Ico (0 : ℝ) r) (B := Ico r (r + a)) measurableSet_Ico Ico_disjoint_Ico_same
  rw [Ico_union_Ico_eq_Ico ha (by linarith)] at h1
  rw [Ico_union_Ico_eq_Ico hr (by linarith)] at h2
  exact (add_comm _ _).trans (h1.symm.trans h2)

/-- Integrating a jointly measurable test over a fixed time interval is measurable. -/
theorem measurable_suspension_fixed_interval (f : LineConfiguration → ℝ≥0∞)
    (hf : Measurable f) (a b : ℝ) :
    Measurable (fun y : reconstructibleGapSequences =>
      ∫⁻ u in Ico a b, f (translateConfiguration u (reconstructConfiguration y)) ∂volume) :=
  (hf.comp measurable_gapSuspensionConfiguration).lintegral_prod_right'

/-- Integrating a jointly measurable test over the distinguished gap is measurable. -/
theorem measurable_suspension_gap_interval (f : LineConfiguration → ℝ≥0∞)
    (hf : Measurable f) :
    Measurable (fun y : reconstructibleGapSequences =>
      ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        f (translateConfiguration u (reconstructConfiguration y)) ∂volume) := by
  have h := ((hf.comp measurable_gapSuspensionConfiguration).indicator
    measurableSet_gapSuspensionStrip).lintegral_prod_right' (ν := volume)
  convert h using 1
  ext y
  exact (lintegral_indicator
    (measurableSet_Ico : MeasurableSet (Ico (0 : ℝ) (y.val 0 : ℝ))) _).symm

/-- Internal stationarity implication from the shift clause of
the proof of Theorem 3. No convergence or Campbell identity
is assumed: the moving-interval boundary terms cancel by index invariance. -/
theorem gapSuspensionMeasure_stationary_internal (q : Measure reconstructibleGapSequences)
    [IsProbabilityMeasure q]
    (hshift : q.map (reindexReconstructibleGaps 1) = q)
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) :
    IsStationary (gapSuspensionProcess q hi hm) := by
  have := gapSuspensionMeasure_probability q hi hm
  have hpos (a : ℝ) (ha : 0 ≤ a) :
      (gapSuspensionMeasure q).map (translateConfiguration a) = gapSuspensionMeasure q := by
    apply Measure.ext
    intro B hB
    let f : LineConfiguration → ℝ≥0∞ := B.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator hB
    let F (y : reconstructibleGapSequences) (u : ℝ) :=
      f (translateConfiguration u (reconstructConfiguration y))
    have hroof (y : reconstructibleGapSequences) (u : ℝ) :
        F y (u + (y.val 0 : ℝ)) = F (reindexReconstructibleGaps 1 y) u := by
      dsimp [F]
      rw [reconstructConfiguration_reindex, translateConfiguration_add]
      congr 2
      have he := gapPosition_add_one y.val 0
      have hz : gapPosition y.val 1 = (y.val 0 : ℝ) := by
        simpa only [gapPosition_zero, zero_add] using he
      rw [hz]
    have hboundary :
        (∫⁻ y, ∫⁻ u in Ico (y.val 0 : ℝ) ((y.val 0 : ℝ) + a), F y u ∂volume ∂q) =
          ∫⁻ y, ∫⁻ u in Ico 0 a, F y u ∂volume ∂q := by
      calc
        _ = ∫⁻ y, ∫⁻ u in Ico (0 : ℝ) a, F (reindexReconstructibleGaps 1 y) u ∂volume ∂q := by
          apply lintegral_congr
          intro y
          calc
            _ = ∫⁻ u in Ico (0 : ℝ) a, F y (u + (y.val 0 : ℝ)) ∂volume := by
              simpa only [zero_add, add_comm a] using
                (suspension_lintegral_Ico_add (F y) 0 a (y.val 0 : ℝ)).symm
            _ = _ := by simp_rw [hroof]
        _ = _ := by
          have he := (lintegral_map (μ := q)
            (measurable_suspension_fixed_interval f hf 0 a)
            (measurable_reindexReconstructibleGaps 1)).symm
          rw [hshift] at he
          exact he
    have hmeas0 := measurable_suspension_fixed_interval f hf 0 a
    have hmeasgap := measurable_suspension_gap_interval f hf
    have hsum :
        (∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ), F y (u + a) ∂volume ∂q) +
            (∫⁻ y, ∫⁻ u in Ico 0 a, F y u ∂volume ∂q) =
          (∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ), F y u ∂volume ∂q) +
            (∫⁻ y, ∫⁻ u in Ico 0 a, F y u ∂volume ∂q) := by
      rw [← hboundary]
      conv_lhs =>
        enter [1, 2, y]
        rw [suspension_lintegral_Ico_add, zero_add]
      rw [hboundary, ← lintegral_add_right _ hmeas0]
      rw [← hboundary, ← lintegral_add_left hmeasgap]
      apply lintegral_congr
      intro y
      exact suspension_lintegral_Ico_balance (F y) a (y.val 0 : ℝ) ha (y.val 0).property.le
    have hfin : (∫⁻ y, ∫⁻ u in Ico 0 a, F y u ∂volume ∂q) ≠ ⊤ := by
      apply ne_of_lt
      calc
        _ ≤ ∫⁻ _y : reconstructibleGapSequences, ∫⁻ _u in Ico (0 : ℝ) a, 1 ∂volume ∂q :=
          lintegral_mono fun y => lintegral_mono fun u => by
            classical
            by_cases h : translateConfiguration u (reconstructConfiguration y) ∈ B
            · simp [F, f, h]
            · simp [F, f, h]
        _ = ENNReal.ofReal a := by simp
        _ < ⊤ := ENNReal.ofReal_lt_top
    have he := (ENNReal.add_left_inj hfin).mp hsum
    calc
      _ = ∫⁻ C, f (translateConfiguration a C) ∂gapSuspensionMeasure q := by
        rw [Measure.map_apply (measurable_translateConfiguration_const a) hB]
        exact (lintegral_indicator_one ((measurable_translateConfiguration_const a) hB)).symm
      _ = ∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ), F y (u + a) ∂volume ∂q := by
        change (∫⁻ C, (f ∘ translateConfiguration a) C ∂gapSuspensionMeasure q) = _
        rw [lintegral_gapSuspensionMeasure q _ (hf.comp (measurable_translateConfiguration_const a))]
        dsimp only [Function.comp_def]
        simp_rw [translateConfiguration_add, add_comm a]
        rfl
      _ = ∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ), F y u ∂volume ∂q := he
      _ = _ := by rw [← lintegral_gapSuspensionMeasure q f hf]; exact lintegral_indicator_one hB
  intro a
  change (gapSuspensionMeasure q).map (translateConfiguration a) = gapSuspensionMeasure q
  by_cases ha : 0 ≤ a
  · exact hpos a ha
  · have hn := hpos (-a) (by linarith)
    have h := congrArg (fun μ : Measure LineConfiguration => μ.map (translateConfiguration a)) hn
    rw [Measure.map_map (measurable_translateConfiguration_const a)
      (measurable_translateConfiguration_const (-a))] at h
    have he : (translateConfiguration a ∘ translateConfiguration (-a)) = id := by
      funext C
      simp [translateConfiguration_add, translateConfiguration_zero]
    rw [he, Measure.map_id] at h
    exact h.symm

/-- The half-open cells between consecutive reconstructed points partition the line. -/
theorem gapPosition_cells_cover (y : reconstructibleGapSequences) :
    (⋃ i : ℤ, Ico (gapPosition y.val i) (gapPosition y.val (i + 1))) = univ := by
  classical
  apply eq_univ_of_forall
  intro r
  obtain ⟨i, hi⟩ := y.property.2 r
  obtain ⟨j, hj⟩ := y.property.1 r
  let S := {k ∈ Finset.Icc i j | gapPosition y.val k ≤ r}
  have hij : i ≤ j := (gapPosition_strictMono y.val).le_iff_le.mp (hi.le.trans hj.le)
  have hn : S.Nonempty := ⟨i, by simp [S, hij, hi.le]⟩
  let k := S.max' hn
  have hk := Finset.mem_filter.mp (Finset.max'_mem S hn)
  have hkr : r < gapPosition y.val (k + 1) := by
    by_contra hkr
    have hk1 : k + 1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by have := (Finset.mem_Icc.mp hk.1).1; omega, ?_⟩, le_of_not_gt hkr⟩
      have := (gapPosition_strictMono y.val).lt_iff_lt.mp
        ((le_of_not_gt hkr).trans_lt hj)
      omega
    have := Finset.le_max' S (k + 1) hk1
    change k + 1 ≤ k at this
    omega
  exact mem_iUnion.mpr ⟨k, hk.2, hkr⟩

/-- Tonelli over the gap partition, with no integrability assumption. -/
theorem tsum_lintegral_gapPosition_cells (y : reconstructibleGapSequences) (f : ℝ → ℝ≥0∞) :
    (∑' i : ℤ, ∫⁻ u in Ico (gapPosition y.val i) (gapPosition y.val (i + 1)), f u ∂volume) =
      ∫⁻ u, f u ∂volume := by
  have hd := (gapPosition_strictMono y.val).monotone.pairwise_disjoint_on_Ico_succ
  have he := lintegral_iUnion (μ := volume)
    (s := fun i : ℤ => Ico (gapPosition y.val i) (gapPosition y.val (i + 1)))
    (fun _ => measurableSet_Ico) hd f
  rw [gapPosition_cells_cover, Measure.restrict_univ] at he
  exact he.symm

/-- Composing two integer reindexings adds their displacements. -/
theorem reindexReconstructibleGaps_add (a b : ℤ) (y : reconstructibleGapSequences) :
    reindexReconstructibleGaps a (reindexReconstructibleGaps b y) =
      reindexReconstructibleGaps (a + b) y := by
  apply Subtype.ext
  funext j
  change y.val (j + a + b) = y.val (j + (a + b))
  rw [add_assoc]

/-- Reindexing by zero fixes the sequence. -/
theorem reindexReconstructibleGaps_zero (y : reconstructibleGapSequences) :
    reindexReconstructibleGaps 0 y = y := by
  apply Subtype.ext
  funext j
  exact congrArg y.val (add_zero j)

private theorem measurable_campbell_index_integral
    (f : ℝ × LineConfiguration → ℝ≥0∞) (hf : Measurable f) (i : ℤ) :
    Measurable (fun y : reconstructibleGapSequences =>
      ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        f (gapPosition y.val i - u,
          reconstructConfiguration (reindexReconstructibleGaps i y)) ∂volume) := by
  have hm : Measurable (fun p : reconstructibleGapSequences × ℝ =>
      f (gapPosition p.1.val i - p.2,
        reconstructConfiguration (reindexReconstructibleGaps i p.1))) :=
    hf.comp ((((measurable_gapPosition i).comp
      (measurable_subtype_coe.comp measurable_fst)).sub measurable_snd).prodMk
        (measurable_reconstructConfiguration.comp
          ((measurable_reindexReconstructibleGaps i).comp measurable_fst)))
  have h := (hm.indicator measurableSet_gapSuspensionStrip).lintegral_prod_right' (ν := volume)
  convert h using 1
  ext y
  exact (lintegral_indicator
    (measurableSet_Ico : MeasurableSet (Ico (0 : ℝ) (y.val 0 : ℝ))) _).symm

/-- Internal Campbell computation from the index-invariance clause of the proof of Theorem 3. Shifting each summand moves its integration
interval to a member of the partition of the entire line. -/
theorem gapSuspension_campbell_indices_internal (q : Measure reconstructibleGapSequences)
    [SFinite q] (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (f : ℝ × LineConfiguration → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, ∑' i : ℤ, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
      f (gapPosition y.val i - u,
        reconstructConfiguration (reindexReconstructibleGaps i y)) ∂volume ∂q) =
      ∫⁻ y, ∫⁻ x, f (x, reconstructConfiguration y) ∂volume ∂q := by
  rw [lintegral_tsum (fun i => (measurable_campbell_index_integral f hf i).aemeasurable)]
  have he (i : ℤ) :
      (∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        f (gapPosition y.val i - u,
          reconstructConfiguration (reindexReconstructibleGaps i y)) ∂volume ∂q) =
      ∫⁻ y, ∫⁻ v in Ico (gapPosition y.val (-i)) (gapPosition y.val (-i + 1)),
        f (-v, reconstructConfiguration y) ∂volume ∂q := by
    calc
      _ = ∫⁻ y, ∫⁻ u in Ico (0 : ℝ) ((reindexReconstructibleGaps (-i) y).val 0 : ℝ),
          f (gapPosition (reindexReconstructibleGaps (-i) y).val i - u,
            reconstructConfiguration (reindexReconstructibleGaps i
              (reindexReconstructibleGaps (-i) y))) ∂volume ∂q := by
        have hm := (lintegral_map (μ := q) (measurable_campbell_index_integral f hf i)
          (measurable_reindexReconstructibleGaps (-i)))
        rw [hshift] at hm
        exact hm
      _ = _ := by
        apply lintegral_congr
        intro y
        simp only [reindexReconstructibleGaps_add, add_neg_cancel,
          reindexReconstructibleGaps_zero]
        simp only [reindexReconstructibleGaps, zero_add]
        rw [gapPosition_reindex, add_neg_cancel, gapPosition_zero, zero_sub]
        have hc := suspension_lintegral_Ico_add
          (fun v => f (-v, reconstructConfiguration y)) 0 (y.val (-i) : ℝ)
          (gapPosition y.val (-i))
        simp only [zero_add] at hc
        rw [show (y.val (-i) : ℝ) + gapPosition y.val (-i) =
          gapPosition y.val (-i + 1) by rw [gapPosition_add_one]; ring] at hc
        simpa only [neg_add_rev, sub_eq_add_neg] using hc
  simp_rw [he]
  have hm (i : ℤ) : Measurable (fun y : reconstructibleGapSequences =>
      ∫⁻ v in Ico (gapPosition y.val (-i)) (gapPosition y.val (-i + 1)),
        f (-v, reconstructConfiguration y) ∂volume) := by
    have hc := ((measurable_campbell_index_integral f hf i).comp
      (measurable_reindexReconstructibleGaps (-i)))
    dsimp only [Function.comp_def] at hc
    convert hc using 1
    ext y
    simp only [reindexReconstructibleGaps_add, add_neg_cancel,
      reindexReconstructibleGaps_zero]
    simp only [reindexReconstructibleGaps, zero_add]
    rw [gapPosition_reindex, add_neg_cancel, gapPosition_zero, zero_sub]
    have hc := suspension_lintegral_Ico_add
      (fun v => f (-v, reconstructConfiguration y)) 0 (y.val (-i) : ℝ)
      (gapPosition y.val (-i))
    simp only [zero_add] at hc
    rw [show (y.val (-i) : ℝ) + gapPosition y.val (-i) =
      gapPosition y.val (-i + 1) by rw [gapPosition_add_one]; ring] at hc
    simpa only [neg_add_rev, sub_eq_add_neg] using hc.symm
  rw [← lintegral_tsum (fun i => (hm i).aemeasurable)]
  apply lintegral_congr
  intro y
  have hn := (Equiv.neg ℤ).tsum_eq
    (fun i : ℤ => ∫⁻ v in Ico (gapPosition y.val i) (gapPosition y.val (i + 1)),
      f (-v, reconstructConfiguration y) ∂volume)
  change (∑' i : ℤ, ∫⁻ v in Ico (gapPosition y.val (-i)) (gapPosition y.val (-i + 1)),
    f (-v, reconstructConfiguration y) ∂volume) = _ at hn
  rw [hn, tsum_lintegral_gapPosition_cells]
  exact lintegral_neg_eq_self (fun u : ℝ => f (u, reconstructConfiguration y))

/-- Translation of the labelled reconstruction gives its shifted atom positions. -/
theorem count_translate_reconstructConfiguration (y : reconstructibleGapSequences)
    (u : ℝ) (B : Set ℝ) :
    count (translateConfiguration u (reconstructConfiguration y)) B =
      ∑' i : ℤ, B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y.val i - u) := by
  classical
  have he : count (translateConfiguration u (reconstructConfiguration y)) B =
      count (reconstructConfiguration y) ((fun x : ℝ => x - u) ⁻¹' B) := by
    unfold count translateConfiguration
    congr 1
    apply Set.encard_congr
    exact
      { toFun := fun x => ⟨x.val + u, x.property.1, by simpa using x.property.2⟩
        invFun := fun x => ⟨x.val - u, by simpa using x.property.1, x.property.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun x => by ext; simp }
  rw [he, count_reconstructConfiguration]
  congr 1

/-- Internal intensity consequence of the proof of Theorem 3.
The proof sums the actual counts and uses the Campbell partition identity. -/
theorem gapSuspensionMeasure_intensity_internal (q : Measure reconstructibleGapSequences)
    [IsProbabilityMeasure q]
    (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) :
    HasIntensity (gapSuspensionProcess q hi hm) 1 := by
  intro B hB _
  change (∫⁻ C, count C B ∂gapSuspensionMeasure q) = _
  rw [lintegral_gapSuspensionMeasure q _ (measurable_count B hB)]
  simp_rw [count_translate_reconstructConfiguration]
  have he (y : reconstructibleGapSequences) :
      (∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        ∑' i : ℤ, B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y.val i - u) ∂volume) =
      ∑' i : ℤ, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y.val i - u) ∂volume :=
    lintegral_tsum fun _ =>
      ((measurable_const.indicator hB).comp (measurable_const.sub measurable_id)).aemeasurable
  simp_rw [he]
  have h := gapSuspension_campbell_indices_internal q hshift
    (fun p : ℝ × LineConfiguration => B.indicator (fun _ => (1 : ℝ≥0∞)) p.1)
    ((measurable_const.indicator hB).comp measurable_fst)
  rw [h]
  simp only [lintegral_const, measure_univ,
    mul_one, ENNReal.coe_one, one_mul]
  exact lintegral_indicator_one hB

/-- The Campbell kernel on a translated reconstruction is the sum over
exactly those labels whose shifted positions lie in `[0,1)`. -/
theorem palmKernel_apply_translate_reconstructConfiguration
    (y : reconstructibleGapSequences) (u : ℝ) (A : Set LineConfiguration)
    (hA : MeasurableSet A) :
    palmKernel (translateConfiguration u (reconstructConfiguration y)) A =
      ∑' i : ℤ, (Ico (0 : ℝ) 1).indicator (fun _ =>
        A.indicator (fun _ => (1 : ℝ≥0∞))
          (reconstructConfiguration (reindexReconstructibleGaps i y)))
        (gapPosition y.val i - u) := by
  classical
  let C := translateConfiguration u (reconstructConfiguration y)
  let S := {i : ℤ | gapPosition y.val i - u ∈ Ico (0 : ℝ) 1}
  let e : S ≃ {x : ℝ // x ∈ C.val ∩ Ico (0 : ℝ) 1} := Equiv.ofBijective
    (fun i => ⟨gapPosition y.val i.val - u, by
      refine ⟨?_, i.property⟩
      change gapPosition y.val i.val - u + u ∈ range (gapPosition y.val)
      exact ⟨i.val, (sub_add_cancel _ _).symm⟩⟩)
    ⟨fun i j h => Subtype.ext ((gapPosition_strictMono y.val).injective (by
      have he := congrArg Subtype.val h
      change gapPosition y.val i.val - u = gapPosition y.val j.val - u at he
      linarith)), by
        rintro ⟨x, hx, hI⟩
        obtain ⟨i, hi⟩ := hx
        change gapPosition y.val i = x + u at hi
        refine ⟨⟨i, ?_⟩, ?_⟩
        · change gapPosition y.val i - u ∈ Ico (0 : ℝ) 1
          simpa only [hi, add_sub_cancel_right] using hI
        · apply Subtype.ext
          change gapPosition y.val i - u = x
          linarith⟩
  change (Measure.sum (fun x : {x : ℝ // x ∈ C.val ∩ Ico (0 : ℝ) 1} =>
    Measure.dirac (translateConfiguration x.val C))) A = _
  rw [Measure.sum_apply _ hA, ← e.tsum_eq]
  have hr (i : S) : translateConfiguration (e i).val C =
      reconstructConfiguration (reindexReconstructibleGaps i.val y) := by
    change translateConfiguration (gapPosition y.val i.val - u)
      (translateConfiguration u (reconstructConfiguration y)) = _
    rw [translateConfiguration_add, sub_add_cancel,
      reconstructConfiguration_reindex]
  simp_rw [hr, Measure.dirac_apply' _ hA]
  simp only [Pi.one_def]
  rw [tsum_subtype S (fun j : ℤ =>
    A.indicator (fun _ => (1 : ℝ≥0∞))
      (reconstructConfiguration (reindexReconstructibleGaps j y)))]
  congr 1

/-- Internal Palm identification in exactly the Campbell definition.
There is no limiting Campbell premise. -/
theorem gapSuspensionMeasure_palm_internal (q : Measure reconstructibleGapSequences)
    [IsProbabilityMeasure q]
    (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) :
    palmMeasure (gapSuspensionProcess q hi hm) = q.map reconstructConfiguration := by
  apply Measure.ext
  intro A hA
  change (gapSuspensionMeasure q).bind palmKernel A = _
  rw [Measure.bind_apply hA measurable_palmKernel.aemeasurable]
  have hmeas : Measurable (fun C : LineConfiguration => palmKernel C A) :=
    (Measure.measurable_coe hA).comp measurable_palmKernel
  rw [lintegral_gapSuspensionMeasure q _ hmeas]
  simp_rw [palmKernel_apply_translate_reconstructConfiguration _ _ _ hA]
  have he (y : reconstructibleGapSequences) :
      (∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        ∑' i : ℤ, (Ico (0 : ℝ) 1).indicator (fun _ =>
          A.indicator (fun _ => (1 : ℝ≥0∞))
            (reconstructConfiguration (reindexReconstructibleGaps i y)))
          (gapPosition y.val i - u) ∂volume) =
      ∑' i : ℤ, ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
        (Ico (0 : ℝ) 1).indicator (fun _ =>
          A.indicator (fun _ => (1 : ℝ≥0∞))
            (reconstructConfiguration (reindexReconstructibleGaps i y)))
          (gapPosition y.val i - u) ∂volume :=
    lintegral_tsum fun i =>
      ((measurable_const.indicator measurableSet_Ico).comp
        (measurable_const.sub measurable_id)).aemeasurable
  simp_rw [he]
  let f : ℝ × LineConfiguration → ℝ≥0∞ := fun p =>
    (Ico (0 : ℝ) 1).indicator (fun _ => A.indicator (fun _ => 1) p.2) p.1
  have hf : Measurable f :=
    (((measurable_const.indicator hA).comp measurable_snd).indicator
      (measurable_fst measurableSet_Ico))
  have h := gapSuspension_campbell_indices_internal q hshift f hf
  rw [h]
  change (∫⁻ y, ∫⁻ x, (Ico (0 : ℝ) 1).indicator (fun _ =>
    A.indicator (fun _ => (1 : ℝ≥0∞)) (reconstructConfiguration y)) x ∂volume ∂q) = _
  simp_rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one, mul_one]
  rw [Measure.map_apply measurable_reconstructConfiguration hA]
  exact lintegral_indicator_one (measurable_reconstructConfiguration hA)

/-- Exact interval count between two labelled points, including empty intervals. -/
theorem count_reconstructConfiguration_Ico (y : reconstructibleGapSequences) (a b : ℤ) :
    count (reconstructConfiguration y) (Ico (gapPosition y.val a) (gapPosition y.val b)) =
      ((b - a).toNat : ℝ≥0∞) := by
  have he : (range (gapPosition y.val) ∩ Ico (gapPosition y.val a) (gapPosition y.val b)).encard =
      (Ico a b).encard := by
    symm
    apply Set.encard_congr
    exact Equiv.ofBijective
      (fun i : Ico a b =>
        (⟨gapPosition y.val i.val, ⟨i.val, rfl⟩,
          (gapPosition_strictMono y.val).le_iff_le.mpr i.property.1,
          (gapPosition_strictMono y.val).lt_iff_lt.mpr i.property.2⟩ :
          {x : ℝ // x ∈ range (gapPosition y.val) ∩
            Ico (gapPosition y.val a) (gapPosition y.val b)}))
      ⟨fun i j h => Subtype.ext ((gapPosition_strictMono y.val).injective
        (congrArg Subtype.val h)), by
        rintro ⟨x, ⟨i, rfl⟩, hi⟩
        exact ⟨⟨i, (gapPosition_strictMono y.val).le_iff_le.mp hi.1,
          (gapPosition_strictMono y.val).lt_iff_lt.mp hi.2⟩, rfl⟩⟩
  change ((range (gapPosition y.val) ∩ Ico (gapPosition y.val a) (gapPosition y.val b)).encard :
    ℝ≥0∞) = _
  rw [he, ← Finset.coe_Ico, Set.encard_coe_eq_coe_finsetCard, Int.card_Ico]
  rfl

/-- The right-closed version of the same exact count. -/
theorem count_reconstructConfiguration_Ioc (y : reconstructibleGapSequences) (a b : ℤ) :
    count (reconstructConfiguration y) (Ioc (gapPosition y.val a) (gapPosition y.val b)) =
      ((b - a).toNat : ℝ≥0∞) := by
  have he : (range (gapPosition y.val) ∩ Ioc (gapPosition y.val a) (gapPosition y.val b)).encard =
      (Ioc a b).encard := by
    symm
    apply Set.encard_congr
    exact Equiv.ofBijective
      (fun i : Ioc a b =>
        (⟨gapPosition y.val i.val, ⟨i.val, rfl⟩,
          (gapPosition_strictMono y.val).lt_iff_lt.mpr i.property.1,
          (gapPosition_strictMono y.val).le_iff_le.mpr i.property.2⟩ :
          {x : ℝ // x ∈ range (gapPosition y.val) ∩
            Ioc (gapPosition y.val a) (gapPosition y.val b)}))
      ⟨fun i j h => Subtype.ext ((gapPosition_strictMono y.val).injective
        (congrArg Subtype.val h)), by
        rintro ⟨x, ⟨i, rfl⟩, hi⟩
        exact ⟨⟨i, (gapPosition_strictMono y.val).lt_iff_lt.mp hi.1,
          (gapPosition_strictMono y.val).le_iff_le.mp hi.2⟩, rfl⟩⟩
  change ((range (gapPosition y.val) ∩ Ioc (gapPosition y.val a) (gapPosition y.val b)).encard :
    ℝ≥0∞) = _
  rw [he, ← Finset.coe_Ioc, Set.encard_coe_eq_coe_finsetCard, Int.card_Ioc]
  rfl

/-- See Subsection 6.3 and Corollary 1.1 of the paper: the rooted enumeration recovers
every reconstructed point, including negative labels and the root. -/
theorem rootedPoint_reconstructRootedConfiguration (y : reconstructibleGapSequences) (i : ℤ) :
    rootedPoint (reconstructRootedConfiguration y) i = gapPosition y.val i := by
  have h0 := gapPosition_zero y.val
  have hp (j : ℤ) : count (reconstructConfiguration y) (Ioc 0 (gapPosition y.val j)) =
      (j.toNat : ℝ≥0∞) := by
    simpa only [h0, sub_zero] using count_reconstructConfiguration_Ioc y 0 j
  have hn (j : ℤ) : count (reconstructConfiguration y) (Ico (gapPosition y.val j) 0) =
      ((-j).toNat : ℝ≥0∞) := by
    simpa only [h0, zero_sub] using count_reconstructConfiguration_Ico y j 0
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · simp only [rootedPoint, ne_of_lt hi, ↓reduceIte, not_lt_of_ge hi.le]
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨⟨i, rfl⟩, ?_, ?_⟩
      · simpa only [h0] using (gapPosition_strictMono y.val) hi
      · change ((-i).toNat : ℝ≥0∞) ≤
          count (reconstructConfiguration y) (Ico (gapPosition y.val i) 0)
        rw [hn]
    · rintro x ⟨⟨j, rfl⟩, hj0, hj⟩
      change ((-i).toNat : ℝ≥0∞) ≤ count (reconstructConfiguration y)
        (Ico (gapPosition y.val j) 0) at hj
      rw [hn] at hj
      have hji : (-i).toNat ≤ (-j).toNat := by exact_mod_cast hj
      have hjneg : j < 0 := (gapPosition_strictMono y.val).lt_iff_lt.mp (by simpa [h0] using hj0)
      apply (gapPosition_strictMono y.val).monotone
      omega
  · simp [rootedPoint, gapPosition_zero]
  · simp only [rootedPoint, ne_of_gt hi, ↓reduceIte, hi]
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨⟨i, rfl⟩, ?_, ?_⟩
      · simpa only [h0] using (gapPosition_strictMono y.val) hi
      · change (i.toNat : ℝ≥0∞) ≤
          count (reconstructConfiguration y) (Ioc 0 (gapPosition y.val i))
        rw [hp]
    · rintro x ⟨⟨j, rfl⟩, hj0, hj⟩
      change (i.toNat : ℝ≥0∞) ≤ count (reconstructConfiguration y)
        (Ioc 0 (gapPosition y.val j)) at hj
      rw [hp] at hj
      have hij : i.toNat ≤ j.toNat := by exact_mod_cast hj
      apply (gapPosition_strictMono y.val).monotone
      omega

/-- The Palm gap map is the inverse of reconstruction, at every label. -/
theorem rootedGap_reconstructRootedConfiguration (y : reconstructibleGapSequences) (i : ℤ) :
    rootedGap (reconstructRootedConfiguration y) i = (y.val i : ℝ) := by
  rw [rootedGap, rootedPoint_reconstructRootedConfiguration,
    rootedPoint_reconstructRootedConfiguration, gapPosition_add_one]
  ring

/-- The rooted Palm pullback is precisely the pushforward onto the rooted carrier. -/
theorem gapSuspensionMeasure_rootedPalm_internal (q : Measure reconstructibleGapSequences)
    [IsProbabilityMeasure q]
    (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) :
    rootedPalmMeasure (gapSuspensionProcess q hi hm) = q.map reconstructRootedConfiguration := by
  unfold rootedPalmMeasure
  rw [gapSuspensionMeasure_palm_internal q hshift hi hm]
  have he : q.map reconstructConfiguration =
      (q.map reconstructRootedConfiguration).map (Subtype.val : RootedConfiguration → LineConfiguration) := by
    rw [Measure.map_map measurable_subtype_coe measurable_reconstructRootedConfiguration]
    rfl
  rw [he, (MeasurableEmbedding.subtype_coe measurableSet_rootedConfigurations).comap_map]

/-- The Palm gap sequence law is the original gap law, using the existing gap map and only coercing positive coordinates to real numbers. -/
theorem gapSuspensionMeasure_palm_gaps_internal (q : Measure reconstructibleGapSequences)
    [IsProbabilityMeasure q]
    (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (hi : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) q)
    (hm : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1) :
    (rootedPalmMeasure (gapSuspensionProcess q hi hm)).map rootedGap =
      q.map (fun y : reconstructibleGapSequences => fun i => (y.val i : ℝ)) := by
  rw [gapSuspensionMeasure_rootedPalm_internal q hshift hi hm,
    Measure.map_map (measurable_pi_iff.mpr measurable_rootedGap)
      measurable_reconstructRootedConfiguration]
  congr 1
  funext y i
  exact rootedGap_reconstructRootedConfiguration y i

/-- Finite telescoping bridge to the sums in the proof of Theorem 3.
This uses the positive coordinate carrier used by the gap-limit construction. -/
theorem gapPosition_sub_eq_sum (y : ℤ → Ioi (0 : ℝ)) (a : ℤ) (k : ℕ) :
    gapPosition y (a + (k : ℤ)) - gapPosition y a =
      ∑ j ∈ Finset.range k, (y (a + (j : ℤ)) : ℝ) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, gapPosition_add_one, Finset.sum_range_succ]
    linarith

/-- The forward and backward divergence clauses of the proof of Theorem 3 imply membership in the exact reconstruction domain. -/
theorem mem_reconstructibleGapSequences_of_divergent_sums (y : ℤ → Ioi (0 : ℝ))
    (hp : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (0 + (j : ℤ)) : ℝ)) atTop atTop)
    (hn : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (-(k : ℤ) + (j : ℤ)) : ℝ)) atTop atTop) :
    y ∈ reconstructibleGapSequences := by
  constructor
  · intro r
    obtain ⟨k, hk⟩ := (hp.eventually (eventually_gt_atTop r)).exists
    refine ⟨k, ?_⟩
    have he := gapPosition_sub_eq_sum y 0 k
    simp only [zero_add, gapPosition_zero, sub_zero] at he
    rw [he]
    simpa only [zero_add] using hk
  · intro r
    obtain ⟨k, hk⟩ := (hn.eventually (eventually_gt_atTop (-r))).exists
    refine ⟨-(k : ℤ), ?_⟩
    rw [← gapPosition_sub_eq_sum, neg_add_cancel, gapPosition_zero, zero_sub] at hk
    linarith

/-- Pullback of the gap law to its true reconstruction domain. This is restriction
and a measurable subtype pullback, with no value assigned off the domain. -/
def reconstructionGapMeasure (q : Measure (ℤ → Ioi (0 : ℝ))) : Measure reconstructibleGapSequences :=
  q.comap Subtype.val

/-- Full support of the reconstruction domain makes its inclusion preserve the law. -/
theorem map_reconstructionGapMeasure (q : Measure (ℤ → Ioi (0 : ℝ)))
    (hsupport : ∀ᵐ y ∂q, y ∈ reconstructibleGapSequences) :
    (reconstructionGapMeasure q).map Subtype.val = q := by
  rw [reconstructionGapMeasure,
    map_comap_subtype_coe measurableSet_reconstructibleGapSequences,
    Measure.restrict_eq_self_of_ae_mem hsupport]

/-- The full-mass pullback of a probability gap law is a probability. -/
theorem reconstructionGapMeasure_probability (q : Measure (ℤ → Ioi (0 : ℝ)))
    [IsProbabilityMeasure q] (hsupport : ∀ᵐ y ∂q, y ∈ reconstructibleGapSequences) :
    IsProbabilityMeasure (reconstructionGapMeasure q) := by
  constructor
  have h := congrArg (fun μ : Measure (ℤ → Ioi (0 : ℝ)) => μ univ)
    (map_reconstructionGapMeasure q hsupport)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ, measure_univ] using h

/-- Index invariance transports to the full-mass reconstruction carrier. -/
theorem reconstructionGapMeasure_shift (q : Measure (ℤ → Ioi (0 : ℝ)))
    (hsupport : ∀ᵐ y ∂q, y ∈ reconstructibleGapSequences)
    (a : ℤ) (hshift : q.map (fun y j => y (j + a)) = q) :
    (reconstructionGapMeasure q).map (reindexReconstructibleGaps a) = reconstructionGapMeasure q := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_reconstructibleGapSequences).map_injective
  rw [Measure.map_map measurable_subtype_coe (measurable_reindexReconstructibleGaps a),
    map_reconstructionGapMeasure q hsupport]
  have hc : (Subtype.val ∘ reindexReconstructibleGaps a) =
      (fun y : ℤ → Ioi (0 : ℝ) => fun j => y (j + a)) ∘
        (Subtype.val : reconstructibleGapSequences → (ℤ → Ioi (0 : ℝ))) := rfl
  rw [hc, ← Measure.map_map (measurable_pi_iff.mpr fun j => measurable_pi_apply (j + a))
    measurable_subtype_coe, map_reconstructionGapMeasure q hsupport, hshift]

/-- Integrable coordinate means transport without any choice of an a.e. reconstruction. -/
theorem reconstructionGapMeasure_mean (q : Measure (ℤ → Ioi (0 : ℝ)))
    (hsupport : ∀ᵐ y ∂q, y ∈ reconstructibleGapSequences) (i : ℤ)
    (hi : Integrable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) q)
    (hm : (∫ y : ℤ → Ioi (0 : ℝ), (y i : ℝ) ∂q) = 1) :
    Integrable (fun y : reconstructibleGapSequences => (y.val i : ℝ)) (reconstructionGapMeasure q) ∧
      (∫ y : reconstructibleGapSequences, (y.val i : ℝ) ∂reconstructionGapMeasure q) = 1 := by
  have he := map_reconstructionGapMeasure q hsupport
  have hmeas : Measurable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply i)
  constructor
  · have h := (integrable_map_measure (μ := reconstructionGapMeasure q) hmeas.aestronglyMeasurable
      (measurable_subtype_coe (α := ℤ → Ioi (0 : ℝ))).aemeasurable)
    rw [he] at h
    exact h.mp hi
  · have h := integral_map (μ := reconstructionGapMeasure q)
      (measurable_subtype_coe (α := ℤ → Ioi (0 : ℝ))).aemeasurable hmeas.aestronglyMeasurable
    rw [he, hm] at h
    exact h.symm

/-- Infinite-volume part of the proof of Theorem 3,
as an internal implication from precisely the shift, mean, and divergent-sum
clauses of the proof of Theorem 3. -/
theorem palm_inversion_from_gap_limit_internal
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hshift : ∀ a : ℤ, q.toMeasure.map (fun y j => y (j + a)) = q.toMeasure)
    (hmean : ∀ i : ℤ, Integrable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) q ∧
      (∫ y : ℤ → Ioi (0 : ℝ), (y i : ℝ) ∂q) = 1)
    (hdiv : ∀ᵐ y ∂q.toMeasure,
      Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (0 + (j : ℤ)) : ℝ)) atTop atTop ∧
      Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (-(k : ℤ) + (j : ℤ)) : ℝ)) atTop atTop) :
    ∃ P : PointProcess,
      (P : Measure LineConfiguration) = gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure) ∧
      IsStationary P ∧ HasIntensity P 1 ∧
      palmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructConfiguration ∧
      rootedPalmMeasure P = (reconstructionGapMeasure q.toMeasure).map reconstructRootedConfiguration ∧
      (rootedPalmMeasure P).map rootedGap =
        q.toMeasure.map (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)) := by
  have hs : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences :=
    hdiv.mono fun y hy => mem_reconstructibleGapSequences_of_divergent_sums y hy.1 hy.2
  have := reconstructionGapMeasure_probability q.toMeasure hs
  have hsq (a : ℤ) := reconstructionGapMeasure_shift q.toMeasure hs a (hshift a)
  have hm := reconstructionGapMeasure_mean q.toMeasure hs 0 (hmean 0).1 (hmean 0).2
  let P := gapSuspensionProcess (reconstructionGapMeasure q.toMeasure) hm.1 hm.2
  refine ⟨P, rfl,
    gapSuspensionMeasure_stationary_internal _ (hsq 1) hm.1 hm.2,
    gapSuspensionMeasure_intensity_internal _ hsq hm.1 hm.2,
    gapSuspensionMeasure_palm_internal _ hsq hm.1 hm.2,
    gapSuspensionMeasure_rootedPalm_internal _ hsq hm.1 hm.2, ?_⟩
  rw [gapSuspensionMeasure_palm_gaps_internal _ hsq hm.1 hm.2]
  have hc : (fun y : reconstructibleGapSequences => fun i => (y.val i : ℝ)) =
      (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)) ∘
        (Subtype.val : reconstructibleGapSequences → (ℤ → Ioi (0 : ℝ))) := rfl
  rw [hc]
  have hmeas : Measurable (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)) :=
    measurable_pi_iff.mpr fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  have he := Measure.map_map (μ := reconstructionGapMeasure q.toMeasure)
    hmeas (measurable_subtype_coe (p := (· ∈ reconstructibleGapSequences)))
  rw [map_reconstructionGapMeasure q.toMeasure hs] at he
  exact he.symm

/-- Boundary check for Subsection 6.3: unit gaps reconstruct integer positions. -/
theorem gapPosition_unit (i : ℤ) :
    gapPosition (fun _ : ℤ => (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) i = (i : ℝ) := by
  induction i using Int.induction_on with
  | zero => simpa only [Int.cast_zero] using gapPosition_zero _
  | succ i hi =>
    rw [gapPosition_add_one, hi]
    push_cast
    rfl
  | pred i hi =>
    have h := gapPosition_add_one (fun _ : ℤ => (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) (-(i : ℤ) - 1)
    rw [sub_add_cancel, hi] at h
    push_cast at *
    linarith

/-- The one-particle periodic boundary case belongs to the reconstruction carrier. -/
theorem unit_mem_reconstructibleGapSequences :
    (fun _ : ℤ => (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) ∈ reconstructibleGapSequences := by
  constructor
  · intro r
    obtain ⟨i, hi⟩ := exists_int_gt r
    exact ⟨i, by simpa only [gapPosition_unit] using hi⟩
  · intro r
    obtain ⟨i, hi⟩ := exists_int_lt r
    exact ⟨i, by simpa only [gapPosition_unit] using hi⟩

/-- A finite initial string of gap cells partitions the interval between its endpoints. -/
theorem lintegral_gapPosition_initial_cells (y : reconstructibleGapSequences)
    (f : ℝ → ℝ≥0∞) (k : ℕ) :
    (∫⁻ u in Ico (0 : ℝ) (gapPosition y.val (k : ℤ)), f u ∂volume) =
      ∑ i ∈ Finset.range k, ∫⁻ u in Ico (gapPosition y.val (i : ℤ))
        (gapPosition y.val ((i : ℤ) + 1)), f u ∂volume := by
  induction k with
  | zero => simp [gapPosition_zero]
  | succ k hk =>
    rw [Finset.sum_range_succ, ← hk, Nat.cast_add, Nat.cast_one]
    have h := lintegral_union (μ := volume) (f := f)
      (A := Ico (0 : ℝ) (gapPosition y.val (k : ℤ)))
      (B := Ico (gapPosition y.val (k : ℤ)) (gapPosition y.val ((k : ℤ) + 1)))
      measurableSet_Ico Ico_disjoint_Ico_same
    rw [Ico_union_Ico_eq_Ico (by
      simpa only [gapPosition_zero] using
        (gapPosition_strictMono y.val).monotone (Int.natCast_nonneg k))
      ((gapPosition_strictMono y.val).monotone (by omega))] at h
    exact h

/-- The finite rotation identity: integrating through `k` complete consecutive
gaps gives `k` equal expectations. This is the cyclic-invariance step in
the proof of Theorem 3. -/
theorem gapSuspension_finite_rotation_internal (q : Measure reconstructibleGapSequences)
    [SFinite q] (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (f : LineConfiguration → ℝ≥0∞) (hf : Measurable f) (k : ℕ) :
    (∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (gapPosition y.val (k : ℤ)),
      f (translateConfiguration u (reconstructConfiguration y)) ∂volume ∂q) =
      (k : ℝ≥0∞) * ∫⁻ C, f C ∂gapSuspensionMeasure q := by
  let H (y : reconstructibleGapSequences) :=
    ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
      f (translateConfiguration u (reconstructConfiguration y)) ∂volume
  have hm : Measurable H := measurable_suspension_gap_interval f hf
  have hc (y : reconstructibleGapSequences) (i : ℤ) :
      (∫⁻ u in Ico (gapPosition y.val i) (gapPosition y.val (i + 1)),
        f (translateConfiguration u (reconstructConfiguration y)) ∂volume) =
      H (reindexReconstructibleGaps i y) := by
    dsimp only [H]
    rw [reconstructConfiguration_reindex]
    simp_rw [translateConfiguration_add]
    change _ = ∫⁻ u in Ico (0 : ℝ) (y.val (0 + i) : ℝ),
      f (translateConfiguration (u + gapPosition y.val i) (reconstructConfiguration y)) ∂volume
    rw [zero_add]
    have he := suspension_lintegral_Ico_add
      (fun u => f (translateConfiguration u (reconstructConfiguration y)))
      0 (y.val i : ℝ) (gapPosition y.val i)
    simpa only [zero_add, gapPosition_add_one, add_comm (y.val i : ℝ)] using he.symm
  simp_rw [lintegral_gapPosition_initial_cells, hc]
  have hms (i : ℕ) : Measurable (fun y => H (reindexReconstructibleGaps (i : ℤ) y)) :=
    hm.comp (measurable_reindexReconstructibleGaps (i : ℤ))
  rw [lintegral_finsetSum _ (fun (i : ℕ) _ => hms i)]
  have he (i : ℤ) : (∫⁻ y, H (reindexReconstructibleGaps i y) ∂q) = ∫⁻ y, H y ∂q := by
    have h := lintegral_map (μ := q) hm (measurable_reindexReconstructibleGaps i)
    rw [hshift] at h
    exact h.symm
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    lintegral_gapSuspensionMeasure q f hf]

/-- Uniform translation over a positive microscopic period, applied to the rooted law.
The period is positive on the whole carrier, so the scalar normalization has no junk value. -/
def uniformPeriodRotationMeasure (q : Measure reconstructibleGapSequences) (N : ℕ+) :
    Measure LineConfiguration :=
  (N : ℝ≥0∞)⁻¹ • (q.prod (volume.restrict (Ico (0 : ℝ) (N : ℝ)))).map gapSuspensionConfiguration

/-- Uniform rotation over one period agrees with suspension whenever the sum of
that period is its microscopic length. This assertion concerns the full periodic
spatial process, prior to the strict quarter-circle restriction. -/
theorem uniformPeriodRotationMeasure_eq_suspension_internal
    (q : Measure reconstructibleGapSequences) [SFinite q]
    (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (N : ℕ+) (hperiod : ∀ᵐ y ∂q, gapPosition y.val (N : ℕ) = (N : ℝ)) :
    uniformPeriodRotationMeasure q N = gapSuspensionMeasure q := by
  apply Measure.ext
  intro A hA
  let f : LineConfiguration → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have h := gapSuspension_finite_rotation_internal q hshift f hf (N : ℕ)
  have he : (∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (gapPosition y.val (N : ℕ)),
      f (translateConfiguration u (reconstructConfiguration y)) ∂volume ∂q) =
      ∫⁻ y, ∫⁻ u in Ico (0 : ℝ) (N : ℝ),
        f (translateConfiguration u (reconstructConfiguration y)) ∂volume ∂q := by
    apply lintegral_congr_ae
    filter_upwards [hperiod] with y hy
    rw [hy]
  rw [he] at h
  have hn : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt N.pos)
  have hn' : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    _ = (N : ℝ≥0∞)⁻¹ * ∫⁻ p, f (gapSuspensionConfiguration p)
        ∂q.prod (volume.restrict (Ico (0 : ℝ) (N : ℝ))) := by
      rw [uniformPeriodRotationMeasure, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply measurable_gapSuspensionConfiguration hA]
      congr 1
      exact (lintegral_indicator_one (measurable_gapSuspensionConfiguration hA)).symm
    _ = (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * ∫⁻ C, f C ∂gapSuspensionMeasure q) := by
      congr 1
      change (∫⁻ p, (f ∘ gapSuspensionConfiguration) p
        ∂q.prod (volume.restrict (Ico (0 : ℝ) (N : ℝ)))) = _
      rw [lintegral_prod _ (hf.comp measurable_gapSuspensionConfiguration).aemeasurable]
      exact h
    _ = _ := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hn hn', one_mul]
      exact lintegral_indicator_one hA

/-- The reconstruction of finite microscopic gaps has precisely the library's
cyclic lifts relative to the distinguished particle. -/
theorem gapPosition_finite_configuration {N : ℕ+} (X : Riesz1.Configuration N) (i : ℤ) :
    gapPosition (fun j => (⟨gap X j, Riesz1.gap_pos X j⟩ : Ioi (0 : ℝ))) i =
      (N : ℝ) * (Riesz1.cyclicLift X i - Riesz1.cyclicLift X 0) := by
  induction i using Int.induction_on with
  | zero => simp [gapPosition_zero]
  | succ i hi =>
    rw [gapPosition_add_one, hi]
    change (N : ℝ) * (Riesz1.cyclicLift X (i : ℤ) - Riesz1.cyclicLift X 0) +
      (N : ℝ) * (Riesz1.cyclicLift X ((i : ℤ) + 1) - Riesz1.cyclicLift X (i : ℤ)) = _
    ring
  | pred i hi =>
    have h := gapPosition_add_one
      (fun j => (⟨gap X j, Riesz1.gap_pos X j⟩ : Ioi (0 : ℝ))) (-(i : ℤ) - 1)
    rw [sub_add_cancel, hi] at h
    change (N : ℝ) * (Riesz1.cyclicLift X (-(i : ℤ)) - Riesz1.cyclicLift X 0) =
      gapPosition _ (-(i : ℤ) - 1) +
        (N : ℝ) * (Riesz1.cyclicLift X (-(i : ℤ) - 1 + 1) -
          Riesz1.cyclicLift X (-(i : ℤ) - 1)) at h
    rw [sub_add_cancel] at h
    linarith

/-- Every positive-volume cyclic gap sequence belongs to the reconstruction carrier,
including `N = 1`. No extra values are assigned to inadmissible sequences. -/
theorem finite_configuration_mem_reconstructibleGapSequences {N : ℕ+}
    (X : Riesz1.Configuration N) :
    (fun j => (⟨gap X j, Riesz1.gap_pos X j⟩ : Ioi (0 : ℝ))) ∈ reconstructibleGapSequences := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have he (m : ℤ) :
      gapPosition (fun j => (⟨gap X j, Riesz1.gap_pos X j⟩ : Ioi (0 : ℝ))) ((N : ℤ) * m) =
        (N : ℝ) * (m : ℝ) := by
    rw [gapPosition_finite_configuration]
    have h1 := Riesz1.cyclicLift_add_mul X N.pos m
    have h0 := Riesz1.cyclicLift_add_mul X N.pos 0
    simp only [Nat.cast_zero, zero_add, Int.cast_zero, mul_zero, add_zero] at h1 h0
    rw [h1, h0]
    ring
  constructor
  · intro r
    obtain ⟨m, hm⟩ := exists_int_gt (r / (N : ℝ))
    refine ⟨(N : ℤ) * m, ?_⟩
    rw [he]
    exact (div_lt_iff₀ hN).mp hm |>.trans_le (le_of_eq (mul_comm _ _))
  · intro r
    obtain ⟨m, hm⟩ := exists_int_lt (r / (N : ℝ))
    refine ⟨(N : ℤ) * m, ?_⟩
    rw [he, mul_comm]
    exact (lt_div_iff₀ hN).mp hm

/-- The existing finite periodic gap sequence lifted to its full-mass
reconstruction domain. Its coordinates remain the `gap X j`. -/
def configurationReconstructionGaps {N : ℕ+} (X : Riesz1.Configuration N) :
    reconstructibleGapSequences :=
  ⟨fun j => ⟨gap X j, Riesz1.gap_pos X j⟩,
    finite_configuration_mem_reconstructibleGapSequences X⟩

/-- The domain lift of the finite gap map is measurable. -/
theorem measurable_configurationReconstructionGaps (N : ℕ+) :
    Measurable (@configurationReconstructionGaps N) :=
  (show Measurable (fun X : Riesz1.Configuration N => fun j =>
    (⟨gap X j, Riesz1.gap_pos X j⟩ : Ioi (0 : ℝ))) from
      measurable_pi_iff.mpr fun j => (Riesz1.measurable_gap j).subtype_mk).subtype_mk

/-- The finite period has exactly its microscopic length, the normalization
needed by the finite rotation identity. -/
theorem gapPosition_configurationReconstructionGaps_period {N : ℕ+}
    (X : Riesz1.Configuration N) :
    gapPosition (configurationReconstructionGaps X).val (N : ℕ) = (N : ℝ) := by
  change gapPosition (fun j => (⟨gap X j, Riesz1.gap_pos X j⟩ : Ioi (0 : ℝ))) (N : ℕ) = _
  rw [gapPosition_finite_configuration]
  have h := Riesz1.cyclicLift_add_N X 0
  simp only [zero_add] at h
  rw [h]
  ring

/-- The finite periodically extended spatial configuration in the proof of Theorem 3, retaining every periodic image. The `microscopicConfiguration` instead keeps only the strict quarter-circle window. -/
def periodicSpatialConfiguration {N : ℕ+} (X : Riesz1.Configuration N) : LineConfiguration :=
  translateConfiguration (-(N : ℝ) * Riesz1.cyclicLift X 0)
    (reconstructConfiguration (configurationReconstructionGaps X))

/-- The periodic spatial object is exactly the microscopic rescaling of all
library cyclic lifts, without a cutoff or an arbitrary completion. -/
theorem periodicSpatialConfiguration_atoms {N : ℕ+} (X : Riesz1.Configuration N) :
    (periodicSpatialConfiguration X).val =
      range (fun i : ℤ => (N : ℝ) * Riesz1.cyclicLift X i) := by
  ext x
  change (∃ i : ℤ, gapPosition (configurationReconstructionGaps X).val i =
    x + -(N : ℝ) * Riesz1.cyclicLift X 0) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    dsimp only [configurationReconstructionGaps] at hi
    rw [gapPosition_finite_configuration] at hi
    linarith
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    dsimp only [configurationReconstructionGaps]
    rw [gapPosition_finite_configuration, ← hi]
    ring

/-- Measurability of the periodic spatial configuration in the sigma-algebra. -/
theorem measurable_periodicSpatialConfiguration (N : ℕ+) :
    Measurable (@periodicSpatialConfiguration N) :=
  measurable_translateConfiguration.comp
    ((measurable_const.mul (Riesz1.measurable_cyclicLift 0)).prodMk
      (measurable_reconstructConfiguration.comp (measurable_configurationReconstructionGaps N)))

/-- The actual finite periodic spatial law, as a pushforward of the Gibbs
law, in both exponent regimes. See the proof of Theorem 3 in the paper. -/
def periodicSpatialLaw (p : Parameters) (N : ℕ+) : Measure LineConfiguration :=
  (gibbsMeasure p N).map periodicSpatialConfiguration

/-- The periodic spatial law is a probability for every volume, including one. -/
theorem periodicSpatialLaw_probability (p : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (periodicSpatialLaw p N) := by
  have := gibbsMeasure_probability p N
  unfold periodicSpatialLaw
  infer_instance

end Riesz2
