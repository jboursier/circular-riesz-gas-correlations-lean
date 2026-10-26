/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CountMoments

/-!
# Count and span inversion at the first positive particle

Deterministic interfaces for the proof of Corollary 1.1. They use the existing
reconstruction and count, include empty windows, and retain the strict upper endpoint
convention in the offset strip.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local instance countSpanInversionConfigurationMeasurableSpace : MeasurableSpace LineConfiguration :=
  configurationMeasurableSpace

/-- The existing gap span is the difference of its reconstructed endpoints. -/
theorem gapSequenceSpan_eq_gapPosition_sub (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) (k : ℕ) :
    gapSequenceSpan y i k = gapPosition y (i + k) - gapPosition y i :=
  (gapPosition_sub_eq_sum y i k).symm

/-- Splitting a span retains the integer labels used by periodic and Palm gaps. -/
theorem gapSequenceSpan_add (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) (k m : ℕ) :
    gapSequenceSpan y i (k + m) = gapSequenceSpan y i k +
      gapSequenceSpan y (i + k) m := by
  simp only [gapSequenceSpan_eq_gapPosition_sub, Nat.cast_add]
  rw [add_assoc]
  ring

/-- Positive gaps give nonnegative spans, including the empty span. -/
theorem gapSequenceSpan_nonneg (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) (k : ℕ) :
    0 ≤ gapSequenceSpan y i k :=
  Finset.sum_nonneg fun _ _ => (y _).property.le

/-- See Subsection 6.4 of the paper: the first positive particle is the right endpoint
of the distinguished gap, for every offset in the half-open strip. -/
theorem first_positive_particle_in_strip (y : reconstructibleGapSequences) (u : ℝ)
    (hu : 0 ≤ u) (huy : u < (y.val 0 : ℝ)) :
    0 < gapPosition y.val 1 - u ∧
      gapPosition y.val 1 - u ≤ (y.val 0 : ℝ) ∧
      ∀ i : ℤ, 0 < gapPosition y.val i - u ↔ 1 ≤ i := by
  have h1 : gapPosition y.val 1 = (y.val 0 : ℝ) := by
    simpa only [gapPosition_zero, zero_add] using gapPosition_add_one y.val 0
  refine ⟨by linarith, by linarith, fun i => ?_⟩
  constructor
  · intro hi
    by_contra h
    have hz := (gapPosition_strictMono y.val).monotone (show i ≤ 0 by omega)
    rw [gapPosition_zero] at hz
    linarith
  · intro hi
    have hz := (gapPosition_strictMono y.val).monotone hi
    linarith

/-- See the proof of Corollary 1.1 in the paper: the spatial count is
exactly the unique index bracketing the right endpoint. The zero-count case
is included. No natural-number rounding of a real count is used. -/
theorem intervalCount_eq_iff_gapPosition_brackets
    (y : reconstructibleGapSequences) (u R : ℝ) (hu : 0 ≤ u)
    (huy : u < (y.val 0 : ℝ)) (hR : 0 ≤ R) (m : ℕ) :
    intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = (m : ℝ) ↔
      gapPosition y.val (m : ℤ) - u ≤ R ∧
        R < gapPosition y.val ((m : ℤ) + 1) - u := by
  have hcount (k : ℕ)
      (hlo : gapPosition y.val (k : ℤ) - u ≤ R)
      (hhi : R < gapPosition y.val ((k : ℤ) + 1) - u) :
      intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = k := by
    have he : (reconstructConfiguration y).val ∩ Ioc u (R + u) =
        (reconstructConfiguration y).val ∩
          Ioc (gapPosition y.val 0) (gapPosition y.val (k : ℤ)) := by
      ext x
      constructor
      · rintro ⟨⟨i, rfl⟩, hi⟩
        refine ⟨⟨i, rfl⟩, ?_, ?_⟩
        · rw [gapPosition_zero]
          linarith [hi.1]
        · apply (gapPosition_strictMono y.val).monotone
          have hn : i < (k : ℤ) + 1 := by
            apply (gapPosition_strictMono y.val).lt_iff_lt.mp
            linarith [hi.2]
          omega
      · rintro ⟨⟨i, rfl⟩, hi⟩
        refine ⟨⟨i, rfl⟩, ?_, ?_⟩
        · have hip : 1 ≤ i := by
            have := (gapPosition_strictMono y.val).lt_iff_lt.mp hi.1
            omega
          have hp := ((first_positive_particle_in_strip y u hu huy).2.2 i).mpr hip
          linarith
        · linarith [hi.2]
    have hc : count (translateConfiguration u (reconstructConfiguration y)) (Ioc 0 R) =
        (k : ℝ≥0∞) := by
      rw [count_translateConfiguration_Ioc, zero_add]
      unfold count
      rw [he]
      simpa only [count, sub_zero, Int.toNat_natCast] using count_reconstructConfiguration_Ioc y 0 (k : ℤ)
    simp only [intervalCount, hc, ENNReal.toReal_natCast]
  constructor
  · intro hm
    obtain ⟨j, hj⟩ := y.property.1 (R + u)
    have hj0 : 0 ≤ j := by
      by_contra h
      have hz := (gapPosition_strictMono y.val).monotone (show j ≤ 0 by omega)
      rw [gapPosition_zero] at hz
      linarith
    let n := j.toNat
    have hn : R + u < gapPosition y.val (n : ℤ) := by
      simpa only [n, Int.toNat_of_nonneg hj0] using hj
    have hex : ∃ k : ℕ, R < gapPosition y.val ((k : ℤ) + 1) - u := by
      refine ⟨n, ?_⟩
      have hz := (gapPosition_strictMono y.val) (show (n : ℤ) < (n : ℤ) + 1 by omega)
      linarith
    let k := Nat.find hex
    have hhi : R < gapPosition y.val ((k : ℤ) + 1) - u := Nat.find_spec hex
    have hlo : gapPosition y.val (k : ℤ) - u ≤ R := by
      by_cases hk : k = 0
      · simp only [hk, Nat.cast_zero, gapPosition_zero, zero_sub]
        linarith
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hprev := Nat.find_min hex (show k - 1 < Nat.find hex by omega)
        have hid : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by omega
        rw [hid] at hprev
        exact le_of_not_gt hprev
    have heq : k = m := by exact_mod_cast (hcount k hlo hhi).symm.trans hm
    simpa only [heq] using And.intro hlo hhi
  · rintro ⟨hlo, hhi⟩
    exact hcount m hlo hhi

/-- The count always has a bracketing index. This includes a radius of zero. -/
theorem exists_intervalCount_bracketing_index
    (y : reconstructibleGapSequences) (u R : ℝ) (hu : 0 ≤ u)
    (huy : u < (y.val 0 : ℝ)) (hR : 0 ≤ R) :
    ∃ m : ℕ,
      intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = (m : ℝ) ∧
      gapPosition y.val (m : ℤ) - u ≤ R ∧
        R < gapPosition y.val ((m : ℤ) + 1) - u := by
  obtain ⟨m, hm⟩ := (show ∃ m : ℕ, count (translateConfiguration u
      (reconstructConfiguration y)) (Ioc 0 R) = (m : ℝ≥0∞) from by
    have hf := (((translateConfiguration u (reconstructConfiguration y)).property 0 R).subset
      (inter_subset_inter_right _ Ioc_subset_Icc_self)).encard_eq_coe_toFinset_card
    exact ⟨_, by simpa [count] using congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) hf⟩)
  have heq : intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = m := by
    simp only [intervalCount, hm, ENNReal.toReal_natCast]
  exact ⟨m, heq, (intervalCount_eq_iff_gapPosition_brackets y u R hu huy hR m).mp heq⟩

/-- See the proof of Corollary 1.1 in the paper: the endpoint immediately
after the counted points differs from the radius by at most its adjacent gap.
The selected span starts at label one, as in the paper. -/
theorem selected_span_at_count_endpoint
    (y : reconstructibleGapSequences) (u R : ℝ) (hu : 0 ≤ u)
    (huy : u < (y.val 0 : ℝ)) (hR : 0 ≤ R) (m : ℕ)
    (hm : intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = m) :
    |gapSequenceSpan y.val 1 m - R| ≤ (y.val 0 : ℝ) + (y.val (m : ℤ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ := (intervalCount_eq_iff_gapPosition_brackets y u R hu huy hR m).mp hm
  have ha := first_positive_particle_in_strip y u hu huy
  rw [gapSequenceSpan_eq_gapPosition_sub]
  rw [show (1 : ℤ) + (m : ℤ) = (m : ℤ) + 1 by omega, gapPosition_add_one] at *
  exact abs_le.mpr ⟨by linarith, by linarith [(y.val (m : ℤ)).property]⟩

/-- See the proof of Corollary 1.1 in the paper, deterministic error
assembly. The local block estimate is an internal good-event input. -/
theorem count_span_inversion_error_internal
    (y : reconstructibleGapSequences) (u R : ℝ) (hu : 0 ≤ u)
    (huy : u < (y.val 0 : ℝ)) (hR : 0 ≤ R) (K m : ℕ) (B D : ℝ)
    (hm : intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = m)
    (hleft : (y.val 0 : ℝ) ≤ D) (hright : (y.val (m : ℤ) : ℝ) ≤ D)
    (hblock : |gapSequenceSpan y.val 1 K - gapSequenceSpan y.val 1 m -
      ((K : ℝ) - m)| ≤ B) :
    |gapSequenceSpan y.val 1 K - R + ((m : ℝ) - K)| ≤ 2 * D + B := by
  have hend := selected_span_at_count_endpoint y u R hu huy hR m hm
  calc
    _ = |(gapSequenceSpan y.val 1 m - R) +
        (gapSequenceSpan y.val 1 K - gapSequenceSpan y.val 1 m - ((K : ℝ) - m))| := by
      congr 1; ring
    _ ≤ |gapSequenceSpan y.val 1 m - R| +
        |gapSequenceSpan y.val 1 K - gapSequenceSpan y.val 1 m - ((K : ℝ) - m)| := abs_add_le _ _
    _ ≤ 2 * D + B := by linarith

/-- Local centered blocks control the difference of two spans with a common
starting label, in either order of their lengths. -/
theorem common_start_span_difference_internal
    (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) (K m : ℕ) (B : ℝ)
    (hblock : |gapSequenceSpan y (i + (min K m : ℕ)) (max K m - min K m) -
      ((max K m - min K m : ℕ) : ℝ)| ≤ B) :
    |gapSequenceSpan y i K - gapSequenceSpan y i m - ((K : ℝ) - m)| ≤ B := by
  rcases le_total K m with h | h
  · rw [min_eq_left h, max_eq_right h] at hblock
    have hs := gapSequenceSpan_add y i K (m - K)
    rw [Nat.add_sub_of_le h] at hs
    have hc : ((m - K : ℕ) : ℝ) = (m : ℝ) - K := Nat.cast_sub h
    rw [hc] at hblock
    have he : gapSequenceSpan y i K - gapSequenceSpan y i m - ((K : ℝ) - m) =
        -(gapSequenceSpan y (i + (K : ℤ)) (m - K) - ((m : ℝ) - K)) := by linarith
    simpa only [he, abs_neg] using hblock
  · rw [min_eq_right h, max_eq_left h] at hblock
    have hs := gapSequenceSpan_add y i m (K - m)
    rw [Nat.add_sub_of_le h] at hs
    have hc : ((K - m : ℕ) : ℝ) = (K : ℝ) - m := Nat.cast_sub h
    rw [hc] at hblock
    convert hblock using 1; congr 1; linarith

/-- See the proof of Corollary 1.1 in the paper: two deterministic span
bounds bracket the count uniformly over the entire offset strip. -/
theorem count_bracketed_by_two_spans_internal
    (y : reconstructibleGapSequences) (u R D : ℝ) (hu : 0 ≤ u)
    (huy : u < (y.val 0 : ℝ)) (hR : 0 ≤ R) (l r m : ℕ)
    (hm : intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) = m)
    (hD : (y.val 0 : ℝ) ≤ D)
    (hl : gapSequenceSpan y.val 1 l + D ≤ R)
    (hr : R < gapSequenceSpan y.val 1 r) : l ≤ m ∧ m ≤ r := by
  obtain ⟨hlo, hhi⟩ := (intervalCount_eq_iff_gapPosition_brackets y u R hu huy hR m).mp hm
  have ha := first_positive_particle_in_strip y u hu huy
  have hlow : gapPosition y.val ((l : ℤ) + 1) - u ≤ R := by
    rw [gapSequenceSpan_eq_gapPosition_sub] at hl
    rw [show (1 : ℤ) + (l : ℤ) = (l : ℤ) + 1 by omega] at hl
    linarith
  have hhigh : R < gapPosition y.val ((r : ℤ) + 1) - u := by
    rw [gapSequenceSpan_eq_gapPosition_sub] at hr
    rw [show (1 : ℤ) + (r : ℤ) = (r : ℤ) + 1 by omega] at hr
    linarith
  constructor
  · have hpos : (l : ℤ) + 1 < (m : ℤ) + 1 :=
      (gapPosition_strictMono y.val).lt_iff_lt.mp (by linarith)
    omega
  · have hpos : (m : ℤ) < (r : ℤ) + 1 :=
      (gapPosition_strictMono y.val).lt_iff_lt.mp (by linarith)
    omega

/-- See the proof of Corollary 1.1 in the paper: simultaneous control
of local blocks gives count inversion at every allowed offset. All good-event
inputs refer only to gaps and fixed labels, making this ready for a union bound. -/
theorem count_span_inversion_on_good_gaps_internal
    (y : reconstructibleGapSequences) (R B D : ℝ) (hR : 0 ≤ R)
    (K l r : ℕ) (hlK : l ≤ K) (hKr : K ≤ r)
    (hgaps : ∀ i : ℕ, i ≤ r → (y.val (i : ℤ) : ℝ) ≤ D)
    (hl : gapSequenceSpan y.val 1 l + D ≤ R)
    (hr : R < gapSequenceSpan y.val 1 r)
    (hblocks : ∀ (i h : ℕ), i ≤ r → h ≤ r - l →
      |gapSequenceSpan y.val (1 + (i : ℤ)) h - h| ≤ B)
    (u : ℝ) (hu : 0 ≤ u) (huy : u < (y.val 0 : ℝ)) :
    |gapSequenceSpan y.val 1 K - R +
      (intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) - K)| ≤
        2 * D + B := by
  obtain ⟨m, hm, _⟩ := exists_intervalCount_bracketing_index y u R hu huy hR
  obtain ⟨hlm, hmr⟩ := count_bracketed_by_two_spans_internal y u R D hu huy hR
    l r m hm (hgaps 0 (Nat.zero_le r)) hl hr
  rw [hm]
  apply count_span_inversion_error_internal y u R hu huy hR K m B D hm
    (hgaps 0 (Nat.zero_le r)) (hgaps m hmr)
  apply common_start_span_difference_internal
  exact hblocks (min K m) (max K m - min K m) (by omega) (by omega)

/-- Boundary check for count inversion: unit gaps and an integer radius give
the exact count, for every offset in `[0,1)`. -/
theorem intervalCount_unit_gap_integer_radius (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (K : ℕ) :
    intervalCount 0 K (translateConfiguration u
      (reconstructConfiguration ⟨fun _ => ⟨1, zero_lt_one⟩,
        unit_mem_reconstructibleGapSequences⟩)) = K := by
  apply (intervalCount_eq_iff_gapPosition_brackets _ u K hu hu1 (Nat.cast_nonneg _) K).mpr
  simp only [gapPosition_unit, Int.cast_natCast, Int.cast_add, Int.cast_one]
  constructor <;> linarith

/-- The simultaneous gap and centered-block event for count inversion.
Its meaning is literal for every threshold and all endpoint indices. -/
def countInversionGoodGaps (R B D : ℝ) (l r : ℕ) : Set (ℤ → Ioi (0 : ℝ)) :=
  {y | (∀ i : ℕ, i ≤ r → (y (i : ℤ) : ℝ) ≤ D) ∧
    gapSequenceSpan y 1 l + D ≤ R ∧ R < gapSequenceSpan y 1 r ∧
    ∀ i h : ℕ, i ≤ r → h ≤ r - l → |gapSequenceSpan y (1 + (i : ℤ)) h - h| ≤ B}

/-- The count-inversion good event is Borel in the existing gap topology. -/
theorem measurableSet_countInversionGoodGaps (R B D : ℝ) (l r : ℕ) :
    MeasurableSet (countInversionGoodGaps R B D l r) := by
  have hg (i : ℕ) : MeasurableSet {y : ℤ → Ioi (0 : ℝ) | i ≤ r → (y (i : ℤ) : ℝ) ≤ D} := by
    by_cases hi : i ≤ r
    · simpa only [hi, true_implies, Function.comp_def] using
        measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply (i : ℤ))) measurable_const
    · simp only [hi, false_implies, ofPred_true, MeasurableSet.univ]
  have hb (i h : ℕ) : MeasurableSet {y : ℤ → Ioi (0 : ℝ) | i ≤ r → h ≤ r - l →
      |gapSequenceSpan y (1 + (i : ℤ)) h - h| ≤ B} := by
    by_cases hi : i ≤ r <;> by_cases hh : h ≤ r - l
    · simpa only [hi, hh, true_implies] using measurableSet_le
        (((continuous_gapSequenceSpan (1 + (i : ℤ)) h).measurable.sub_const _).abs) measurable_const
    all_goals simp only [hi, hh, false_implies, implies_true, ofPred_true, MeasurableSet.univ]
  have hgs : MeasurableSet {y : ℤ → Ioi (0 : ℝ) | ∀ i : ℕ, i ≤ r → (y (i : ℤ) : ℝ) ≤ D} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter hg
  have hbs : MeasurableSet {y : ℤ → Ioi (0 : ℝ) | ∀ i h : ℕ, i ≤ r → h ≤ r - l →
      |gapSequenceSpan y (1 + (i : ℤ)) h - h| ≤ B} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter (fun i => MeasurableSet.iInter (hb i))
  exact hgs.inter ((measurableSet_le ((continuous_gapSequenceSpan 1 l).measurable.add_const D)
    measurable_const).inter ((measurableSet_lt measurable_const
      (continuous_gapSequenceSpan 1 r).measurable).inter hbs))

/-- See the proof of Corollary 1.1 in the paper: the exact finite union
bound for the simultaneous event, before inserting rigidity and one-gap tails. -/
theorem countInversionGoodGaps_compl_measure_le
    (μ : Measure (ℤ → Ioi (0 : ℝ))) (R B D : ℝ) (l r : ℕ) :
    μ (countInversionGoodGaps R B D l r)ᶜ ≤
      (∑ i ∈ Finset.range (r + 1), μ {y | D < (y (i : ℤ) : ℝ)}) +
      μ {y | R < gapSequenceSpan y 1 l + D} + μ {y | gapSequenceSpan y 1 r ≤ R} +
      ∑ i ∈ Finset.range (r + 1), ∑ h ∈ Finset.range (r - l + 1),
        μ {y | B < |gapSequenceSpan y (1 + (i : ℤ)) h - h|} := by
  classical
  let G := ⋃ i ∈ Finset.range (r + 1), {y : ℤ → Ioi (0 : ℝ) | D < (y (i : ℤ) : ℝ)}
  let L := {y : ℤ → Ioi (0 : ℝ) | R < gapSequenceSpan y 1 l + D}
  let U := {y : ℤ → Ioi (0 : ℝ) | gapSequenceSpan y 1 r ≤ R}
  let T := ⋃ i ∈ Finset.range (r + 1), ⋃ h ∈ Finset.range (r - l + 1),
    {y : ℤ → Ioi (0 : ℝ) | B < |gapSequenceSpan y (1 + (i : ℤ)) h - h|}
  have hsub : (countInversionGoodGaps R B D l r)ᶜ ⊆ ((G ∪ L) ∪ U) ∪ T := by
    intro y hy
    by_contra hn
    simp only [mem_union, not_or] at hn
    apply hy
    refine ⟨fun i hi => ?_, le_of_not_gt hn.1.1.2, lt_of_not_ge hn.1.2, fun i h hi hh => ?_⟩
    · apply le_of_not_gt
      intro h
      exact hn.1.1.1 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), h⟩⟩)
    · apply le_of_not_gt
      intro hb
      exact hn.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
        mem_iUnion.mpr ⟨h, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩⟩⟩⟩)
  have hg : μ G ≤ ∑ i ∈ Finset.range (r + 1), μ {y | D < (y (i : ℤ) : ℝ)} :=
    measure_biUnion_finset_le _ _
  have ht : μ T ≤ ∑ i ∈ Finset.range (r + 1), ∑ h ∈ Finset.range (r - l + 1),
      μ {y | B < |gapSequenceSpan y (1 + (i : ℤ)) h - h|} := by
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _
  calc
    _ ≤ μ (((G ∪ L) ∪ U) ∪ T) := measure_mono hsub
    _ ≤ (μ G + μ L + μ U) + μ T :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hg le_rfl) le_rfl) ht

/-- See the proof of Corollary 1.1 in the paper: the error event in the
actual suspension strip is contained in a gap-dependent bad event. It is
therefore independent of the offset for the ensuing length-bias estimate. -/
theorem count_inversion_failure_subset_good_compl_internal
    (R B D : ℝ) (hR : 0 ≤ R) (K l r : ℕ) (hlK : l ≤ K) (hKr : K ≤ r) :
    gapSuspensionStrip ∩ {z : reconstructibleGapSequences × ℝ |
      2 * D + B < |gapSequenceSpan z.1.val 1 K - R +
        (intervalCount 0 R (gapSuspensionConfiguration z) - K)|} ⊆
      Prod.fst ⁻¹' {y : reconstructibleGapSequences | y.val ∉ countInversionGoodGaps R B D l r} := by
  rintro ⟨y, u⟩ ⟨hu, herr⟩ hgood
  exact not_lt_of_ge (count_span_inversion_on_good_gaps_internal y R B D hR K l r hlK hKr
    hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2 u hu.1 hu.2) herr

/-- The selected count inversion error has at most the mass of the explicit
gap bad event, with respect to the original suspension sampling measure. -/
theorem count_inversion_failure_measure_le_internal
    (q : Measure reconstructibleGapSequences) (R B D : ℝ) (hR : 0 ≤ R)
    (K l r : ℕ) (hlK : l ≤ K) (hKr : K ≤ r) :
    ((q.prod volume).restrict gapSuspensionStrip)
      {z : reconstructibleGapSequences × ℝ |
        2 * D + B < |gapSequenceSpan z.1.val 1 K - R +
          (intervalCount 0 R (gapSuspensionConfiguration z) - K)|} ≤
      ((q.prod volume).restrict gapSuspensionStrip)
        (Prod.fst ⁻¹' {y : reconstructibleGapSequences | y.val ∉ countInversionGoodGaps R B D l r}) := by
  have hE : MeasurableSet {z : reconstructibleGapSequences × ℝ |
      2 * D + B < |gapSequenceSpan z.1.val 1 K - R +
        (intervalCount 0 R (gapSuspensionConfiguration z) - K)|} := by
    apply measurableSet_lt measurable_const
    exact (((((continuous_gapSequenceSpan 1 K).measurable.comp
      (measurable_subtype_coe.comp measurable_fst)).sub_const R).add
      (((measurable_intervalCount 0 R).comp measurable_gapSuspensionConfiguration).sub_const _)).abs)
  have hbad : MeasurableSet (Prod.fst ⁻¹'
      {y : reconstructibleGapSequences | y.val ∉ countInversionGoodGaps R B D l r}) :=
    ((measurableSet_countInversionGoodGaps R B D l r).compl.preimage measurable_subtype_coe).preimage
      (measurable_fst : Measurable (Prod.fst : reconstructibleGapSequences × ℝ → reconstructibleGapSequences))
  rw [Measure.restrict_apply hE, Measure.restrict_apply hbad]
  apply measure_mono
  intro z hz
  exact ⟨count_inversion_failure_subset_good_compl_internal R B D hR K l r hlK hKr
    ⟨hz.2, hz.1⟩, hz.2⟩

/-- Enlarging an interval of positive gaps increases its span. -/
theorem gapSequenceSpan_mono_length (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) :
    Monotone (gapSequenceSpan y i) := by
  intro k m hkm
  have hs := gapSequenceSpan_add y i k (m - k)
  rw [Nat.add_sub_of_le hkm] at hs
  linarith [gapSequenceSpan_nonneg y (i + k) (m - k)]

/-- See the proof of Corollary 1.1 in the paper: very short blocks need
no rigidity event. Positivity extends them to a controlled block of length
`h₀`, giving the uniform bound `2 h₀` used in the proof. -/
theorem short_block_centered_bound_internal
    (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) (h h₀ : ℕ) (hh : h ≤ h₀)
    (hspan : gapSequenceSpan y i h₀ ≤ 2 * h₀) :
    |gapSequenceSpan y i h - h| ≤ 2 * h₀ := by
  have hs := gapSequenceSpan_mono_length y i hh
  have hnat : (h : ℝ) ≤ h₀ := by exact_mod_cast hh
  exact abs_le.mpr ⟨by linarith [gapSequenceSpan_nonneg y i h], by linarith⟩

/-- See the proof of Corollary 1.1 in the paper: control at lengths at
least `h₀` supplies all smaller centered blocks too. In particular the union
bound may start at a growing `h₀`, rather than including one-gap rigidity
at its fixed threshold. -/
theorem all_block_bounds_from_long_blocks_internal
    (y : ℤ → Ioi (0 : ℝ)) (r H h₀ : ℕ) (hh₀ : 1 ≤ h₀) (hh₀H : h₀ ≤ H)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hblocks : ∀ i h : ℕ, i ≤ r → h₀ ≤ h → h ≤ H →
      |gapSequenceSpan y (1 + (i : ℤ)) h - h| ≤ (h : ℝ) ^ α) :
    ∀ i h : ℕ, i ≤ r → h ≤ H →
      |gapSequenceSpan y (1 + (i : ℤ)) h - h| ≤
        2 * h₀ + (H : ℝ) ^ α := by
  intro i h hi hh
  by_cases hsmall : h ≤ h₀
  · have hbase := hblocks i h₀ hi le_rfl hh₀H
    have hone : (1 : ℝ) ≤ h₀ := by exact_mod_cast hh₀
    have hp : (h₀ : ℝ) ^ α ≤ h₀ := by
      calc
        _ ≤ (h₀ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone hα1
        _ = _ := Real.rpow_one _
    have hspan : gapSequenceSpan y (1 + (i : ℤ)) h₀ ≤ 2 * h₀ := by
      linarith [(abs_le.mp hbase).2]
    exact (short_block_centered_bound_internal y _ h h₀ hsmall hspan).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hb := hblocks i h hi (by omega) hh
    have hle : (h : ℝ) ^ α ≤ (H : ℝ) ^ α :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hh) hα
    exact (hb.trans hle).trans (le_add_of_nonneg_left (by positivity))

/-- Boundary check for the good-event definition: for unit gaps the block
conditions reduce to the nonnegative error threshold, and the endpoint
conditions retain their exact strict/non-strict inequalities. -/
theorem countInversionGoodGaps_unit (R B D : ℝ) (l r : ℕ) :
    (fun _ : ℤ => (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) ∈ countInversionGoodGaps R B D l r ↔
      1 ≤ D ∧ (l : ℝ) + D ≤ R ∧ R < (r : ℝ) ∧ 0 ≤ B := by
  simp only [countInversionGoodGaps, mem_ofPred_eq, gapSequenceSpan, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, sub_self, abs_zero]
  constructor
  · rintro ⟨hg, hl, hr, hb⟩
    exact ⟨hg 0 (Nat.zero_le r), hl, hr, hb 0 0 (Nat.zero_le r) (Nat.zero_le _)⟩
  · rintro ⟨hD, hl, hr, hB⟩
    exact ⟨fun _ _ => hD, hl, hr, fun _ _ _ _ => hB⟩

/-- See the proof of Corollary 1.1 in the paper: simultaneous rigidity
for every label in a finite window and every length at least `h₀`.
Constants precede the window and both length cutoffs. The explicit number
of tests is retained so later scale choices can absorb it exponentially. -/
theorem periodicGapLaw_simultaneous_block_rigidity (p : Parameters) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ min p.val.2 1 / 2 + η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ r H h₀ : ℕ,
          1 ≤ h₀ → H ≤ (N : ℕ) / 2 →
          (periodicGapLaw p N).toMeasure
            (⋃ i ∈ Finset.range (r + 1), ⋃ h ∈ Finset.Icc h₀ H,
              {y | (h : ℝ) ^ (min p.val.2 1 / 2 + η) <
                |gapSequenceSpan y (1 + (i : ℤ)) h - h|}) ≤
            ENNReal.ofReal (((r + 1 : ℕ) : ℝ) * (Finset.Icc h₀ H).card * C *
              Real.exp (-c * (h₀ : ℝ) ^ (η / (4 * (p.val.2 + 2))))) := by
  obtain ⟨η₀, hη₀, hsmall, hrig⟩ := periodicGapLaw_finite_rigidity p
  refine ⟨η₀, hη₀, hsmall, fun η hη hηsmall => ?_⟩
  obtain ⟨C, c, hC, hc, hb⟩ := hrig η hη hηsmall
  refine ⟨C, c, hC, hc, fun N hN r H h₀ hh₀ hHN => ?_⟩
  let Q := C * Real.exp (-c * (h₀ : ℝ) ^ (η / (4 * (p.val.2 + 2))))
  have hδ : 0 ≤ η / (4 * (p.val.2 + 2)) := div_nonneg hη.le (by linarith [p.property.2.1])
  have htest (i h : ℕ) (hh : h ∈ Finset.Icc h₀ H) :
      (periodicGapLaw p N).toMeasure
        {y | (h : ℝ) ^ (min p.val.2 1 / 2 + η) <
          |gapSequenceSpan y (1 + (i : ℤ)) h - h|} ≤ ENNReal.ofReal Q := by
    have hh' := Finset.mem_Icc.mp hh
    apply (hb N hN h (by omega) (by omega) (1 + (i : ℤ))).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hp : (h₀ : ℝ) ^ (η / (4 * (p.val.2 + 2))) ≤
        (h : ℝ) ^ (η / (4 * (p.val.2 + 2))) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hh'.1) hδ
    exact mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr hc.le)
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), ∑ h ∈ Finset.Icc h₀ H,
        (periodicGapLaw p N).toMeasure
          {y | (h : ℝ) ^ (min p.val.2 1 / 2 + η) <
            |gapSequenceSpan y (1 + (i : ℤ)) h - h|} :=
      (measure_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _i ∈ Finset.range (r + 1), ∑ _h ∈ Finset.Icc h₀ H, ENNReal.ofReal Q :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun h hh => htest i h hh
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp only [Q]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast]
      ring

/-- See the proof of Corollary 1.1 in the paper: the finite one-gap
upper tail in the same periodic gap carrier as the simultaneous span event. -/
theorem periodicGapLaw_upper_gap_tail (p : Parameters) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ i : ℤ,
      ∀ D : ℝ, 1 ≤ D →
        (periodicGapLaw p N).toMeasure {y | D < (y i : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-c * D)) := by
  obtain ⟨C, c, hC, hc, ht, _⟩ := SingleGapTails.single_gap_tails p.val.2 p.val.1 p.val.1
    p.property.2.1 p.property.2.2 p.property.1 le_rfl
  refine ⟨C, c, hC, hc, fun N hN i D hD => ?_⟩
  have hE : MeasurableSet {y : ℤ → Ioi (0 : ℝ) | D < (y i : ℝ)} :=
    measurableSet_lt measurable_const (measurable_subtype_coe.comp (measurable_pi_apply i))
  rw [periodicGapLaw_toMeasure, Measure.map_apply (measurable_periodicGapSequence N) hE]
  apply (measure_mono (fun X hX => ?_)).trans ((ht p rfl le_rfl le_rfl N hN i).2 D hD)
  change D < gap X i at hX
  exact hX.le

/-- See the proof of Corollary 1.1 in the paper: it suffices to union
bound rigidity failures of lengths at least `h₀`. All shorter centered spans
are supplied by positivity and extension to `h₀`. -/
theorem countInversionGoodGaps_compl_subset_long_failures_internal
    (R D α : ℝ) (l r h₀ : ℕ) (hh₀ : 1 ≤ h₀) (hh₀H : h₀ ≤ r - l)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (countInversionGoodGaps R (2 * h₀ + ((r - l : ℕ) : ℝ) ^ α) D l r)ᶜ ⊆
      (((⋃ i ∈ Finset.range (r + 1), {y : ℤ → Ioi (0 : ℝ) | D < (y (i : ℤ) : ℝ)}) ∪
        {y | R < gapSequenceSpan y 1 l + D}) ∪ {y | gapSequenceSpan y 1 r ≤ R}) ∪
      (⋃ i ∈ Finset.range (r + 1), ⋃ h ∈ Finset.Icc h₀ (r - l),
        {y | (h : ℝ) ^ α < |gapSequenceSpan y (1 + (i : ℤ)) h - h|}) := by
  classical
  intro y hy
  by_contra hn
  simp only [mem_union, not_or] at hn
  have hg (i : ℕ) (hi : i ≤ r) : (y (i : ℤ) : ℝ) ≤ D := by
    apply le_of_not_gt
    intro h
    exact hn.1.1.1 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), h⟩⟩)
  have hb (i h : ℕ) (hi : i ≤ r) (hh : h₀ ≤ h) (hhH : h ≤ r - l) :
      |gapSequenceSpan y (1 + (i : ℤ)) h - h| ≤ (h : ℝ) ^ α := by
    apply le_of_not_gt
    intro hbad
    exact hn.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
      mem_iUnion.mpr ⟨h, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hh, hhH⟩, hbad⟩⟩⟩⟩)
  exact hy ⟨hg, le_of_not_gt hn.1.1.2, lt_of_not_ge hn.1.2,
    all_block_bounds_from_long_blocks_internal y r (r - l) h₀ hh₀ hh₀H α hα hα1 hb⟩

end Riesz2
