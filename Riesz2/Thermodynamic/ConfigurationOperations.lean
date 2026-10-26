/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Sanity.PalmMeasurability
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Configuration operations

Measurability for the bounded-count sigma-algebra, including partial order statistics,
translation and Campbell rooting.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2

local instance : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- Evaluation of the counting measure, Subsection 1.5. -/
theorem configurationMeasure_apply (C : LineConfiguration) (B : Set ℝ)
    (hB : MeasurableSet B) : configurationMeasure C B = count C B :=
  FrozenSanity.configurationMeasure_apply C B hB

/-- Local finiteness also applies to bounded sets that are not Borel. -/
theorem count_lt_top_of_bounded (C : LineConfiguration) (B : Set ℝ)
    (hB : Bornology.IsBounded B) : count C B < ⊤ :=
  FrozenSanity.count_lt_top_of_bounded C B hB

/-- Counts increase with the set being counted. -/
theorem count_mono (C : LineConfiguration) {B D : Set ℝ} (h : B ⊆ D) :
    count C B ≤ count C D := by
  unfold count
  exact_mod_cast Set.encard_mono (inter_subset_inter_right C.val h)

/-- Bounded Borel counts are the defining measurable evaluations. -/
theorem measurable_count_bounded (B : Set ℝ) (hB : MeasurableSet B)
    (hb : Bornology.IsBounded B) : Measurable (fun C : LineConfiguration => count C B) :=
  FrozenSanity.measurable_count B hB hb

/-- See Subsection 1.5 of the paper: every Borel count is measurable, including
the possible infinite value on unbounded sets. -/
theorem measurable_count (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun C : LineConfiguration => count C B) := by
  have he (C : LineConfiguration) : count C B =
      ⨆ n : ℕ, count C (B ∩ Metric.closedBall 0 (n : ℝ)) := by
    simp_rw [← configurationMeasure_apply _ _
      (hB.inter measurableSet_closedBall)]
    rw [← configurationMeasure_apply _ _ hB]
    have hm : Monotone (fun n : ℕ => B ∩ Metric.closedBall 0 (n : ℝ)) := by
      intro n m hnm
      exact inter_subset_inter_right _ (Metric.closedBall_subset_closedBall (by exact_mod_cast hnm))
    rw [← hm.measure_iUnion, ← inter_iUnion, Metric.iUnion_closedBall_nat, inter_univ]
  simpa only [he] using Measurable.iSup (fun n : ℕ =>
    measurable_count_bounded _ (hB.inter measurableSet_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right))

/-- A map to configurations is measurable if its bounded Borel counts are measurable. -/
theorem measurable_configuration_of_counts {α : Type*} [MeasurableSpace α]
    (f : α → LineConfiguration)
    (hf : ∀ B : Set ℝ, MeasurableSet B → Bornology.IsBounded B →
      Measurable (fun a => count (f a) B)) : Measurable f := by
  apply Measurable.of_le_map
  change (⨆ (B : Set ℝ) (_ : MeasurableSet B) (_ : Bornology.IsBounded B),
    MeasurableSpace.comap (fun C : LineConfiguration => count C B) inferInstance) ≤ _
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun hb => ?_
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  rw [MeasurableSpace.map_comp]
  exact (hf B hB hb).le_map

/-- Counting after restriction amounts to intersecting the test set. -/
theorem count_restrictConfiguration (W B : Set ℝ) (C : LineConfiguration) :
    count (restrictConfiguration W C) B = count C (B ∩ W) := by
  unfold count restrictConfiguration
  congr 2
  ext x
  simp only [mem_inter_iff]
  tauto

/-- See Subsection 1.5 of the paper: restriction to any Borel window is measurable. -/
theorem measurable_restrictConfiguration (W : Set ℝ) (hW : MeasurableSet W) :
    Measurable (restrictConfiguration W) := by
  apply measurable_configuration_of_counts
  intro B hB hb
  simp_rw [count_restrictConfiguration]
  exact measurable_count_bounded _ (hB.inter hW) (hb.subset inter_subset_left)

/-- Nested restrictions compose as intersection of their windows. -/
theorem restrictConfiguration_restrictConfiguration (W V : Set ℝ) (C : LineConfiguration) :
    restrictConfiguration W (restrictConfiguration V C) = restrictConfiguration (W ∩ V) C := by
  apply Subtype.ext
  ext x
  simp only [restrictConfiguration, mem_inter_iff]
  tauto

/-- See Subsection 1.5 of the paper: translation is jointly measurable. -/
theorem measurable_translateConfiguration :
    Measurable (fun p : ℝ × LineConfiguration => translateConfiguration p.1 p.2) :=
  FrozenSanity.measurable_translateConfiguration

/-- Translation by a fixed displacement is measurable. -/
theorem measurable_translateConfiguration_const (t : ℝ) :
    Measurable (translateConfiguration t) :=
  measurable_translateConfiguration.comp (measurable_const.prodMk measurable_id)

/-- See Theorem 3 of the paper: the finite Campbell rooting operation is measurable. -/
theorem measurable_palmKernel : Measurable palmKernel :=
  FrozenSanity.measurable_palmKernel

/-- The finite count used for interval fluctuations is measurable. -/
theorem measurable_intervalCount (a b : ℝ) : Measurable (intervalCount a b) :=
  (measurable_count _ measurableSet_Ioc).ennreal_toReal

private theorem finite_configuration_inter (C : LineConfiguration) (B : Set ℝ)
    (hB : Bornology.IsBounded B) : (C.val ∩ B).Finite := by
  obtain ⟨r, hr⟩ := hB.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr
  exact (C.property (-r) r).subset (inter_subset_inter_right _ hr)

private theorem exists_count_threshold_max (C : LineConfiguration) (B : Set ℝ)
    (hB : Bornology.IsBounded B) (k : ℝ≥0∞) (hk : 0 < k) (h : k ≤ count C B) :
    ∃ x ∈ C.val ∩ B, k ≤ count C (B ∩ Iic x) := by
  have hn : (C.val ∩ B).Nonempty := by
    by_contra hn
    have hz : count C B = 0 := by simp [count, not_nonempty_iff_eq_empty.mp hn]
    rw [hz] at h
    exact (not_le_of_gt hk) h
  have hm := hn.isGreatest_csSup (finite_configuration_inter C B hB)
  refine ⟨sSup (C.val ∩ B), hm.1, ?_⟩
  apply h.trans
  unfold count
  have hs : C.val ∩ B ⊆ C.val ∩ (B ∩ Iic (sSup (C.val ∩ B))) :=
    fun _ hx => ⟨hx.1, hx.2, hm.2 hx⟩
  exact_mod_cast Set.encard_mono hs

private theorem sInf_count_threshold_le_iff (C : LineConfiguration) (B : Set ℝ)
    (hB : Bornology.IsBounded B) (k : ℝ≥0∞) (hk : 0 < k) (h : k ≤ count C B)
    (r : ℝ) :
    sInf {x : ℝ | x ∈ C.val ∩ B ∧ k ≤ count C (B ∩ Iic x)} ≤ r ↔
      k ≤ count C (B ∩ Iic r) := by
  let S := {x : ℝ | x ∈ C.val ∩ B ∧ k ≤ count C (B ∩ Iic x)}
  have hf : S.Finite := (finite_configuration_inter C B hB).subset (fun _ hx => hx.1)
  have hn : S.Nonempty := exists_count_threshold_max C B hB k hk h
  have hm := hn.isLeast_csInf hf
  constructor
  · intro hr
    exact hm.1.2.trans (count_mono C (inter_subset_inter_right B (Iic_subset_Iic.mpr hr)))
  · intro hr
    obtain ⟨x, hx, hxc⟩ := exists_count_threshold_max C (B ∩ Iic r)
      (hB.subset inter_subset_left) k hk hr
    have he : (B ∩ Iic r) ∩ Iic x = B ∩ Iic x := by
      ext y
      simp only [mem_inter_iff, mem_Iic]
      exact ⟨fun hy => ⟨hy.1.1, hy.2⟩, fun hy => ⟨⟨hy.1, hy.2.trans hx.2.2⟩, hy.2⟩⟩
    rw [he] at hxc
    exact (hm.2 ⟨⟨hx.1, hx.2.1⟩, hxc⟩).trans hx.2.2

/-- See Subsection 1.5 of the paper: comparison of a partial order statistic
with a real threshold is exactly a finite count comparison. -/
theorem orderedPoint_le_iff (a b : ℝ) (leftClosed : Bool) (j : ℕ+)
    (C : OrderedPointDomain a b leftClosed j) (r : ℝ) :
    orderedPoint a b leftClosed j C ≤ r ↔
      (j : ℝ≥0∞) ≤ count C.val ((if leftClosed then Ico a b else Ioc a b) ∩ Iic r) := by
  apply sInf_count_threshold_le_iff
  · cases leftClosed
    · exact Metric.isBounded_Ioc a b
    · exact Metric.isBounded_Ico a b
  · exact_mod_cast j.pos
  · exact C.property

/-- The domain of every partial order statistic is measurable. -/
theorem measurableSet_orderedPointDomain (a b : ℝ) (leftClosed : Bool) (j : ℕ+) :
    MeasurableSet {C : LineConfiguration |
      (j : ℝ≥0∞) ≤ count C (if leftClosed then Ico a b else Ioc a b)} := by
  apply measurableSet_le measurable_const (measurable_count _ ?_)
  cases leftClosed <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact measurableSet_Ioc
  · exact measurableSet_Ico

/-- See Subsection 1.5 of the paper: the ordered point is measurable on its
partial domain. There is no position assigned to missing points. -/
theorem measurable_orderedPoint (a b : ℝ) (leftClosed : Bool) (j : ℕ+) :
    Measurable (orderedPoint a b leftClosed j) := by
  apply measurable_of_Iic
  intro r
  have hI : MeasurableSet (if leftClosed then Ico a b else Ioc a b) := by
    cases leftClosed <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact measurableSet_Ioc
    · exact measurableSet_Ico
  have he : (orderedPoint a b leftClosed j ⁻¹' Iic r) =
      {C : OrderedPointDomain a b leftClosed j |
        (j : ℝ≥0∞) ≤ count C.val ((if leftClosed then Ico a b else Ioc a b) ∩ Iic r)} := by
    ext C
    exact orderedPoint_le_iff a b leftClosed j C r
  rw [he]
  exact measurableSet_le measurable_const
    ((measurable_count _ (hI.inter measurableSet_Iic)).comp measurable_subtype_coe)

/-- See Subsection 1.5 of the paper, with all parts in a single statement. -/
theorem configuration_operations_measurable (R : ℝ) (_hR : 0 < R) (B : Set ℝ)
    (hB : MeasurableSet B) (a b : ℝ) (leftClosed : Bool) (j : ℕ+) :
    Measurable (restrictConfiguration (Icc (-R) R)) ∧
      Measurable (fun p : ℝ × LineConfiguration => translateConfiguration p.1 p.2) ∧
      Measurable (fun C : LineConfiguration => count C B) ∧
      Measurable (orderedPoint a b leftClosed j) :=
  ⟨measurable_restrictConfiguration _ measurableSet_Icc,
    measurable_translateConfiguration, measurable_count B hB,
    measurable_orderedPoint a b leftClosed j⟩

/-- The bi-infinite rooted carrier is a measurable subset of configuration space.
See Corollary 1.1 of the paper. Unboundedness can be tested on integer half-lines. -/
theorem measurableSet_rootedConfigurations : MeasurableSet rootedConfigurations := by
  have he : rootedConfigurations =
      {C : LineConfiguration | 0 < count C {0}} ∩
        ((⋂ n : ℕ, {C : LineConfiguration | 0 < count C (Ioi (n : ℝ))}) ∩
          ⋂ n : ℕ, {C : LineConfiguration | 0 < count C (Iio (-(n : ℝ)))}) := by
    have hp (C : LineConfiguration) (B : Set ℝ) :
        0 < count C B ↔ (C.val ∩ B).Nonempty := by
      unfold count
      norm_cast
      exact Set.encard_pos
    ext C
    simp only [rootedConfigurations, mem_ofPred_eq, mem_inter_iff, mem_iInter, hp]
    constructor
    · rintro ⟨h0, hpos, hneg⟩
      refine ⟨⟨0, h0, rfl⟩, ?_, ?_⟩
      · intro n
        obtain ⟨x, hx, hn⟩ := hpos n
        exact ⟨x, hx, hn⟩
      · intro n
        obtain ⟨x, hx, hn⟩ := hneg (-n)
        exact ⟨x, hx, hn⟩
    · rintro ⟨⟨x, hx, hx0⟩, hpos, hneg⟩
      refine ⟨hx0 ▸ hx, ?_, ?_⟩
      · intro r
        obtain ⟨n, hn⟩ := exists_nat_gt r
        obtain ⟨x, hx, hnx⟩ := hpos n
        exact ⟨x, hx, hn.trans hnx⟩
      · intro r
        obtain ⟨n, hn⟩ := exists_nat_gt (-r)
        obtain ⟨x, hx, hnx⟩ := hneg n
        exact ⟨x, hx, lt_of_lt_of_le hnx (by linarith)⟩
  rw [he]
  exact (measurableSet_lt measurable_const (measurable_count _ (measurableSet_singleton 0))).inter
    ((MeasurableSet.iInter fun n : ℕ =>
      measurableSet_lt measurable_const (measurable_count _ measurableSet_Ioi)).inter
        (MeasurableSet.iInter fun n : ℕ =>
          measurableSet_lt measurable_const (measurable_count _ measurableSet_Iio)))

private theorem exists_isLeast_of_locallyFinite (C : LineConfiguration) (S : Set ℝ)
    (hS : S ⊆ C.val) (a : ℝ) (ha : ∀ x ∈ S, a ≤ x) (hn : S.Nonempty) :
    ∃ x, IsLeast S x := by
  obtain ⟨b, hb⟩ := hn
  have hf : (S ∩ Icc a b).Finite := (C.property a b).subset
    (fun _ hx => ⟨hS hx.1, hx.2⟩)
  have hn' : (S ∩ Icc a b).Nonempty := ⟨b, hb, ha b hb, le_rfl⟩
  have hm := hn'.isLeast_csInf hf
  refine ⟨_, hm.1.1, ?_⟩
  intro y hy
  by_cases hyb : y ≤ b
  · exact hm.2 ⟨hy, ha y hy, hyb⟩
  · exact hm.1.2.2.trans (le_of_not_ge hyb)

private theorem exists_isGreatest_of_locallyFinite (C : LineConfiguration) (S : Set ℝ)
    (hS : S ⊆ C.val) (b : ℝ) (hb : ∀ x ∈ S, x ≤ b) (hn : S.Nonempty) :
    ∃ x, IsGreatest S x := by
  obtain ⟨a, ha⟩ := hn
  have hf : (S ∩ Icc a b).Finite := (C.property a b).subset
    (fun _ hx => ⟨hS hx.1, hx.2⟩)
  have hn' : (S ∩ Icc a b).Nonempty := ⟨a, ha, le_rfl, hb a ha⟩
  have hm := hn'.isGreatest_csSup hf
  refine ⟨_, hm.1.1, ?_⟩
  intro y hy
  by_cases hay : a ≤ y
  · exact hm.2 ⟨hy, hay, hb y hy⟩
  · exact (le_of_not_ge hay).trans hm.1.2.1

private theorem exists_right_count_threshold (C : RootedConfiguration) (k : ℕ)
    (hk : 0 < k) :
    ∃ x : ℝ, x ∈ C.val.val ∧ 0 < x ∧ (k : ℝ≥0∞) ≤ count C.val (Ioc 0 x) := by
  have hinf : (C.val.val ∩ Ioi 0).Infinite := by
    intro hf
    obtain ⟨b, hb⟩ := hf.bddAbove
    obtain ⟨x, hx, hxb⟩ := C.property.2.1 (max 0 b)
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right 0 b) hxb))
      (hb ⟨hx, lt_of_le_of_lt (le_max_left 0 b) hxb⟩)
  obtain ⟨t, ht, htk⟩ := hinf.exists_subset_card_eq k
  have hn : (t : Set ℝ).Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (fun he => by simp [he] at htk; omega)
  have hm := hn.isGreatest_csSup t.finite_toSet
  refine ⟨sSup (t : Set ℝ), (ht hm.1).1, (ht hm.1).2, ?_⟩
  have hs : (t : Set ℝ) ⊆ C.val.val ∩ Ioc 0 (sSup (t : Set ℝ)) :=
    fun x hx => ⟨(ht hx).1, (ht hx).2, hm.2 hx⟩
  have hc := Set.encard_mono hs
  rw [Set.encard_coe_eq_coe_finsetCard, htk] at hc
  unfold count
  exact_mod_cast hc

private theorem exists_left_count_threshold (C : RootedConfiguration) (k : ℕ)
    (hk : 0 < k) :
    ∃ x : ℝ, x ∈ C.val.val ∧ x < 0 ∧ (k : ℝ≥0∞) ≤ count C.val (Ico x 0) := by
  have hinf : (C.val.val ∩ Iio 0).Infinite := by
    intro hf
    obtain ⟨a, ha⟩ := hf.bddBelow
    obtain ⟨x, hx, hxa⟩ := C.property.2.2 (min 0 a)
    exact (not_le_of_gt (lt_of_lt_of_le hxa (min_le_right 0 a)))
      (ha ⟨hx, lt_of_lt_of_le hxa (min_le_left 0 a)⟩)
  obtain ⟨t, ht, htk⟩ := hinf.exists_subset_card_eq k
  have hn : (t : Set ℝ).Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (fun he => by simp [he] at htk; omega)
  have hm := hn.isLeast_csInf t.finite_toSet
  refine ⟨sInf (t : Set ℝ), (ht hm.1).1, (ht hm.1).2, ?_⟩
  have hs : (t : Set ℝ) ⊆ C.val.val ∩ Ico (sInf (t : Set ℝ)) 0 :=
    fun x hx => ⟨(ht hx).1, hm.2 hx, (ht hx).2⟩
  have hc := Set.encard_mono hs
  rw [Set.encard_coe_eq_coe_finsetCard, htk] at hc
  unfold count
  exact_mod_cast hc

/-- See Corollary 1.1 of the paper: positive Palm labels are characterized by right counts. -/
theorem rootedPoint_le_iff_of_pos (C : RootedConfiguration) (i : ℤ) (hi : 0 < i) (r : ℝ) :
    rootedPoint C i ≤ r ↔ (i.toNat : ℝ≥0∞) ≤ count C.val (Ioc 0 r) := by
  have hk : 0 < i.toNat := by omega
  let S := {x : ℝ | x ∈ C.val.val ∧ 0 < x ∧
    (i.toNat : ℝ≥0∞) ≤ count C.val (Ioc 0 x)}
  have hn : S.Nonempty := exists_right_count_threshold C i.toNat hk
  obtain ⟨x, hm⟩ := exists_isLeast_of_locallyFinite C.val S
    (fun _ hx => hx.1) 0 (fun _ hx => hx.2.1.le) hn
  have he : rootedPoint C i = x := by
    simp only [rootedPoint, ne_of_gt hi, ↓reduceIte, hi]
    exact hm.csInf_eq
  rw [he]
  constructor
  · intro hxr
    exact hm.1.2.2.trans (count_mono C.val (Ioc_subset_Ioc_right hxr))
  · intro hr
    obtain ⟨y, hy, hyc⟩ := exists_count_threshold_max C.val (Ioc 0 r)
      (Metric.isBounded_Ioc 0 r) (i.toNat : ℝ≥0∞) (by exact_mod_cast hk) hr
    have hc : (i.toNat : ℝ≥0∞) ≤ count C.val (Ioc 0 y) :=
      hyc.trans (count_mono C.val (fun _ hz => ⟨hz.1.1, hz.2⟩))
    exact (hm.2 ⟨hy.1, hy.2.1, hc⟩).trans hy.2.2

/-- See Corollary 1.1 of the paper: negative Palm labels are characterized by left counts. -/
theorem le_rootedPoint_iff_of_neg (C : RootedConfiguration) (i : ℤ) (hi : i < 0) (r : ℝ) :
    r ≤ rootedPoint C i ↔ ((-i).toNat : ℝ≥0∞) ≤ count C.val (Ico r 0) := by
  have hk : 0 < (-i).toNat := by omega
  let S := {x : ℝ | x ∈ C.val.val ∧ x < 0 ∧
    ((-i).toNat : ℝ≥0∞) ≤ count C.val (Ico x 0)}
  have hn : S.Nonempty := exists_left_count_threshold C (-i).toNat hk
  obtain ⟨x, hm⟩ := exists_isGreatest_of_locallyFinite C.val S
    (fun _ hx => hx.1) 0 (fun _ hx => hx.2.1.le) hn
  have he : rootedPoint C i = x := by
    simp only [rootedPoint, ne_of_lt hi, ↓reduceIte, not_lt_of_ge hi.le]
    exact hm.csSup_eq
  rw [he]
  constructor
  · intro hrx
    exact hm.1.2.2.trans (count_mono C.val (Ico_subset_Ico_left hrx))
  · intro hr
    have hnB : (C.val.val ∩ Ico r 0).Nonempty := by
      by_contra hnB
      have hz : count C.val (Ico r 0) = 0 := by
        simp [count, not_nonempty_iff_eq_empty.mp hnB]
      rw [hz] at hr
      exact (not_le_of_gt (show (0 : ℝ≥0∞) < (-i).toNat by exact_mod_cast hk)) hr
    have hf := finite_configuration_inter C.val (Ico r 0) (Metric.isBounded_Ico r 0)
    have hmB := hnB.isLeast_csInf hf
    have hc : ((-i).toNat : ℝ≥0∞) ≤ count C.val (Ico (sInf (C.val.val ∩ Ico r 0)) 0) := by
      apply hr.trans
      unfold count
      have hs : C.val.val ∩ Ico r 0 ⊆
          C.val.val ∩ Ico (sInf (C.val.val ∩ Ico r 0)) 0 :=
        fun y hy => ⟨hy.1, hmB.2 hy, hy.2.2⟩
      exact_mod_cast Set.encard_mono hs
    exact hmB.1.2.1.trans (hm.2 ⟨hmB.1.1, hmB.1.2.2, hc⟩)

/-- The two-sided point enumeration is measurable at every label.
See Corollary 1.1 of the paper, used by the rooted operations of Subsection 1.5. -/
theorem measurable_rootedPoint (i : ℤ) : Measurable (fun C : RootedConfiguration => rootedPoint C i) := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · apply measurable_of_Ici
    intro r
    have he : (fun C : RootedConfiguration => rootedPoint C i) ⁻¹' Ici r =
        {C : RootedConfiguration | ((-i).toNat : ℝ≥0∞) ≤ count C.val (Ico r 0)} := by
      ext C
      exact le_rootedPoint_iff_of_neg C i hi r
    rw [he]
    exact measurableSet_le measurable_const
      ((measurable_count _ measurableSet_Ico).comp measurable_subtype_coe)
  · simpa only [rootedPoint, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : RootedConfiguration => (0 : ℝ)))
  · apply measurable_of_Iic
    intro r
    have he : (fun C : RootedConfiguration => rootedPoint C i) ⁻¹' Iic r =
        {C : RootedConfiguration | (i.toNat : ℝ≥0∞) ≤ count C.val (Ioc 0 r)} := by
      ext C
      exact rootedPoint_le_iff_of_pos C i hi r
    rw [he]
    exact measurableSet_le measurable_const
      ((measurable_count _ measurableSet_Ioc).comp measurable_subtype_coe)

/-- Every labelled Palm gap is measurable, Corollary 1.1. -/
theorem measurable_rootedGap (i : ℤ) : Measurable (fun C : RootedConfiguration => rootedGap C i) :=
  (measurable_rootedPoint (i + 1)).sub (measurable_rootedPoint i)

/-- Every finite block of labelled Palm gaps is measurable, Corollary 1.1. -/
theorem measurable_rootedGapBlock (k : ℕ+) : Measurable (rootedGapBlock k) := by
  apply Measurable.of_eval
  intro i
  exact measurable_rootedGap i

end Riesz2
