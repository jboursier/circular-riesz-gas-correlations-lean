/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.LocalConverges
public import Riesz2.Sanity.PalmMeasurability

/-!
# Uniqueness of local total-variation limits

The sigma-algebras of the increasing bounded windows generate the configuration
sigma-algebra. Equality of window laws therefore determines a law. The event supremum is
used directly with its normalization.
-/

public section

noncomputable section

open MeasureTheory Set Filter MeasurableSpace
open scoped ENNReal Topology

namespace Riesz2

/-- The event total variation is symmetric, Theorem 3. -/
theorem totalVariation_symm {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : totalVariation μ ν = totalVariation ν μ := by
  unfold totalVariation
  congr 1
  funext A
  exact add_comm _ _

/-- The event supremum controls either one-sided difference of event masses. -/
theorem measure_sub_le_totalVariation {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set α) (hA : MeasurableSet A) : μ A - ν A ≤ totalVariation μ ν :=
  (le_add_right le_rfl).trans (le_iSup (fun A : {A : Set α // MeasurableSet A} =>
    (μ A.val - ν A.val) + (ν A.val - μ A.val)) ⟨A, hA⟩)

/-- The triangle inequality for the event-supremum normalization. -/
theorem totalVariation_triangle {α : Type*} [MeasurableSpace α]
    (μ ν ξ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    totalVariation μ ξ ≤ totalVariation μ ν + totalVariation ν ξ := by
  apply iSup_le
  intro A
  calc
    (μ A.val - ξ A.val) + (ξ A.val - μ A.val) ≤
        ((μ A.val - ν A.val) + (ν A.val - ξ A.val)) +
          ((ξ A.val - ν A.val) + (ν A.val - μ A.val)) :=
      add_le_add tsub_le_tsub_add_tsub tsub_le_tsub_add_tsub
    _ = ((μ A.val - ν A.val) + (ν A.val - μ A.val)) +
        ((ν A.val - ξ A.val) + (ξ A.val - ν A.val)) := by ac_rfl
    _ ≤ totalVariation μ ν + totalVariation ν ξ :=
      add_le_add (le_iSup (fun A : {A : Set α // MeasurableSet A} =>
        (μ A.val - ν A.val) + (ν A.val - μ A.val)) A)
        (le_iSup (fun A : {A : Set α // MeasurableSet A} =>
          (ν A.val - ξ A.val) + (ξ A.val - ν A.val)) A)

/-- Zero event total variation identifies finite measures, Theorem 3. -/
theorem totalVariation_eq_zero_iff {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    totalVariation μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply Measure.ext
    intro A hA
    apply le_antisymm
    · apply tsub_eq_zero_iff_le.mp
      exact le_antisymm (h ▸ measure_sub_le_totalVariation μ ν A hA) bot_le
    · apply tsub_eq_zero_iff_le.mp
      have hs : totalVariation ν μ = 0 := (totalVariation_symm ν μ).trans h
      exact le_antisymm (hs ▸ measure_sub_le_totalVariation ν μ A hA) bot_le
  · rintro rfl
    simp [totalVariation]

local instance localLimitUniquenessConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

private theorem window_count (R : ℝ) (B : Set ℝ) (C : LineConfiguration) :
    count (restrictConfiguration (Icc (-R) R) C) B = count C (B ∩ Icc (-R) R) := by
  unfold count restrictConfiguration
  congr 2
  ext x
  simp only [mem_inter_iff]
  tauto

private theorem window_measurable (R : ℝ) :
    Measurable (restrictConfiguration (Icc (-R) R)) := by
  apply Measurable.of_le_map
  change (⨆ (B : Set ℝ) (_ : MeasurableSet B) (_ : Bornology.IsBounded B),
    MeasurableSpace.comap (fun C : LineConfiguration => count C B) inferInstance) ≤ _
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun hb => ?_
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  rw [MeasurableSpace.map_comp]
  apply Measurable.le_map
  change Measurable (fun C : LineConfiguration =>
    count (restrictConfiguration (Icc (-R) R) C) B)
  simp_rw [window_count]
  exact FrozenSanity.measurable_count _ (hB.inter measurableSet_Icc)
    (hb.subset inter_subset_left)

private theorem window_comp {R S : ℝ} (h : R ≤ S) :
    restrictConfiguration (Icc (-R) R) ∘ restrictConfiguration (Icc (-S) S) =
      restrictConfiguration (Icc (-R) R) := by
  funext C
  apply Subtype.ext
  ext x
  change ((x ∈ C.val ∧ -S ≤ x ∧ x ≤ S) ∧ -R ≤ x ∧ x ≤ R) ↔ _
  constructor
  · exact fun hx => ⟨hx.1.1, hx.2⟩
  · exact fun hx => ⟨⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩, hx.2⟩

/-- Window sigma-algebras increase with their radii. -/
theorem configuration_windowSpace_mono {R S : ℝ} (h : R ≤ S) :
    configurationMeasurableSpace.comap (restrictConfiguration (Icc (-R) R)) ≤
      configurationMeasurableSpace.comap (restrictConfiguration (Icc (-S) S)) := by
  have hm := MeasurableSpace.comap_mono (g := restrictConfiguration (Icc (-S) S))
    (window_measurable R).comap_le
  rwa [MeasurableSpace.comap_comp, window_comp h] at hm

/-- Bounded windows generate the configuration sigma-algebra, Theorem 3. -/
theorem configurationMeasurableSpace_eq_iSup_windows :
    configurationMeasurableSpace = ⨆ n : ℕ,
      configurationMeasurableSpace.comap (restrictConfiguration (Icc (-(n + 1 : ℝ)) (n + 1))) := by
  apply le_antisymm
  · change (⨆ (B : Set ℝ) (_ : MeasurableSet B) (_ : Bornology.IsBounded B),
      MeasurableSpace.comap (fun C : LineConfiguration => count C B) inferInstance) ≤ _
    refine iSup_le fun B => iSup_le fun hB => iSup_le fun hb => ?_
    obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : ℝ)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hBW : B ⊆ Icc (-(n + 1 : ℝ)) (n + 1) := by
      rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr
      exact hr.trans (Icc_subset_Icc (by linarith) (by linarith))
    have he : (fun C : LineConfiguration => count C B) =
        (fun C : LineConfiguration => count C B) ∘
          restrictConfiguration (Icc (-(n + 1 : ℝ)) (n + 1)) := by
      funext C
      simp only [Function.comp_apply, window_count, inter_eq_left.mpr hBW]
    rw [he, ← MeasurableSpace.comap_comp]
    apply le_iSup_of_le n
    exact MeasurableSpace.comap_mono (FrozenSanity.measurable_count B hB hb).comap_le
  · exact iSup_le fun n => (window_measurable (n + 1)).comap_le

/-- Laws agreeing on every bounded symmetric window are equal.
This is the generating-family step in Theorem 3. -/
theorem pointProcess_eq_of_window_laws (P Q : PointProcess)
    (h : ∀ R : ℝ, 0 < R →
      (P : Measure LineConfiguration).map (restrictConfiguration (Icc (-R) R)) =
        (Q : Measure LineConfiguration).map (restrictConfiguration (Icc (-R) R))) : P = Q := by
  let m : ℕ → MeasurableSpace LineConfiguration := fun n =>
    configurationMeasurableSpace.comap (restrictConfiguration (Icc (-(n + 1 : ℝ)) (n + 1)))
  have hm : Monotone m := by
    intro n k hnk
    apply configuration_windowSpace_mono
    exact_mod_cast Nat.add_le_add_right hnk 1
  have hgen : configurationMeasurableSpace = generateFrom (⋃ n, {A | MeasurableSet[m n] A}) :=
    configurationMeasurableSpace_eq_iSup_windows.trans
      (generateFrom_iUnion_measurableSet m).symm
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (⋃ n, {A | MeasurableSet[m n] A}) hgen
    (isPiSystem_iUnion_of_monotone _ (fun n => @isPiSystem_measurableSet _ (m n))
      (fun n k hnk => hm hnk))
  · intro A hA
    obtain ⟨n, B, hB, rfl⟩ := mem_iUnion.mp hA
    have he := congrArg (fun μ : Measure LineConfiguration => μ B) (h (n + 1) (by positivity))
    simpa only [Measure.map_apply (window_measurable _) hB] using he
  · simp

/-- See Theorem 3 of the paper: a sequence of point-process laws has at most one
limit in local total variation. -/
theorem localConverges_unique
    (laws : ℕ+ → @Measure LineConfiguration configurationMeasurableSpace)
    (P Q : PointProcess) (hP : LocalConverges laws P) (hQ : LocalConverges laws Q) : P = Q := by
  obtain ⟨hprob, hP⟩ := hP
  obtain ⟨_, hQ⟩ := hQ
  have (N : ℕ+) : IsProbabilityMeasure (laws N) := hprob N
  apply pointProcess_eq_of_window_laws P Q
  intro R hR
  let f := restrictConfiguration (Icc (-R) R)
  apply (totalVariation_eq_zero_iff _ _).mp
  apply le_antisymm _ bot_le
  have ht := (hP R hR).add (hQ R hR)
  rw [zero_add] at ht
  apply ge_of_tendsto ht
  filter_upwards [] with n
  rw [totalVariation_symm ((laws (Riesz1.particleNumber n)).map f)
    ((P : Measure LineConfiguration).map f)]
  exact totalVariation_triangle _ _ _

end Riesz2
