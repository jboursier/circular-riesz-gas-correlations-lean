/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tightness on countable products

Uniform compact containment of each coordinate implies uniform compact containment
of the product, by a summable allocation of the error probability.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2

/-- A family of laws on a countable product is tight if every coordinate has
uniform compact containment. The coordinate spaces need not be metrizable. -/
theorem isTightMeasureSet_pi_of_coordinate_compacts
    {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [MeasurableSpace (∀ i, E i)]
    (S : Set (Measure (∀ i, E i)))
    (h : ∀ i (ε : ℝ≥0∞), 0 < ε → ∃ K : Set (E i), IsCompact K ∧
      ∀ μ ∈ S, μ {x | x i ∉ K} ≤ ε) : IsTightMeasureSet S := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  choose K hK hb using fun i => h i (δ i) (hδ i)
  refine ⟨Set.pi univ K, isCompact_univ_pi hK, ?_⟩
  intro μ hμ
  have he : (Set.pi univ K)ᶜ = ⋃ i, {x | x i ∉ K i} := by
    ext x
    simp
  rw [he]
  exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun i => hb i μ hμ).trans hs.le)

end Riesz2
