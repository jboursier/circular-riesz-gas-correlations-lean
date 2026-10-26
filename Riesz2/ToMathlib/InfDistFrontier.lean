/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distance from a point of an open set to its frontier

For an open set `U` in a real normed space, a point `x ∈ U` and a point `y ∉ U`, the segment
from `x` to `y` meets the frontier of `U`. The distance from `x` to the frontier of `U` is then
the distance from `x` to the complement of `U`, which is the distance to the boundary used in the
collision-barrier bridge.
-/

@[expose] public section

open Metric Set

namespace Riesz2

/-- Let `U` be open, `x ∈ U` and `y ∉ U`. Then the segment from `x` to `y` contains a point of the
frontier of `U`. -/
theorem exists_mem_frontier_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x y : E} (hx : x ∈ U) (hy : y ∉ U) :
    ∃ z ∈ frontier U, z ∈ segment ℝ x y := by
  by_contra hcon
  push Not at hcon
  have hsub : segment ℝ x y ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · refine Or.inr fun hzc => hcon z ?_ hz
      rw [hU.frontier_eq]
      exact ⟨hzc, hzU⟩
  have hdisj : Disjoint U (closure U)ᶜ :=
    Set.disjoint_left.mpr fun z hzU hzc => hzc (subset_closure hzU)
  have hopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hall : segment ℝ x y ⊆ U :=
    (convex_segment x y).isPreconnected.subset_left_of_subset_union hU hopen hdisj hsub
      ⟨x, left_mem_segment ℝ x y, hx⟩
  exact hy (hall (right_mem_segment ℝ x y))

/-- Let `U` be open, `x ∈ U`, and let the complement `Uᶜ` be nonempty. Then the distance from `x`
to the frontier of `U` equals the distance from `x` to `Uᶜ`. -/
theorem infDist_frontier_eq_infDist_compl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (hne : Uᶜ.Nonempty) :
    infDist x (frontier U) = infDist x Uᶜ := by
  have hfr : frontier U ⊆ Uᶜ := fun z hz => by
    rw [hU.frontier_eq] at hz
    exact hz.2
  have hF : (frontier U).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz, -⟩ := exists_mem_frontier_segment hU hx hy
    exact ⟨z, hz⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset hfr hF)
  rw [le_infDist hne]
  intro y hy
  obtain ⟨z, hz, hzseg⟩ := exists_mem_frontier_segment hU hx hy
  have hsplit := dist_add_dist_of_mem_segment hzseg
  have hzy : infDist x (frontier U) ≤ dist x z := infDist_le_dist_of_mem hz
  linarith [dist_nonneg (x := z) (y := y)]

end Riesz2
