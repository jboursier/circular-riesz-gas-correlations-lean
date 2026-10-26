/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic

/-!
# Distance to the boundary of an affine polytope

Let `ℓ j` for `j` in a finite index type be affine functions on a finite-dimensional real normed
space `E`, and let `Ω = {x | ∀ j, 0 < ℓ j x}` be bounded and nonempty. The set `Ω` is open
(`isOpen_polytope`). Every boundary point lies on some face `{ℓ j = 0}` (`frontier_subset_zero`),
so the distance from an interior point `x` to the boundary is at least `(⨅ j, ℓ j x) / G`, where `G`
bounds the Lipschitz constants of the faces (`div_le_infDist_frontier`).
-/

@[expose] public section

namespace Riesz2.AffinePolytope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The open polytope `{x | ∀ j, 0 < ℓ j x}` is open. -/
theorem isOpen_polytope [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] (ℓ : ι → E →ᵃ[ℝ] ℝ) :
    IsOpen {x : E | ∀ j, 0 < ℓ j x} := by
  have hset : {x : E | ∀ j, 0 < ℓ j x} = ⋂ j, {x : E | 0 < ℓ j x} := by
    ext x
    simp
  rw [hset]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional (ℓ j))

/-- Every boundary point of `{x | ∀ j, 0 < ℓ j x}` lies on some face `{ℓ j = 0}`. -/
theorem frontier_subset_zero [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (ℓ : ι → E →ᵃ[ℝ] ℝ) {y : E} (hy : y ∈ frontier {x : E | ∀ j, 0 < ℓ j x}) :
    ∃ j, ℓ j y = 0 := by
  have hopen := isOpen_polytope ℓ
  have hclosed : IsClosed {x : E | ∀ j, 0 ≤ ℓ j x} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun j =>
      isClosed_le continuous_const (AffineMap.continuous_of_finiteDimensional (ℓ j))
  have hcl : closure {x : E | ∀ j, 0 < ℓ j x} ⊆ {x : E | ∀ j, 0 ≤ ℓ j x} :=
    closure_minimal (fun x hx j => (hx j).le) hclosed
  have hyo : y ∉ {x : E | ∀ j, 0 < ℓ j x} := by
    have h := hy.2
    rwa [hopen.interior_eq] at h
  have hnonneg : ∀ j, 0 ≤ ℓ j y := hcl hy.1
  have hyo' : ¬ ∀ j, 0 < ℓ j y := hyo
  simp only [not_forall, not_lt] at hyo'
  obtain ⟨j, hj⟩ := hyo'
  exact ⟨j, le_antisymm hj (hnonneg j)⟩

/-- A bounded nonempty open subset of a nontrivial finite-dimensional real normed space has a
nonempty frontier. -/
theorem frontier_nonempty [Nontrivial E] {Ω : Set E} (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) : (frontier Ω).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hclopen : IsClopen Ω := isClopen_iff_frontier_eq_empty.mpr h
  rw [hclopen.eq_univ hne] at hb
  exact NormedSpace.unbounded_univ ℝ E hb

/-- For finitely many affine functions there is one constant `G > 0` bounding all their increments
by `G ‖u - v‖`. -/
theorem exists_lipschitz [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] (ℓ : ι → E →ᵃ[ℝ] ℝ) :
    ∃ G : ℝ, 0 < G ∧ ∀ j, ∀ u v : E, ℓ j u - ℓ j v ≤ G * ‖u - v‖ := by
  have hK : ∀ j, ∃ K : ℝ, ∀ u v : E, ℓ j u - ℓ j v ≤ K * ‖u - v‖ := by
    intro j
    refine ⟨‖LinearMap.toContinuousLinearMap (ℓ j).linear‖, fun u v => ?_⟩
    have hlin : ℓ j u - ℓ j v = (ℓ j).linear (u - v) := by
      have h := AffineMap.linear_apply_vsub (ℓ j) u v
      simp only [vsub_eq_sub] at h
      exact h.symm
    have hop := (LinearMap.toContinuousLinearMap (ℓ j).linear).le_opNorm (u - v)
    rw [Real.norm_eq_abs] at hop
    have hcoe :
        (LinearMap.toContinuousLinearMap (ℓ j).linear) (u - v) = (ℓ j).linear (u - v) := rfl
    rw [hlin, ← hcoe]
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hop)
  choose K hK using hK
  classical
  have := Fintype.ofFinite ι
  refine ⟨1 + ∑ j, |K j|, by positivity, fun j u v => ?_⟩
  have hsum : |K j| ≤ ∑ i, |K i| :=
    Finset.single_le_sum (f := fun i => |K i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  calc ℓ j u - ℓ j v ≤ K j * ‖u - v‖ := hK j u v
    _ ≤ |K j| * ‖u - v‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ (1 + ∑ i, |K i|) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- Let `Ω = {x | ∀ j, 0 < ℓ j x}` be bounded, and let `G > 0` bound the increments of the affine
functions `ℓ j`. For every `x ∈ Ω`, the distance from `x` to the frontier of `Ω` is at least
`(⨅ j, ℓ j x) / G`. -/
theorem div_le_infDist_frontier [Nontrivial E] [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (ℓ : ι → E →ᵃ[ℝ] ℝ)
    {Ω : Set E} (hΩ : Ω = {x : E | ∀ j, 0 < ℓ j x}) (hb : Bornology.IsBounded Ω)
    {G : ℝ} (hG : 0 < G) (hlip : ∀ j, ∀ u v : E, ℓ j u - ℓ j v ≤ G * ‖u - v‖)
    {x : E} (hx : x ∈ Ω) :
    (⨅ j, ℓ j x) / G ≤ Metric.infDist x (frontier Ω) := by
  subst hΩ
  have hne : (frontier {x : E | ∀ j, 0 < ℓ j x}).Nonempty :=
    frontier_nonempty ⟨x, hx⟩ hb
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  obtain ⟨j, hj⟩ := frontier_subset_zero ℓ hy
  have h1 : (⨅ i, ℓ i x) ≤ ℓ j x := ciInf_le (Finite.bddBelow_range _) j
  have h2 : ℓ j x - ℓ j y ≤ G * ‖x - y‖ := hlip j x y
  rw [hj, sub_zero] at h2
  rw [dist_eq_norm, div_le_iff₀ hG]
  linarith [mul_comm G ‖x - y‖]

end Riesz2.AffinePolytope

end
