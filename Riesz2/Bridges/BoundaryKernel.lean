/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreBarrier
public import Riesz2.ToMathlib.InfDistFrontier

/-!
# Collision-barrier kernel theorem

This file applies `Riesz1.Internal.schrodinger_eq_zero_of_boundary_barrier` on a
bounded open set in a nontrivial finite-dimensional real inner product space.
The distance to the boundary is `Metric.infDist x (frontier U)`. For `x ∈ U` it
equals the distance to `Uᶜ` by `Riesz2.infDist_frontier_eq_infDist_compl`.
Boundedness and `Nontrivial E` ensure that `Uᶜ` is nonempty.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ContDiff

namespace Riesz2

/-- The companion collision-barrier kernel theorem. Let `E` be a nontrivial real inner product space of
finite dimension, and let `U ⊆ E` be a bounded open set. Let `W` be smooth on `U` with
`W x ≥ dist(x, ∂U)⁻² - C` for every `x ∈ U`, and let `C + 1 < lam`. If `u ∈ L²(U)` solves
`(-Δ + W + lam) u = 0` in the sense of distributions on `U`, then `u = 0` almost everywhere on
`U`. No boundary trace of `u` is assumed. -/
theorem collisionBarrierKernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {U : Set E} (hU : IsOpen U) (hB : Bornology.IsBounded U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) {C lam : ℝ} (hlam : C + 1 < lam)
    (hbar : ∀ x ∈ U, (infDist x (frontier U))⁻¹ ^ 2 - C ≤ W x)
    {u : E → ℝ} (huL : MemLp u 2 (volume.restrict U))
    (hu : Riesz1.IsDistributionalSchrodingerSolution U W lam u) :
    u =ᵐ[volume.restrict U] 0 := by
  have hUc : Uᶜ.Nonempty :=
    Set.nonempty_compl.mpr fun h => NormedSpace.unbounded_univ ℝ E (h ▸ hB)
  have hbar' : ∀ x ∈ U, (infDist x Uᶜ)⁻¹ ^ 2 - C ≤ W x := by
    intro x hx
    rw [← infDist_frontier_eq_infDist_compl hU hx hUc]
    exact hbar x hx
  exact Riesz1.Internal.schrodinger_eq_zero_of_boundary_barrier hU hB hUc hW (by linarith) hbar' huL
    hu

end Riesz2
