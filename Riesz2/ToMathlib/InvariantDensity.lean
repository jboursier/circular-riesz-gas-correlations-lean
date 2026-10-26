/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Invariant densities

A measure-preserving map `T` leaves `μ.withDensity g` invariant when the density satisfies
`g (T x) = g x`. This is the form in which a symmetry of an energy acts on a Gibbs measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz2
namespace InvariantDensity

/-- A measure-preserving map fixes a density that is invariant along its orbits. -/
theorem map_withDensity_eq_self {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} (hT : MeasurePreserving T μ μ) {g : α → ℝ≥0∞} (hg : Measurable g)
    (hgT : ∀ x, g (T x) = g x) :
    (μ.withDensity g).map T = μ.withDensity g := by
  ext s hs
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs),
    withDensity_apply _ hs, ← hT.setLIntegral_comp_preimage hs hg]
  simp only [hgT]

end InvariantDensity
end Riesz2
end
end
