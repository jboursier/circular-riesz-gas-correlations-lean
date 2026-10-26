/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth convex cutoff for gap penalties: `Riesz2.PhysicalCutoff`

The cutoff θ on [0,+∞) used in Section 5 and Subsection 6.1. It is nonnegative, smooth and
convex, vanishes on [0,1/2], and has bounded second derivative with θ'' ≥ 1 on [1,+∞).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The cutoff θ on [0,+∞) used in Section 5 and Subsection 6.1. It is nonnegative, smooth and
convex, vanishes on [0,1/2], and has bounded second derivative with θ'' ≥ 1 on [1,+∞). -/
@[reducible] def PhysicalCutoff :=
  {θ : ℝ → ℝ // ContDiffOn ℝ (⊤ : ℕ∞) θ (Ici 0) ∧ ConvexOn ℝ (Ici 0) θ ∧
    (∀ x ∈ Ici (0 : ℝ), 0 ≤ θ x) ∧
    (∀ x ∈ Icc (0 : ℝ) (1 / 2), θ x = 0) ∧
    ∃ C : ℝ, 1 ≤ C ∧ (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ) x ∧
      deriv (deriv θ) x ≤ C) ∧ (∀ x : ℝ, 1 ≤ x → 1 ≤ deriv (deriv θ) x)}

end Riesz2

end
end
