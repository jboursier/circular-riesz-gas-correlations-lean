/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
public import Riesz1.Frozen.CyclicLift
public import Riesz1.Frozen.AlmostOptimalRigidity

/-! # Library identification and nonvacuity of rigidity -/
public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace Riesz2.DefinitionSanity

theorem rigidity_ranges_nonempty :
    ∃ (N : ℕ+) (_i : Fin (N : ℕ)) (k : ℕ),
      2 ≤ (N : ℕ) ∧ 1 ≤ k ∧ k ≤ (N : ℕ) / 2 := by
  exact ⟨2, ⟨0, by norm_num⟩, 1, by norm_num, by norm_num, by norm_num⟩

end Riesz2.DefinitionSanity
end
end
