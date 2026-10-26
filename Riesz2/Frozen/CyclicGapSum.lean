/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapVector

/-!
# Sum over a cyclic interval of gaps: `Riesz2.cyclicGapSum`

The sum L_{i,r}(y) = y_i + ⋯ + y_{i+r−1}, with cyclic indices of period N, used in equation
(3.8).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The sum L_{i,r}(y) = y_i + ⋯ + y_{i+r−1}, with cyclic indices of period N, used in equation
(3.8). -/
def cyclicGapSum (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ)
    (y : Fin (N : ℕ) → ℝ) : ℝ :=
  ∑ a ∈ Finset.range r, y ⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩

end Riesz2

end
end
