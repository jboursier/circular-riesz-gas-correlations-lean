/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PhysicalCutoff
public import Riesz2.Frozen.Gap

/-!
# Upper-gap and two-sided penalties: `Riesz2.physicalGapPenalty`

The sum of θ(n^{-ε}y_i) over the first n microscopic gaps, with θ(n^{-ε}y_i⁻¹) added when
`twoSided` is true. These are the upper-gap penalty of Section 5 and the two-sided penalty
of equation (6.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The sum of θ(n^{-ε}y_i) over the first n microscopic gaps, with θ(n^{-ε}y_i⁻¹) added when
`twoSided` is true. These are the upper-gap penalty of Section 5 and the two-sided penalty
of equation (6.1). -/
def physicalGapPenalty (N n : ℕ+) (_hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) (X : Riesz1.Configuration N) : ℝ :=
  ∑ i : Fin (n : ℕ), (θ.val ((n : ℝ) ^ (-ε) * gap X i.val) +
    if twoSided then θ.val ((n : ℝ) ^ (-ε) * (gap X i.val)⁻¹) else 0)

end Riesz2

end
end
