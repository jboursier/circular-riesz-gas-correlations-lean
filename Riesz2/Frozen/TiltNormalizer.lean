/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PhysicalGapPenalty
public import Riesz2.Frozen.GibbsMeasure

/-!
# Normalizer of the gap tilt: `Riesz2.tiltNormalizer`

The integral E_{G_{N,β}} exp(−βF) for the gap penalty F. Strict positivity and finiteness
are conclusions of the statements using the tilted law. See Section 5 and Subsection 6.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The integral E_{G_{N,β}} exp(−βF) for the gap penalty F. Strict positivity and finiteness
are conclusions of the statements using the tilted law. See Section 5 and Subsection 6.1. -/
def tiltNormalizer (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε twoSided X))
    ∂gibbsMeasure p N

end Riesz2

end
end
