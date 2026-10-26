/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PhysicalAmbientGapEnergy
public import Riesz2.Frozen.PhysicalCutoff

/-!
# Full tilted gap potential: `Riesz2.fullPhysicalPotentialValue`

The potential β(H_N^g + F), with the ambient extension of equation (3.8) and either the
upper-gap or two-sided penalty of Section 5 and Subsection 6.1. It is evaluated on U_N,
where the gap coordinates are positive for N ≥ 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The potential β(H_N^g + F), with the ambient extension of equation (3.8) and either the
upper-gap or two-sided penalty of Section 5 and Subsection 6.1. It is evaluated on U_N,
where the gap coordinates are positive for N ≥ 2. -/
def fullPhysicalPotentialValue (p : Parameters) (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) : ℝ :=
  p.val.1 * (physicalAmbientGapEnergy p N y +
    ∑ i : Fin (N : ℕ), (θ.val ((N : ℝ) ^ (-ε) * y.val i) +
      if twoSided then θ.val ((N : ℝ) ^ (-ε) * (y.val i)⁻¹) else 0))

end Riesz2

end
end
