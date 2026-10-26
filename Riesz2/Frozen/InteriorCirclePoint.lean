/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.UnitLength

/-!
# Nonzero circle point from an interior lift: `Riesz2.interiorCirclePoint`

A real x ∈ (0,1) viewed as a nonzero point of the unit circle. This supplies the
noncollision arguments of the sampled kernel in Subsection 2.4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- A real x ∈ (0,1) viewed as a nonzero point of the unit circle. This supplies the
noncollision arguments of the sampled kernel in Subsection 2.4. -/
def interiorCirclePoint (x : {x : ℝ // 0 < x ∧ x < 1}) :
    {x : UnitAddCircle // x ≠ 0} :=
  ⟨(x.val : UnitAddCircle), by
    intro h
    have h0 : x.val = 0 :=
      (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ))
        (show x.val ∈ Ico (0 : ℝ) 1 from ⟨le_of_lt x.property.1, x.property.2⟩)).mp h
    exact (ne_of_gt x.property.1) h0⟩

end Riesz2

end
end
