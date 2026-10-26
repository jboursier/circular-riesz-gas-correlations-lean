/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.Frozen.GapTangentSpace

/-!
# Full tilted gap law in intrinsic coordinates: `Riesz2.fullIntrinsicTiltedGapLaw`

The pullback of the full tilted gap law by z ↦ 1 + z on the zero-sum subspace. The full gap
law is supported on the mass-N hyperplane, so this chart is bijective on its support. See
Subsection 3.2 and Section 5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The pullback of the full tilted gap law by z ↦ 1 + z on the zero-sum subspace. The full gap
law is supported on the mass-N hyperplane, so this chart is bijective on its support. See
Subsection 3.2 and Section 5. -/
def fullIntrinsicTiltedGapLaw (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (ε : ℝ) (twoSided : Bool) : Measure (gapTangentSpace N) :=
  (activeTiltedGapLaw p N N (le_refl _) θ ε twoSided).comap
    (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i))

end Riesz2

end
end
