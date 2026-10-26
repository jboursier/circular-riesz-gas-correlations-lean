/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapTangentSpace

/-!
# Gap simplex in intrinsic coordinates: `Riesz2.intrinsicGapDomain`

The positive mass-N simplex 𝓜_N in the chart y = 1 + z, with z ∈ 1⊥. See Subsection 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The positive mass-N simplex 𝓜_N in the chart y = 1 + z, with z ∈ 1⊥. See Subsection 3.2. -/
def intrinsicGapDomain (N : ℕ+) : Set (gapTangentSpace N) :=
  {z | ∀ i, 0 < 1 + z.val i}

end Riesz2

end
end
