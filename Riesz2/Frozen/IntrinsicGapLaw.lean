/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.CenteredGapChart
public import Riesz2.Frozen.GapVector

/-!
# Gap law in intrinsic coordinates: `Riesz2.intrinsicGapLaw`

The image ν = Gap_N#μ in the isometric affine chart y = 1 + z of Subsection 3.2. Since every
gap vector has total mass N, the chart subtracts one from each coordinate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The image ν = Gap_N#μ in the isometric affine chart y = 1 + z of Subsection 3.2. Since every
gap vector has total mass N, the chart subtracts one from each coordinate. -/
def intrinsicGapLaw {N : ℕ+} (μ : Measure (Riesz1.Configuration N)) :
    Measure (gapTangentSpace N) :=
  μ.map (fun X => centeredGapChart N (WithLp.toLp 2 (gapVector X)))

end Riesz2

end
end
