/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ComponentGeometry
public import Riesz1.Frozen.CyclicIndexDistance

/-!
# Distance between component labels: `Riesz2.componentDistance`

The distance inherited from the line or an ambient cycle in Section 4. On the line it is |i
− j|. On a cycle it is d_N(i,j).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The distance inherited from the line or an ambient cycle in Section 4. On the line it is |i
− j|. On a cycle it is d_N(i,j). -/
def componentDistance {ι : Type*} (g : ComponentGeometry ι) (i j : ι) : ℝ :=
  match g with
  | Sum.inl e => |(e i : ℝ) - (e j : ℝ)|
  | Sum.inr ⟨m, e⟩ => (Riesz1.cyclicIndexDistance m (e i) (e j) : ℝ)

end Riesz2

end
end
