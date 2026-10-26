/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.CyclicGapSum
public import Riesz2.Frozen.GapTangentSpace

/-!
# Domain of the ambient gap energy: `Riesz2.gapAmbientDomain`

The open set U_N where 0 < L_{i,r}(y) < N for every cyclic interval with 1 ≤ r ≤ floor(N/2).
It is the domain of the ambient extension in equation (3.8). Every positive mass-N simplex
point belongs to U_N when N ≥ 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The open set U_N where 0 < L_{i,r}(y) < N for every cyclic interval with 1 ≤ r ≤ floor(N/2).
It is the domain of the ambient extension in equation (3.8). Every positive mass-N simplex
point belongs to U_N when N ≥ 2. -/
def gapAmbientDomain (N : ℕ+) : Set (EuclideanSpace ℝ (Fin (N : ℕ))) :=
  {y | ∀ (i : Fin (N : ℕ)) (r : ℕ), 1 ≤ r → r ≤ (N : ℕ) / 2 →
    0 < cyclicGapSum N i r (WithLp.ofLp y) ∧
      cyclicGapSum N i r (WithLp.ofLp y) < (N : ℝ)}

end Riesz2

end
end
