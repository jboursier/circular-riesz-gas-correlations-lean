/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapTangentSpace

/-!
# Domain of a proper gap marginal: `Riesz2.properMarginalDomain`

The Euclidean domain B_{n,N} = {x_i > 0, ∑ᵢ x_i < N} for a proper active gap marginal. See
Subsection 3.2 and Appendix A.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The Euclidean domain B_{n,N} = {x_i > 0, ∑ᵢ x_i < N} for a proper active gap marginal. See
Subsection 3.2 and Appendix A. -/
def properMarginalDomain (n N : ℕ+) : Set (EuclideanSpace ℝ (Fin (n : ℕ))) :=
  {x | (∀ i, 0 < x i) ∧ (∑ i, x i) < (N : ℝ)}

end Riesz2

end
end
