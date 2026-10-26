/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ParticlePairData

/-!
# Energy of general pair potentials: `Riesz2.particlePairEnergy`

The energy H = 2∑_{i<j}χ_ij(x_j−x_i) of Subsection 3.1, with temperature included in χ. It
agrees with `Riesz1.hsPairExpression` after translating the pair indices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The energy H = 2∑_{i<j}χ_ij(x_j−x_i) of Subsection 3.1, with temperature included in χ. It
agrees with `Riesz1.hsPairExpression` after translating the pair indices. -/
def particlePairEnergy {N : ℕ+} (χ : ParticlePairData N)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  2 * ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
    χ p (x p.val.2 - x p.val.1)

end Riesz2

end
end
