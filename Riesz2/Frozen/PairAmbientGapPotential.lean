/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ParticlePairEnergy

/-!
# Pair potential in ambient gap coordinates: `Riesz2.pairAmbientGapPotential`

The potential W obtained from H = 2∑_{i<j}χ_ij(x_j−x_i) by reconstructing relative positions
from cumulative gaps. On the mass simplex, every pair argument lies in (0,1). Subtracting
the mean position preserves pair separations. See Subsection 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The potential W obtained from H = 2∑_{i<j}χ_ij(x_j−x_i) by reconstructing relative positions
from cumulative gaps. On the mass simplex, every pair argument lies in (0,1). Subtracting
the mean position preserves pair separations. See Subsection 3.2. -/
def pairAmbientGapPotential {N : ℕ+} (χ : ParticlePairData N)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  2 * ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
    χ p ((∑ a ∈ Finset.univ.filter
      (fun a : Fin (N : ℕ) => p.val.1.val ≤ a.val ∧ a.val < p.val.2.val), y a) / (N : ℝ))

end Riesz2

end
end
