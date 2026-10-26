/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.KernelAtParameters
public import Riesz2.Frozen.GapAmbientDomain
public import Riesz2.Frozen.InteriorCirclePoint

/-!
# Ambient extension of the physical gap energy: `Riesz2.physicalAmbientGapEnergy`

The extension H_N^g in equation (3.8), evaluated on U_N. Every kernel argument lies in
(0,1). Antipodal intervals have weight one, and all other intervals have weight two.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The extension H_N^g in equation (3.8), evaluated on U_N. Every kernel argument lies in
(0,1). Antipodal intervals have weight one, and all other intervals have weight two. -/
def physicalAmbientGapEnergy (p : Parameters) (N : ℕ+)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) : ℝ :=
  (N : ℝ) ^ (-p.val.2) * ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
    (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
      kernelAtParameters p (interiorCirclePoint
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val) / (N : ℝ), by
          have hi := y.property i (r.val + 1) (by omega) (by omega)
          have hpos : (0 : ℝ) < N := by exact_mod_cast N.pos
          exact ⟨div_pos hi.1 hpos, (div_lt_one hpos).mpr hi.2⟩⟩)

end Riesz2

end
end
