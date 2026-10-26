/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapTangentSpace

/-!
# Rotation-periodic particle chamber: `Riesz2.particleChamber`

The ordered particle chamber D_N of Subsection 3.1 and Assumptions 3.1, without a cut on the
rotation coordinate. It agrees with `Riesz1.hsChamber`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The ordered particle chamber D_N of Subsection 3.1 and Assumptions 3.1, without a cut on the
rotation coordinate. It agrees with `Riesz1.hsChamber`. -/
def particleChamber (N : ℕ+) : Set (EuclideanSpace ℝ (Fin (N : ℕ))) :=
  {x | StrictMono (fun i => x i) ∧ ∀ i, x i < x ⟨0, N.pos⟩ + 1}

end Riesz2

end
end
