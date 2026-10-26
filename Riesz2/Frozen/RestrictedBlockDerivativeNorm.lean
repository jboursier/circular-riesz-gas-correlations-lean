/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.BlockObservable

/-!
# Derivative norm restricted to a good event: `Riesz2.restrictedBlockDerivativeNorm`

The sum of the least coordinate Lipschitz constants restricted to A. For the interior of the
convex good event this encodes D_A, the sum of essential weak derivative bounds in Lemma
6.5. Continuity extends the bounds to the boundary, and global Lipschitz bounds ensure that
the defining infima are over nonempty sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The sum of the least coordinate Lipschitz constants restricted to A. For the interior of the
convex good event this encodes D_A, the sum of essential weak derivative bounds in Lemma
6.5. Continuity extends the bounds to the boundary, and global Lipschitz bounds ensure that
the defining infima are over nonempty sets. -/
def restrictedBlockDerivativeNorm {n : ℕ+} (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) (A : Set (Fin (n : ℕ) → ℝ)) : ℝ :=
  ∑ j ∈ J, (sInf {L : ℝ≥0 | ∀ (x : Fin (n : ℕ) → ℝ) (t : ℝ),
    x ∈ A → Function.update x j t ∈ A →
    |G.val (Function.update x j t) - G.val x| ≤ (L : ℝ) * |t - x j|} : ℝ≥0)

end Riesz2

end
end
