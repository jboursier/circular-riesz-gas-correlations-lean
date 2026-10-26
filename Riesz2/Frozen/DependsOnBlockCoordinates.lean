/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.BlockObservable

/-!
# Dependence on a block of coordinates: `Riesz2.DependsOnBlockCoordinates`

The condition that G(x) = G(y) whenever x and y agree on the specified labels. This encodes
the coordinate support of observables in Proposition 6.6 and Theorem 4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The condition that G(x) = G(y) whenever x and y agree on the specified labels. This encodes
the coordinate support of observables in Proposition 6.6 and Theorem 4. -/
def DependsOnBlockCoordinates {n : ℕ+} (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) : Prop :=
  ∀ x y : Fin (n : ℕ) → ℝ, (∀ i ∈ J, x i = y i) → G.val x = G.val y

end Riesz2

end
end
