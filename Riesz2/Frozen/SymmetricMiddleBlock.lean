/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.BlockObservable

/-!
# Symmetric middle block of labels: `Riesz2.symmetricMiddleBlock`

The block {floor(n/2)−K,…,floor(n/2)+K} in Proposition 6.6, with labels shifted down by one
in Lean. The comparison statement imposes K ≤ floor(n/4) and a strict bound when n ≡ 1 mod
4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The block {floor(n/2)−K,…,floor(n/2)+K} in Proposition 6.6, with labels shifted down by one
in Lean. The comparison statement imposes K ≤ floor(n/4) and a strict bound when n ≡ 1 mod
4. -/
def symmetricMiddleBlock (n : ℕ+) (K : ℕ) : Finset (Fin (n : ℕ)) :=
  Finset.univ.filter (fun i => (n : ℕ) / 2 ≤ i.val + 1 + K ∧
    i.val + 1 ≤ (n : ℕ) / 2 + K)

end Riesz2

end
end
