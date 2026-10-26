/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.CyclicGapSum

/-!
# Cyclic interval of component labels: `Riesz2.cyclicIndexInterval`

The cyclic interval {i,…,i+r−1} of labels modulo N, used in the interval representation of
Subsection 2.5. The matrix formulas use 1 ≤ r ≤ floor(N/2), so no label repeats.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The cyclic interval {i,…,i+r−1} of labels modulo N, used in the interval representation of
Subsection 2.5. The matrix formulas use 1 ≤ r ≤ floor(N/2), so no label repeats. -/
def cyclicIndexInterval (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ) : Finset (Fin (N : ℕ)) :=
  (Finset.range r).image (fun a => (⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)))

end Riesz2

end
end
