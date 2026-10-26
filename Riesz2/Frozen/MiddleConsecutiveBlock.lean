/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.BlockObservable

/-!
# Consecutive labels in the middle of a gap block: `Riesz2.MiddleConsecutiveBlock`

At most n/4 consecutive labels in the closed middle half of {1,…,n}, shifted down by one in
Lean. This is the support condition used in the proof of Proposition 6.6.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- At most n/4 consecutive labels in the closed middle half of {1,…,n}, shifted down by one in
Lean. This is the support condition used in the proof of Proposition 6.6. -/
def MiddleConsecutiveBlock (n : ℕ+) (J : Finset (Fin (n : ℕ))) : Prop :=
  ∃ a k : ℕ, k ≤ (n : ℕ) / 4 ∧ a + k ≤ (n : ℕ) ∧
    J = Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + k) ∧
    ∀ i ∈ J, (n : ℕ) ≤ 4 * (i.val + 1) ∧ 4 * (i.val + 1) ≤ 3 * (n : ℕ)

end Riesz2

end
end
