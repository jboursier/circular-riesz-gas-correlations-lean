/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.BlockObservable

/-!
# Good event for an active gap block: `Riesz2.goodBlockEvent`

The event A_N of Subsection 6.1, with bounds on each gap, every ordinary interval sum and
the total active mass. In Lemma 6.5 the parameter η is K_s ε.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The event A_N of Subsection 6.1, with bounds on each gap, every ordinary interval sum and
the total active mass. In Lemma 6.5 the parameter η is K_s ε. -/
def goodBlockEvent (s : ℝ) (n N : ℕ+) (η : ℝ) : Set (Fin (n : ℕ) → ℝ) :=
  {x | (∑ i, x i) < (N : ℝ) ∧
    (∀ i, (n : ℝ) ^ (-η) ≤ x i ∧ x i ≤ (n : ℝ) ^ η) ∧
    ∀ a b : ℕ, a < b → b ≤ (n : ℕ) →
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b), x i) -
        (b - a : ℕ)| ≤ (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2)}

end Riesz2

end
end
