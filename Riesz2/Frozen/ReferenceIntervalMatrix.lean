/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.SampledSecondDifference
public import Riesz2.Frozen.CyclicIndexInterval

/-!
# Truncated reference interval matrix: `Riesz2.referenceIntervalMatrix`

The interval sum defining 𝔾_{N,s}^{[K]} in Subsection 2.5 and Subsection 5.1, retaining
lengths r ≥ K. It is zero if K > floor(N/2). Equation (3.10) compares twice the untruncated
matrix with the physical Hessian at the equally spaced configuration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The interval sum defining 𝔾_{N,s}^{[K]} in Subsection 2.5 and Subsection 5.1, retaining
lengths r ≥ K. It is zero if K > floor(N/2). Equation (3.10) compares twice the untruncated
matrix with the physical Hessian at the equally spaced configuration. -/
def referenceIntervalMatrix (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  fun a b => ∑ i : Fin (N : ℕ),
    ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r),
      (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s N hN ⟨r % (N : ℕ), Nat.mod_lt _ N.pos⟩ *
        (if a ∈ cyclicIndexInterval N i r then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i r then 1 else 0)

end Riesz2

end
end
