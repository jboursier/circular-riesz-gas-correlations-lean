/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ScalarFormData

/-!
# Conservative scalar forms: `Riesz2.IsConservativeScalarForm`

The constant function one belongs to the form domain and has zero energy. This encodes
conservativity in Assumptions 4.1 and 5.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The constant function one belongs to the form domain and has zero energy. This encodes
conservativity in Assumptions 4.1 and 5.2. -/
def IsConservativeScalarForm {α : Type*} [MeasurableSpace α]
    {ρ : Measure α} (Q : ScalarFormData ρ) : Prop :=
  ∃ one : Q.1, (∀ᵐ x ∂ρ, one.val x = 1) ∧ Q.2 one one = 0

end Riesz2

end
end
