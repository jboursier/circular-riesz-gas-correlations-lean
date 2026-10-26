/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ScalarFormData

/-!
# Weak scalar Neumann Poisson equation: `Riesz2.ScalarPoissonSolution`

The mean-zero weak equation Lψ = G − E_νG, tested on the full scalar form domain.
Integrability of the right-hand pairing is explicit. It agrees with the weak graph of
`Riesz1.hsNeumannGraph` in the particle setting. See Subsection 3.1 and Proposition 3.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The mean-zero weak equation Lψ = G − E_νG, tested on the full scalar form domain.
Integrability of the right-hand pairing is explicit. It agrees with the weak graph of
`Riesz1.hsNeumannGraph` in the particle setting. See Subsection 3.1 and Proposition 3.3. -/
def ScalarPoissonSolution {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (Q : ScalarFormData ν) (G ψ : Q.1) : Prop :=
  Integrable G.val ν ∧ Integrable ψ.val ν ∧ (∫ x, ψ.val x ∂ν) = 0 ∧
  ∀ h : Q.1,
    Integrable (fun x => (G.val x - ∫ y, G.val y ∂ν) * h.val x) ν ∧
    Q.2 ψ h = ∫ x, (G.val x - ∫ y, G.val y ∂ν) * h.val x ∂ν

end Riesz2

end
end
