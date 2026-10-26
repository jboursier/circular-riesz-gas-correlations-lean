/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ScalarFormData
public import Riesz2.Frozen.MatrixFieldPair

/-!
# Finite matrix-energy domain: `Riesz2.WeightedFormDomain`

Fields in the scalar form domain that take values in a fixed subspace S and have integrable
matrix energy uᵀMu. For nonnegative M this is finite nonnegative matrix energy. See
Subsection 3.5 and Lemma 4.4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- Fields in the scalar form domain that take values in a fixed subspace S and have integrable
matrix energy uᵀMu. For nonnegative M this is finite nonnegative matrix energy. See
Subsection 3.5 and Lemma 4.4. -/
def WeightedFormDomain {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ρ : Measure α} (Q : ScalarFormData ρ) (M : α → Matrix ι ι ℝ)
    (S : Submodule ℝ (ι → ℝ)) (u : ι → Q.1) : Prop :=
  (∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S) ∧
  Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val)) ρ

end Riesz2

end
end
