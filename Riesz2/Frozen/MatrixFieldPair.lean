/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Pairing of matrix fields and vector fields: `Riesz2.matrixFieldPair`

The pointwise pairing uᵀMv on a finite component space. It supplies the matrix term of the
finite-energy weak equations in Subsection 3.5 and Lemma 4.4, independently of the base
dimension.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The pointwise pairing uᵀMv on a finite component space. It supplies the matrix term of the
finite-energy weak equations in Subsection 3.5 and Lemma 4.4, independently of the base
dimension. -/
def matrixFieldPair {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ρ : Measure α} (M : α → Matrix ι ι ℝ)
    (u v : ι → Lp ℝ 2 ρ) (x : α) : ℝ :=
  ∑ i, ∑ j, u i x * M x i j * v j x

end Riesz2

end
end
