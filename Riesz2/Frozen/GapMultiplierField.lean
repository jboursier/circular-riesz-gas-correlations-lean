/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ScalarFormData
public import Riesz2.Frozen.MatrixFieldPair
public import Mathlib.Data.PNat.Basic

/-!
# Multiplier for the total-gap constraint: `Riesz2.gapMultiplierField`

The multiplier λ = N⁻¹1ᵀ(Mu−v) of equation (3.7). It is interpreted as a local distribution
through smooth compactly supported tests in Proposition 3.3. For a gradient source, v is the
canonical tangent representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The multiplier λ = N⁻¹1ᵀ(Mu−v) of equation (3.7). It is interpreted as a local distribution
through smooth compactly supported tests in Proposition 3.3. For a gradient source, v is the
canonical tangent representative. -/
def gapMultiplierField {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (N : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1) (x : α) : ℝ :=
  (N : ℝ)⁻¹ * ((∑ i, ∑ j, M x i j * (u j).val x) - ∑ i, v i x)

end Riesz2

end
end
