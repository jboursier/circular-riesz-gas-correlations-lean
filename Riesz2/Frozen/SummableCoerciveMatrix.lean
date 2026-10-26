/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ComponentDistance
public import Riesz2.Frozen.MatrixFieldPair
public import Riesz2.Frozen.ShortExponent
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Summable coercive matrix fields: `Riesz2.SummableCoerciveMatrix`

The measurable symmetric matrix M of Assumptions 4.2, with coercivity (A n^{qh})⁻¹ and entry
bounds A n^{qh}(1+d(i,j))^{-s}. The ranges h > 0, A ≥ 1 and q ≥ 0 are explicit in the decay
statements.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The measurable symmetric matrix M of Assumptions 4.2, with coercivity (A n^{qh})⁻¹ and entry
bounds A n^{qh}(1+d(i,j))^{-s}. The ranges h > 0, A ≥ 1 and q ≥ 0 are explicit in the decay
statements. -/
def SummableCoerciveMatrix {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] {ρ : Measure α} (s : ShortExponent) (n : ℕ+)
    (h A q : ℝ) (g : ComponentGeometry ι) (M : α → Matrix ι ι ℝ) : Prop :=
  (∀ i j, Measurable (fun x => M x i j)) ∧ ∀ᵐ x ∂ρ,
    (∀ i j, M x i j = M x j i) ∧
    (∀ z : ι → ℝ,
      (A * (n : ℝ) ^ (q * h))⁻¹ * (∑ i, z i ^ 2) ≤
        ∑ i, ∑ j, z i * M x i j * z j) ∧
    (∀ i j, |M x i j| ≤ A * (n : ℝ) ^ (q * h) *
      (1 + componentDistance g i j) ^ (-s.val))

end Riesz2

end
end
