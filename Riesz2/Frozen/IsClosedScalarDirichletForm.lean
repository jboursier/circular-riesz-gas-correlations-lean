/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ScalarFormData

/-!
# Closed scalar Dirichlet forms: `Riesz2.IsClosedScalarDirichletForm`

A dense, symmetric, nonnegative, closed Markov form on L². Closedness uses the graph norm,
and normal contractions express the Dirichlet property. See Subsection 3.1 and Assumptions
4.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- A dense, symmetric, nonnegative, closed Markov form on L². Closedness uses the graph norm,
and normal contractions express the Dirichlet property. See Subsection 3.1 and Assumptions
4.1. -/
def IsClosedScalarDirichletForm {α : Type*} [MeasurableSpace α]
    {ρ : Measure α} (Q : ScalarFormData ρ) : Prop :=
  DenseRange (fun f : Q.1 => f.val) ∧
  (∀ f g : Q.1, Q.2 f g = Q.2 g f) ∧
  (∀ f : Q.1, 0 ≤ Q.2 f f) ∧
  (∀ (f : ℕ → Q.1) (u : Lp ℝ 2 ρ),
    Tendsto (fun k => (f k).val) atTop (𝓝 u) →
    (∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ i j : ℕ, k ≤ i → k ≤ j →
      ‖(f i).val - (f j).val‖ ^ 2 + Q.2 (f i - f j) (f i - f j) < ε) →
    ∃ g : Q.1, g.val = u ∧
      Tendsto (fun k => Q.2 (f k - g) (f k - g)) atTop (𝓝 0)) ∧
  (∀ (φ : ℝ → ℝ), LipschitzWith 1 φ → φ 0 = 0 → ∀ f : Q.1,
    ∃ g : Q.1, (∀ᵐ x ∂ρ, g.val x = φ (f.val x)) ∧ Q.2 g g ≤ Q.2 f f)

end Riesz2

end
end
