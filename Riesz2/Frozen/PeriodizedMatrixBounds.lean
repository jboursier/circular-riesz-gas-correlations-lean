/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ReferenceIntervalMatrix
public import Riesz1.Frozen.CyclicIndexDistance
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Bounds on the periodized matrix: `Riesz2.PeriodizedMatrixBounds`

The hypotheses on the matrix M in Assumptions 5.3: reference exterior blocks, symmetric
coercivity, a positive cyclic-interval representation, upper and long-interval lower
coefficient bounds, and the active entry error. Cutoff and structural parameter ranges are
specified at each use.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The hypotheses on the matrix M in Assumptions 5.3: reference exterior blocks, symmetric
coercivity, a positive cyclic-interval representation, upper and long-interval lower
coefficient bounds, and the active entry error. Cutoff and structural parameter ranges are
specified at each use. -/
def PeriodizedMatrixBounds {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) : Prop :=
  (∀ i j, Measurable (fun x => M x i j)) ∧
  let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
  (∀ᵐ x ∂ν,
    (∀ i j, M x i j = M x j i) ∧
    (∀ i j, (n : ℕ) ≤ i.val ∨ (n : ℕ) ≤ j.val → M x i j = H i j) ∧
    (∀ z : Fin (m : ℕ) → ℝ,
      C⁻¹ * (n : ℝ) ^ (-κ * ε) * (∑ i, z i ^ 2) ≤
        ∑ i, ∑ j, z i * M x i j * z j) ∧
    (∀ i j, i.val < (n : ℕ) → j.val < (n : ℕ) →
      |M x i j - H i j| ≤ C * (n : ℝ) ^ (κ * ε) *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2))) ∧
  ∃ a : Fin (m : ℕ) → Fin ((m : ℕ) / 2) → α → ℝ,
    (∀ i r, Measurable (a i r)) ∧ ∀ᵐ x ∂ν,
    (∀ i r, 0 ≤ a i r x ∧ a i r x ≤
      C * (n : ℝ) ^ (κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ∧
      ((n : ℝ) ^ (γ * ε) ≤ ((r.val + 1 : ℕ) : ℝ) →
        C⁻¹ * (n : ℝ) ^ (-κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤ a i r x)) ∧
    ∀ z : Fin (m : ℕ) → ℝ,
      (∑ i, ∑ j, z i * M x i j * z j) =
        ∑ i, ∑ r, a i r x * (cyclicGapSum m i (r.val + 1) z) ^ 2

end Riesz2

end
end
