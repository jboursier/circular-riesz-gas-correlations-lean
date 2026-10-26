/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.Frozen.InverseTemperature
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Riesz2.Main.OptimalPointwiseDecay

/-!
# Optimal pointwise decay in the long-range regime: `Riesz2.optimalPointwiseDecay`

Optimal value and intrinsic gradient decay on the full component cycle, for constrained and
unrestricted weak solutions, with unique existence. The loss exponent depends only on s, κₛ,
γₛ and M₀, and is chosen before ε, Cₛ and β. See Proposition 5.15.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- Optimal value and intrinsic gradient decay on the full component cycle, for constrained and
unrestricted weak solutions, with unique existence. The loss exponent depends only on s, κₛ,
γₛ and M₀, and is chosen before ε, Cₛ and β. See Proposition 5.15. -/
theorem optimalPointwiseDecay :
  ∀ (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (M₀ : ℕ+),
    0 < κₛ → 0 < γₛ → ∃ κ : ℝ, 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n m : ℕ+) (_ : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
        (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
        let K := (Nat.floor ((n : ℝ) ^ ε)) ^ (M₀ : ℕ)
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
          (ν : Measure (EuclideanSpace ℝ (Fin d))),
          IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
          IsProbabilityMeasure ν →
          (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
            IsEuclideanGibbsPotential volume ν Ω V 2) →
          ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
            IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
            PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
            ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (b : Bool),
              let S := if b then zeroSumComponents (Fin (m : ℕ)) else ⊤
              (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u →
                ∀ j : Fin (m : ℕ),
                  ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(2 - s.val)) * ‖χ‖ ∧
                  Real.sqrt (Q.2 (u j) (u j)) ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(3 - s.val) / 2) * ‖χ‖) :=
  by exact Riesz2.Main.optimalPointwiseDecay

end Riesz2

end
end
