/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.WeightedWeakSolution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Riesz2.Main.MaximumPrinciple

/-!
# Maximum principle for weak solutions: `Riesz2.maximumPrinciple`

The maximum principle for finite-energy weak solutions of (M + L)u = v, including solutions
in a fixed component subspace. Essential suprema use the Euclidean vector norm and may be
infinite. See Proposition 3.6.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The maximum principle for finite-energy weak solutions of (M + L)u = v, including solutions
in a fixed component subspace. Essential suprema use the Euclidean vector norm and may be
infinite. See Proposition 3.6. -/
theorem maximumPrinciple :
  ∀ (d : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin d))),
    IsProbabilityMeasure ρ → ∀ Q : ScalarFormData ρ,
    IsClosedScalarDirichletForm Q →
    ∀ (m : ℕ+) (M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
      (∀ i j, Measurable (fun x => M x i j)) → ∀ c : ℝ, 0 < c →
      (∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j) →
      ∀ (S : Submodule ℝ (Fin (m : ℕ) → ℝ)) (v : Fin (m : ℕ) → Lp ℝ 2 ρ)
        (u : Fin (m : ℕ) → Q.1),
        WeightedWeakSolution Q M S v u →
        eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
          ENNReal.ofReal c⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => v i x)) ∞ ρ :=
  by exact Riesz2.Main.maximumPrinciple

end Riesz2

end
end
