/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.SummableCoerciveMatrix
public import Riesz2.Frozen.InverseTemperature
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Analysis.Convex.Basic
public import Riesz2.DecayShort.OptimalDecay

/-!
# Proof of optimal decay for a point source

The optimal decay estimate for the weak solution of (M + L)u = χe_i under Assumptions 4.1
and 4.2. The statement includes unique existence on the full finite-energy domain. The loss
exponent is chosen before h, the matrix prefactor and the remaining data. See Proposition
4.5. The proof is `Riesz2.OptimalDecay.optimal_point_source_decay`.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.Main

/-- The optimal decay estimate for the weak solution of (M + L)u = χe_i under Assumptions 4.1
and 4.2. The statement includes unique existence on the full finite-energy domain. The loss
exponent is chosen before h, the matrix prefactor and the remaining data. See Proposition
4.5. -/
theorem optimalPointSourceDecay :
  ∀ (s : ShortExponent) (β : InverseTemperature) (q : ℝ),
    0 ≤ q → ∃ r : ℝ, 0 ≤ r ∧ ∀ h : ℝ, 0 < h → ∀ A : ℝ, 1 ≤ A →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ+) (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ (n : ℕ) → ∀ g : ComponentGeometry ι,
      ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
        (ν : Measure (EuclideanSpace ℝ (Fin d))),
        IsOpen Ω → Convex ℝ Ω → Ω.Nonempty → IsProbabilityMeasure ν → ν Ωᶜ = 0 →
        ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
          IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ,
            SummableCoerciveMatrix (ρ := ν) s n h A q g M →
            ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
              (∃! u : ι → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : ι → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) ⊤ (fun i => if i = i₀ then χ else 0) u →
                ∀ j : ι, ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
                  (1 + componentDistance g j i₀) ^ (-s.val) * ‖χ‖) :=
  Riesz2.OptimalDecay.optimal_point_source_decay

end Riesz2.Main
