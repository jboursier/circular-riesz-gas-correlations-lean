/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.Frozen.ProperMarginalDomain
public import Riesz2.Frozen.HessianMatrix
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.OfLong
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Riesz2.Main.ProperPhysicalMarginalDecay

/-!
# Decay for the long-range physical marginal: `Riesz2.properPhysicalMarginalDecay`

Decay for the proper physical marginal with upper-gap forcing, including unique existence
for H¹ sources and bounded L² sources. The loss exponent is chosen before ε and β. Constants
are locally uniform in β, and infinite essential suprema retain their extended values. See
Proposition 5.18.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- Decay for the proper physical marginal with upper-gap forcing, including unique existence
for H¹ sources and bounded L² sources. The loss exponent is chosen before ε and β. Constants
are locally uniform in β, and infinite essential suprema retain their extended values. See
Proposition 5.18. -/
theorem properPhysicalMarginalDecay :
  ∀ s : Riesz1.RieszExponent, ∃ κ : ℝ, 0 < κ ∧
  ∀ θ : PhysicalCutoff, ∀ ε : ℝ, 0 < ε →
  ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (N n : ℕ+) (_ : 4 ≤ (N : ℕ)) (_ : 2 ≤ (n : ℕ)),
      2 * (n : ℕ) ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      let p := ofLong β s
      let ν := activeTiltedGapLaw p N n hn θ ε false
      0 < tiltNormalizer p N n hn θ ε false ∧ tiltNormalizer p N n hn θ ε false < ⊤ ∧
      IsProbabilityMeasure ν ∧
      ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
        IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
        IsNeumannRealization (properMarginalDomain n N) Q ∧
        IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
        ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4 * (i₀.val + 1) →
          4 * (i₀.val + 1) ≤ 3 * (n : ℕ) →
          ∀ χ : Lp ℝ 2 ν, (χ ∈ Q.1 ∨ eLpNorm χ ∞ ν < ⊤) →
          (∃! u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u →
            ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (κ * ε) *
                ((1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-(2 - s.val)) +
                  (n : ℝ) ^ (-(1 / 2 : ℝ)))) *
                (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ δ)) *
                  eLpNorm χ ∞ ν)) :=
  by exact Riesz2.Main.properPhysicalMarginalDecay

end Riesz2

end
end
