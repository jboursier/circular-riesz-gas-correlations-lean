/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ParticlePairEnergy
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Admissible pair potentials: `Riesz2.AdmissibleParticlePairs`

The smooth pair potentials χ_ij of Assumptions 3.1, with lower curvature bound c, divergence
at both endpoints of (0,1), and the collision criterion for every a > 0. The particle number
satisfies N ≥ 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The smooth pair potentials χ_ij of Assumptions 3.1, with lower curvature bound c, divergence
at both endpoints of (0,1), and the collision criterion for every a > 0. The particle number
satisfies N ≥ 2. -/
def AdmissibleParticlePairs {N : ℕ+} (_hN : 2 ≤ (N : ℕ))
    (χ : ParticlePairData N) (c : ℝ) : Prop :=
  (∀ p, ContDiffOn ℝ (⊤ : ℕ∞) (χ p) (Ioo 0 1) ∧
    (∀ r ∈ Ioo (0 : ℝ) 1, c ≤ deriv (deriv (χ p)) r) ∧
    Tendsto (χ p) (𝓝[>] 0) atTop ∧ Tendsto (χ p) (𝓝[<] 1) atTop) ∧
  ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ particleChamber N,
      (Metric.infDist x (particleChamber N)ᶜ)⁻¹ ^ 2 - C ≤
        a * ‖gradient (particlePairEnergy χ) x‖ ^ 2 -
          Laplacian.laplacian (particlePairEnergy χ) x

end Riesz2

end
end
