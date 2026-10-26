/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.Frozen.DependsOnBlockCoordinates
public import Riesz2.Frozen.SymmetricMiddleBlock
public import Riesz2.Frozen.GoodBlockEvent
public import Riesz2.Frozen.RestrictedBlockDerivativeNorm
public import Riesz2.Frozen.BlockDerivativeNorm
import Riesz2.Main.TwoVolumeComparisonV2

/-!
# Comparison of gap laws at two volumes: `Riesz2.twoVolumeComparisonV2`

The comparison of two-sided tilted gap expectations at volumes N and N' in Proposition 6.6.
Observables depend on the symmetric middle block with K ≤ floor(n/4), with strict inequality
when n ≡ 1 mod 4 so that the support lies in the closed middle half. K_s, κ, the small-ε
range and δ are chosen before β. Constants C,c are uniform on compact positive temperature
intervals. Normalization and integrability are conclusions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The comparison of two-sided tilted gap expectations at volumes N and N' in Proposition 6.6.
Observables depend on the symmetric middle block with K ≤ floor(n/4), with strict inequality
when n ≡ 1 mod 4 so that the support lies in the closed middle half. K_s, κ, the small-ε
range and δ are chosen before β. Constants C,c are uniform on compact positive temperature
intervals. Normalization and integrability are conclusions. -/
theorem twoVolumeComparisonV2 :
  ∀ s : {s : ℝ // 0 < s ∧ s ≠ 1},
    ∃ Kₛ κ ε₀ : ℝ, 1 < Kₛ ∧ 0 < κ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    let p : Parameters := ⟨(β.val, s.val), β.property, s.property⟩
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (hn' : (n : ℕ) ≤ (N' : ℕ)),
      let μ := tiltedParticleMeasure p N n hn θ ε true
      let μ' := tiltedParticleMeasure p N' n hn' θ ε true
      0 < tiltNormalizer p N n hn θ ε true ∧ tiltNormalizer p N n hn θ ε true < ⊤ ∧
      0 < tiltNormalizer p N' n hn' θ ε true ∧ tiltNormalizer p N' n hn' θ ε true < ⊤ ∧
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      ∀ (K : ℕ), K ≤ (n : ℕ) / 4 →
        ((n : ℕ) % 4 ≠ 1 ∨ K < (n : ℕ) / 4) → ∀ G : BlockObservable n,
        DependsOnBlockCoordinates G (symmetricMiddleBlock n K) →
        Integrable (fun X => G.val (finiteGapBlock X)) μ ∧
        Integrable (fun X => G.val (finiteGapBlock X)) μ' ∧
        |(∫ X, G.val (finiteGapBlock X) ∂μ) - (∫ X, G.val (finiteGapBlock X) ∂μ')| ≤
          C * (n : ℝ) ^ (κ * ε - min s.val 1 / 2) *
            (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
                (goodBlockEvent s.val n N (Kₛ * ε)) +
              Real.exp (-c * (n : ℝ) ^ δ) * blockDerivativeNorm G) :=
  by exact Riesz2.Main.twoVolumeComparisonV2

end Riesz2

end
end
