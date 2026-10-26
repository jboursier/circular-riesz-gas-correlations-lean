/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
public import Riesz1.Frozen.CyclicLift
public import Riesz1.Frozen.AlmostOptimalRigidity

/-!
# Proof of near-optimal rigidity of long-range gaps

For 0 < s < 1, sums of k consecutive microscopic gaps deviate from k by at most k^{s/2+b},
except on an event with stretched exponential probability. Constants are uniform in the
volume, label and span. See Lemma 2.2 of the paper, from Theorem 1(1) of the companion
paper. The proof applies `Riesz1.almost_optimal_rigidity` through the long-range branch of
the Gibbs law.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.Main

/-- For 0 < s < 1, sums of k consecutive microscopic gaps deviate from k by at most k^{s/2+b},
except on an event with stretched exponential probability. Constants are uniform in the
volume, label and span. See Lemma 2.2 of the paper, from Theorem 1(1) of the companion
paper. -/
theorem nearOptimalRigidity :
  ∀ (s : Riesz1.RieszExponent) (β : InverseTemperature),
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) (k : ℕ),
          1 ≤ k → k ≤ (N : ℕ) / 2 →
          gibbsMeasure (ofLong β s) N {X |
            |(N : ℝ) * (Riesz1.cyclicLift X ((i.val : ℤ) + k) -
                Riesz1.cyclicLift X i.val) - k| ≥ (k : ℝ) ^ (s.val / 2 + ε)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (ε / (4 * (s.val + 2))))) := by
  intro s β
  obtain ⟨_, ε₀, hε₀, h⟩ := Riesz1.almost_optimal_rigidity
    β.val s.val β.property s.property.1 s.property.2
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨c, C, hc, hC, hN⟩ := h ε hε hεsmall
  refine ⟨C, c, hC, hc, ?_⟩
  intro N _ i k hk hkN
  simpa [gibbsMeasure, ofLong, s.property.2] using (hN N).1 i k hk hkN

end Riesz2.Main

end
