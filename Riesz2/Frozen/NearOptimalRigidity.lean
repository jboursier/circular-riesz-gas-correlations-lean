/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
public import Riesz1.Frozen.CyclicLift
import Riesz2.Main.NearOptimalRigidity

/-!
# Near-optimal rigidity of long-range gaps: `Riesz2.nearOptimalRigidity`

For 0 < s < 1, sums of k consecutive microscopic gaps deviate from k by at most k^{s/2+b},
except on an event with stretched exponential probability. Constants are uniform in the
volume, label and span. See Lemma 2.2 of the paper, from Theorem 1(1) of the companion
paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

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
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (ε / (4 * (s.val + 2))))) :=
  by exact Riesz2.Main.nearOptimalRigidity

end Riesz2

end
end
