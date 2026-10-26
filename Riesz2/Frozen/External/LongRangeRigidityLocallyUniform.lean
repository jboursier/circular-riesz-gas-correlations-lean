/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
public import Riesz1.Frozen.CyclicLift

/-!
# Locally uniform long-range gap rigidity: `Riesz2.External.LongRangeRigidityLocallyUniform`

The gap rigidity estimate of Theorem 1(1) of the companion paper, with constants uniform for
β in compact subsets of (0,+∞). For 0 < b < (1−s/2)/2, the probability that
|N(x_{i+k}−x_i)−k| ≥ k^{s/2+b} is at most C exp(−c k^{b/(4(s+2))}), uniformly in the volume,
label and 1 ≤ k ≤ floor(N/2). Compact-temperature uniformity follows from the proof of the
companion theorem. See also Lemma 2.2 of the paper.
-/

@[expose] public section

noncomputable section

open Set

namespace Riesz2.External

def LongRangeRigidityLocallyUniform : Prop :=
  ∀ (s : Riesz1.RieszExponent) (b : ℝ), 0 < b → b < (1 - s.val / 2) / 2 →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
        ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : ℤ) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
          gibbsMeasure (ofLong β s) N {X |
            |(N : ℝ) * (Riesz1.cyclicLift X (i + k) - Riesz1.cyclicLift X i) - k| ≥
              (k : ℝ) ^ (s.val / 2 + b)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / (4 * (s.val + 2)))))

end Riesz2.External

end
end
