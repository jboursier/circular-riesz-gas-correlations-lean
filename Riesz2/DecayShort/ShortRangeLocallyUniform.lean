/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ShortRangeResultPart5

/-!
# Locally uniform short-range correlation constants

The compact-temperature quantifiers of Theorem 2 of the paper,
using the distance-threshold assembly of its written proof.
-/

public section
noncomputable section
open MeasureTheory Set
namespace Riesz2.DecayShort

/-- Theorem 2 of the paper, with constants uniform on every positive
compact temperature interval and the tail exponent chosen before that interval. -/
theorem shortRangeGapCorrelations_locallyUniform :
  ∀ s : ShortExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi → ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d :=
  ShortRangeResultPart5.paper_short_range_gap_correlations_locallyUniform

end Riesz2.DecayShort
