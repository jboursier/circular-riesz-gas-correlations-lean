/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.ShortRangeGapCorrelations.Definitions
public import Riesz2.Frozen.ShortRangeGapCorrelations

/-!
# Theorem 2 (Short-range gap correlations): the proof

The statement of the challenge, on the definitions of `Definitions.lean`, proved from
`Riesz2.shortRangeGapCorrelations` of the library. These definitions are copies of those of the library, so the
two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz2Audit.ShortRangeGapCorrelations

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For s > 1, the covariance of one-gap observables is bounded by C((1+d_N(i,j))^{-s+ε} +
N^{-1+ε}) times the derivative factors in equation (1.6). The power δ depends only on s and
ε. The finite-volume term accounts for the total-gap constraint. Lean also includes the
constant-gap case N = 1.
This is Theorem 2 of the paper. -/
theorem shortRangeGapCorrelations :
  ∀ s : ShortExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ β : InverseTemperature, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d :=
  by exact _root_.Riesz2.shortRangeGapCorrelations

end Riesz2

end

end Riesz2Audit.ShortRangeGapCorrelations

end
