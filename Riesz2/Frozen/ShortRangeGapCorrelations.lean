/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Riesz1.Frozen.CyclicIndexDistance
public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.GapSecondMoments
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.CorrelationFactor
public import Riesz2.Frozen.GapCorrelation
public import Riesz2.Frozen.OfShort
import Riesz2.Main.ShortRangeGapCorrelations

/-!
# Decay of short-range gap correlations: `Riesz2.shortRangeGapCorrelations`

For s > 1, the covariance of one-gap observables is bounded by C((1+d_N(i,j))^{-s+ε} +
N^{-1+ε}) times the derivative factors in equation (1.6). The power δ depends only on s and
ε. The finite-volume term accounts for the total-gap constraint. Lean also includes the
constant-gap case N = 1.
This is Theorem 2 of the paper.
-/

@[expose] public section

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
  by exact Riesz2.Main.shortRangeGapCorrelations

end Riesz2

end
end
