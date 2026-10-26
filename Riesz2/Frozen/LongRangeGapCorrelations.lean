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
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.RieszExponent
public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.GapSecondMoments
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.IsMesoscopicSequence
public import Riesz2.Frozen.CorrelationFactor
public import Riesz2.Frozen.Gap
public import Riesz2.Frozen.GapCorrelation
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
import Riesz2.Main.LongRangeGapCorrelations

/-!
# Decay of long-range gap correlations: `Riesz2.longRangeGapCorrelations`

For 0 < s < 1, the covariance of one-gap observables decays as (1+d_N(i,j))^{−(2−s−ε)},
multiplied by the derivative factors in equation (1.4). The power δ depends only on s and ε.
On every mesoscopic scale n_N, some pair with n_N/2 ≤ d_N(i,j) ≤ n_N has gap covariance at
most −c₀d_N(i,j)^{s−2}, with c₀ depending only on β and s.
This is Theorem 1 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For 0 < s < 1, the covariance of one-gap observables decays as (1+d_N(i,j))^{−(2−s−ε)},
multiplied by the derivative factors in equation (1.4). The power δ depends only on s and ε.
On every mesoscopic scale n_N, some pair with n_N/2 ≤ d_N(i,j) ≤ n_N has gap covariance at
most −c₀d_N(i,j)^{s−2}, with c₀ depending only on β and s.
This is Theorem 1 of the paper. -/
theorem longRangeGapCorrelations :
  ∀ s : Riesz1.RieszExponent,
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ β : InverseTemperature, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
          let p := ofLong β s
          let d := Riesz1.cyclicIndexDistance N i j
          ∃ hMom : GapSecondMoments p N i.val j.val f g,
          |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
            C / (1 + (d : ℝ)) ^ (2 - s.val - ε) *
              correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d) ∧
    (∀ β : InverseTemperature, ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ n : ℕ+ → ℕ+, IsMesoscopicSequence n → ∃ m₀ : ℕ,
        ∀ m : ℕ, m₀ ≤ m →
          let N := Riesz1.particleNumber m
          ∃ i j : Fin (N : ℕ),
            (n N : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance N i j : ℝ) ∧
            (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ (n N : ℝ) ∧
            ∃ hi : MemLp (fun X => gap X i.val) 2 (gibbsMeasure (ofLong β s) N),
            ∃ hj : MemLp (fun X => gap X j.val) 2 (gibbsMeasure (ofLong β s) N),
            gapCorrelation (ofLong β s) N i.val j.val id id hi hj ≤
              -c₀ * (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (s.val - 2)) :=
  by exact Riesz2.Main.longRangeGapCorrelations

end Riesz2

end
end
