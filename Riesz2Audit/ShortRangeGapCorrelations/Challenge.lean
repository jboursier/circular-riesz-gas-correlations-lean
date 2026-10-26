/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.ShortRangeGapCorrelations.Definitions

/-!
# Theorem 2 (Short-range gap correlations): the statement

Mathlib-only statement of Theorem 2 of J. Boursier, *Decay of correlations and thermodynamic
limit for the circular Riesz gas* (arXiv:2209.00396, revised version 2026).

For every `s > 1` and every `ε > 0` there is `δ > 0` such that, for every `β > 0`, there are
`C, c > 0` such that, for every `N ≥ 1`, every pair of labels `i,j` and every pair of
observables `ξ,χ` (`GapObservable`), the four variables `ξ(y_i)`, `χ(y_j)`, `ξ'(y_i)` and
`χ'(y_j)` are almost everywhere strongly measurable with finite second moments
(`GapSecondMoments`), where `y_i = N(x_{i+1}-x_i)` (`gap`). With
`d = min(|i-j|,N-|i-j|)` (`Riesz1.cyclicIndexDistance`),

`|Cov_{P_{N,β}}[ξ(y_i),χ(y_j)]| ≤ C ((1+d)^{-s+ε} + N^{-1+ε}) A_i(ξ) A_j(χ)`,

where `A_i(ξ) = (E[ξ'(y_i)²])^{1/2} + ‖ξ'‖_{L∞(ℝ)} exp(-c d^δ)` (`correlationFactor`).
The covariance is `gapCorrelation`, and the supremum norm is the Lebesgue essential supremum.
The exponent `δ` is chosen before `β`, and `C,c` before `N`, the labels and the observables.

## How the objects are specified

`ShortExponent` is `s > 1`, and `InverseTemperature` is `β > 0`. `ofShort β s` forms the
parameters. `gibbsMeasure` selects `shortGibbsMeasure`, whose energy is
`N^{-s} Σ_{i≠j} Σ_{k∈ℤ}|x_i-x_j+k|^{-s}` (`shortEnergy`, `shortKernelLift`). The lattice sum
is defined off the integer lattice (`OffLattice`). The Gibbs law is the inverse extended
partition function times the exponential density with respect to the companion library's
Lebesgue measure on ordered real lifts.

A lift satisfies `x_0 < ... < x_{N-1} < x_0+1` and `0 ≤ x_0 < 1`. The paper's label 1 is
label 0. `gap` uses `Riesz1.cyclicLift`, so it includes the gap across the end of the cycle.
`GapObservable` supplies a Lipschitz function and a Lebesgue almost everywhere strongly
measurable, essentially bounded derivative representative satisfying `HasDerivAt` almost
everywhere. `derivativeSup` is its essential supremum, and `gapDerivativeNorm` is its `L²` norm
under the gap law. This encodes the paper's locally absolutely continuous observables with
bounded derivatives.

`GapSecondMoments` concludes four `MemLp ... 2` assertions, including almost everywhere strong
measurability and finite second moments. `gapCorrelation` is Mathlib's covariance with the
second-moment proofs as arguments. The statement also covers the constant-gap case `N = 1`,
while the paper starts at `N = 2`. The constants are chosen for each fixed `β`. The library also
proves the version with constants uniform for `β` in compact intervals,
`Riesz2.DecayShort.shortRangeGapCorrelations_locallyUniform`.

The statement uses the definitions of `Definitions.lean` in this directory, which imports
Mathlib only. The proof of the theorem is the only `sorry`.
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
  sorry

end Riesz2

end

end Riesz2Audit.ShortRangeGapCorrelations

end
