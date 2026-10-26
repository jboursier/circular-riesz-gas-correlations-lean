/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.LongRangeGapCorrelations.Definitions

/-!
# Theorem 1 (Long-range gap correlations): the statement

Mathlib-only statement of Theorem 1 of J. Boursier, *Decay of correlations and thermodynamic
limit for the circular Riesz gas* (arXiv:2209.00396, revised version 2026).

For every `0 < s < 1`, both assertions hold. First, for every `ε > 0` there is `δ > 0` such
that, for every `β > 0`, there are `C, c > 0` such that, for every `N ≥ 1`, every pair of
labels `i,j` and every pair of observables `ξ,χ` (`GapObservable`), the four variables
`ξ(y_i)`, `χ(y_j)`, `ξ'(y_i)` and `χ'(y_j)` are almost everywhere strongly measurable with finite
second moments (`GapSecondMoments`), where `y_i = N(x_{i+1}-x_i)` (`gap`). With
`d = min(|i-j|,N-|i-j|)` (`Riesz1.cyclicIndexDistance`),

`|Cov_{P_{N,β}}[ξ(y_i),χ(y_j)]| ≤ C (1+d)^{-(2-s-ε)} A_i(ξ) A_j(χ)`,

where `A_i(ξ) = (E[ξ'(y_i)²])^{1/2} + ‖ξ'‖_{L∞(ℝ)} exp(-c d^δ)` (`correlationFactor`).
The covariance is `gapCorrelation`, and the supremum norm is the Lebesgue essential supremum.

Second, for every `β > 0` there is `c₀ > 0` such that, for every sequence of positive integers
`(n_N)` with `n_N → ∞` and `n_N/N → 0` (`IsMesoscopicSequence`), there is `m₀ ∈ ℕ` such that,
for every `m ≥ m₀`, setting `N = m+1`, there are labels `i,j` with
`n_N/2 ≤ d_N(i,j) ≤ n_N`. The two gaps are almost everywhere strongly measurable with finite
second moments, and `Cov_{P_{N,β}}[y_i,y_j] ≤ -c₀ d_N(i,j)^{s-2}`. Thus `δ` is chosen before
`β`, and `c₀` before the sequence, independently of `ε`.

## How the objects are specified

`Riesz1.RieszExponent` is `0 < s < 1`, and `InverseTemperature` is `β > 0`. `ofLong β s`
forms the parameters. `gibbsMeasure (ofLong β s) N` is exactly the companion library's
`Riesz1.gibbsMeasure`, with the ordered-pair energy `N^{-s} Σ_{i≠j} g_s(x_i-x_j)`.
The kernel is twice the real part of Mathlib's even Hurwitz zeta function. The finite
configuration is its ordered real lift `x_0 < ... < x_{N-1} < x_0+1`, with `0 ≤ x_0 < 1`.
The paper's label 1 is label 0. `Riesz1.cyclicLift` extends the positions to integer labels.

`GapObservable` is a pair consisting of a globally Lipschitz function and a Lebesgue almost
everywhere strongly measurable, essentially bounded representative of its derivative, with
`HasDerivAt` almost everywhere. This encodes the paper's locally absolutely continuous
observables with bounded derivatives. `derivativeSup` is the essential supremum of that
representative, and `gapDerivativeNorm` is its `L²` norm under the gap law. The statement covers
`N = 1` as well as the paper's `N ≥ 2`, for every supplied derivative representative.

`GapSecondMoments` consists of four `MemLp ... 2` assertions. These include almost everywhere
strong measurability and finiteness of the second moments. They are conclusions.
`gapCorrelation` is Mathlib's covariance with second-moment proofs supplied as arguments. The
mesoscopic limits use `N = Riesz1.particleNumber m = m+1`. The constants are chosen for each
fixed `β`. The library also proves the version with constants uniform for `β` in compact
intervals, `Riesz2.longRangeGapCorrelations_locallyUniform`, which takes the proved inputs
`External.PeriodicZeta` and `External.LongRangeRigidityLocallyUniform` as arguments.

The statement uses the definitions of `Definitions.lean` in this directory, which imports
Mathlib only. The proof of the theorem is the only `sorry`.
-/

@[expose] public section

namespace Riesz2Audit.LongRangeGapCorrelations

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
  sorry

end Riesz2

end

end Riesz2Audit.LongRangeGapCorrelations

end
