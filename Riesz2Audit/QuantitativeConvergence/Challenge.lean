/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.QuantitativeConvergence.Definitions

/-!
# Theorem 4 (Quantitative convergence of labelled gaps): the statement

Mathlib-only statement of Theorem 4 of J. Boursier, *Decay of correlations and thermodynamic
limit for the circular Riesz gas* (arXiv:2209.00396, revised version 2026).

For every pair of parameters `β > 0`, `s > 0`, `s ≠ 1` (`Parameters`), there is a unique
local total variation limit `P = Riesz_{s,β}` (`UniqueRieszLimit`, `limitingRieszProcess`),
and `PalmRegular P` holds. For every `ε > 0` there is `C > 0` such that, for every pair of
positive integers `N,K` with `K ≤ N^{min(s,2)/2}/32`, and every Lipschitz `G : ℝ^K → ℝ`
(`BlockObservable K`), the finite-gap observable and the Palm-gap observable are both integrable,
and

`|E_{P_{N,β}} G(y_1,...,y_K) - E_{Riesz_{s,β}^0} G(z_1-z_0,...,z_K-z_{K-1})|`
`≤ C N^{-min(s,2)min(s,1)/4+ε} Σ_{j=1}^K ‖∂_jG‖∞`.

Here `y_i = N(x_{i+1}-x_i)` (`finiteGapBlock`), the Palm enumeration satisfies `z_0 = 0`
(`rootedGapBlock`), and the norm is the least Lipschitz constant along a coordinate
(`coordinateDerivativeNorm`, `blockDerivativeNorm`). The limit and its Palm regularity are
concluded before `ε` is quantified, and `C` is chosen before `N`, `K` and `G`.

## How the objects are specified

`Parameters` contains both exponent regimes. `gibbsMeasure` uses the imported companion law
for `s < 1` and the lattice-sum Gibbs law for `s > 1`. Finite positions are ordered real lifts
with `0 ≤ x_0 < 1`, and `gap` uses the cyclic extension. The paper's label 1 is label 0, so
`finiteGapBlock` is the vector of Lean gaps with indices `0,...,K-1`.

`UniqueRieszLimit` means existence and uniqueness of a point-process limit in total variation
on every `[-R,R]`, `R > 0`, along `N = n+1`. It includes that each microscopic law is a
probability measure. The microscopic law retains centered positions in
`(-1/4,1/4)` and multiplies them by `N`. `rootedPalmMeasure` is the pullback of the Campbell
measure, obtained by averaging roots in `[0,1)`, to configurations containing `0` and unbounded
in both directions. `rootedGapBlock` uses the increasing enumeration of such a configuration.
`PalmRegular` concludes measurability of this carrier, its full Palm mass, normalization of
both Palm measures, zero mass of the complement, invariance of the gap sequence under index
shift, and integrability and expectation one of every integer-labelled gap.

`BlockObservable K` is a Lipschitz function on the finite product of `K` real lines with the
supremum metric. `coordinateDerivativeNorm G j` is the infimum of nonnegative constants `L` such
that `|G(x with x_j=t)-G(x)| ≤ L|t-x_j|` for every `x,t`. Their sum is `blockDerivativeNorm`.
This specifies the paper's partial-derivative norms without choosing pointwise derivatives.
`exponentA s = min(s/2,1)`, `exponentB s = min(s,1)/2`, and `convergenceRate s` is their
product. The real inequality on positive integer `K` is equivalent to the paper's floor bound
and already excludes `N = 1`. Both integrability assertions are conclusions. The constants are
chosen for each fixed `β`. The library also proves the version with constants uniform for `β` in
compact intervals,
`Riesz2.QuantitativeConvergenceResult.quantitativeConvergence_locallyUniform`, which takes the
proved input `External.LogConcaveConvergence` as an argument.

The statement uses the definitions of `Definitions.lean` in this directory, which imports
Mathlib only. The proof of the theorem is the only `sorry`.
-/

@[expose] public section

namespace Riesz2Audit.QuantitativeConvergence

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), expectations of Lipschitz functions G of the first K
microscopic gaps converge to those under Riesz_{s,β}^0. For 1 ≤ K ≤
floor(N^{min(s,2)/2}/32), the error is at most C N^{-min(s,2)min(s,1)/4+ε} ∑ⱼ ‖∂ⱼG‖∞. The
statement also supplies the limiting process and integrability of both observables.
This is Theorem 4 of the paper. -/
theorem quantitativeConvergence :
  letI := configurationMeasurableSpace
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    PalmRegular P ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N K : ℕ+, (K : ℝ) ≤ (N : ℝ) ^ exponentA p.val.2 / 32 →
        ∀ G : BlockObservable K,
          Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
            (gibbsMeasure p N) ∧
          Integrable (fun C => G.val (rootedGapBlock K C)) (rootedPalmMeasure P) ∧
          |(∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
            (∫ C, G.val (rootedGapBlock K C) ∂rootedPalmMeasure P)| ≤
              C * (N : ℝ) ^ (-convergenceRate p.val.2 + ε) * blockDerivativeNorm G :=
  sorry

end Riesz2

end

end Riesz2Audit.QuantitativeConvergence

end
