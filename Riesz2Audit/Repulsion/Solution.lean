/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.Repulsion.Definitions
public import Riesz2.Frozen.Repulsion

/-!
# Proposition 1.2 (Repulsion of neighbouring particles): the proof

The statement of the challenge, on the definitions of `Definitions.lean`, proved from
`Riesz2.repulsion` of the library. These definitions are copies of those of the library, so the
two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz2Audit.Repulsion

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), the Palm gaps satisfy P(z_{i+1}−z_i ≤ u) ≤ C exp(−cu^{-s})
for every i ∈ ℤ and 0 < u ≤ 1. The constants c,C > 0 depend only on β and s. The statement
includes the limiting process and its Palm probability law.
This is Proposition 1.2 of the paper. -/
theorem repulsion :
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    PalmRegular P ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
        repulsionProbability P i u ≤ ENNReal.ofReal (C * Real.exp (-c * u ^ (-p.val.2))) :=
  by exact _root_.Riesz2.repulsion

end Riesz2

end

end Riesz2Audit.Repulsion

end
