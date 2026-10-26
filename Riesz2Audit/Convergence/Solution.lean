/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.Convergence.Definitions
public import Riesz2.Frozen.Convergence

/-!
# Theorem 3 (Uniqueness of the limiting measure): the proof

The statement of the challenge, on the definitions of `Definitions.lean`, proved from
`Riesz2.convergence` of the library. These definitions are copies of those of the library, so the
two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz2Audit.Convergence

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), the microscopic laws Q_{N,β} converge in total variation
on every bounded window to a unique process Riesz_{s,β}. The limit is translation invariant
and has intensity one. Its Palm law has two-sided, index-stationary gaps of mean one, as
constructed in Subsection 6.3.
This is Theorem 3 of the paper. -/
theorem convergence :
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    IsStationary P ∧ HasIntensity P 1 ∧ PalmRegular P :=
  by exact _root_.Riesz2.convergence

end Riesz2

end

end Riesz2Audit.Convergence

end
