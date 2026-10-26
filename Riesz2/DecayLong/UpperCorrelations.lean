/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.UpperThreshold

/-!
# The distance threshold in the proof of Theorem 1

The proof of Theorem 1 of the paper uses a proper
window when `1 + d ≤ N^δ₀`, and the full cycle otherwise. Here `ρ > 2(2-s)`
and `δ₀ = 1/(2ρ)`. Bounded volumes are absorbed uniformly in temperature.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace Riesz2.DecayLong.UpperCorrelations

open Riesz2.DecayShort GibbsPotentialComparison PhysicalCore
open Riesz2.DecayShort.ShortRangeResultPart5

set_option backward.isDefEq.respectTransparency false

/-- The upper bound in Theorem 1 of the paper,
by singleton specialization of its compact-temperature threshold proof.
See the proof of Theorem 1 in the paper: physical gap
covariance decay, including second moments. The stretched-exponential power
is chosen before temperature. Both factors use the unforced derivative norms. -/
theorem decay_gap_correlations_upper (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
  ∀ s : Riesz1.RieszExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ β : InverseTemperature, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofLong β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * (1 + (d : ℝ)) ^ (-(2-s.val) + ε) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  exact decay_gap_correlations_upper_by_threshold hzeta hRig

end Riesz2.DecayLong.UpperCorrelations
