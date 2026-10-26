/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart10
public import Riesz2.Thermodynamic.LengthAveragingFibresPart11

/-!
# Length averaging on fibres

The fibre estimates in the proof of Lemma 6.5 hold in both exponent regimes. The
long-range estimate uses `LengthAveragingFibresPart11`. The short-range estimate uses
the retained squared comparison of `LengthAveragingFibresPart10`.
-/

@[expose] public section
noncomputable section
namespace Riesz2.LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper, both regimes: for `0 < s < 1` the long
conclusion `LongConclusionInternal s`, and for `s > 1` the short conclusion
`ShortConclusionInternal s` (exceptional moments, unique tangent solvability, both
conditional fibre sums and the multiplier estimate). -/
theorem length_averaging_fibres
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform) :
    (∀ s : Riesz1.RieszExponent, LongConclusionInternal s) ∧
    (∀ s : ℝ, 1 < s → ShortConclusionInternal s) :=
  length_averaging_fibres_internal hz hRig short_uniform_conditional_comparison_internal

end Riesz2.LengthAveragingFibres
