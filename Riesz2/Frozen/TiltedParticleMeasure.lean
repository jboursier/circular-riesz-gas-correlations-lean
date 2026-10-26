/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.TiltNormalizer

/-!
# Tilted particle Gibbs law: `Riesz2.tiltedParticleMeasure`

The normalized measure proportional to exp(−βF) G_{N,β} on particle configurations, where F
is the gap penalty of Section 5 or equation (6.1). Its gap image is defined separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The normalized measure proportional to exp(−βF) G_{N,β} on particle configurations, where F
is the gap penalty of Section 5 or equation (6.1). Its gap image is defined separately. -/
def tiltedParticleMeasure (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) : Measure (Riesz1.Configuration N) :=
  (tiltNormalizer p N n hn θ ε twoSided)⁻¹ •
    (gibbsMeasure p N).withDensity (fun X =>
      ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε twoSided X)))

end Riesz2

end
end
