/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.TiltedParticleMeasure
public import Riesz2.Frozen.FiniteGapBlock
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Active tilted gap law: `Riesz2.activeTiltedGapLaw`

The image of the tilted particle law under the first n microscopic gaps, in Euclidean
coordinates. For n = N this law is supported on the mass-N hyperplane. See Section 5 and
Subsection 6.1 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The image of the tilted particle law under the first n microscopic gaps, in Euclidean
coordinates. For n = N this law is supported on the mass-N hyperplane. See Section 5 and
Subsection 6.1 of the paper. -/
def activeTiltedGapLaw (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) :
    Measure (EuclideanSpace ℝ (Fin (n : ℕ))) :=
  (tiltedParticleMeasure p N n hn θ ε twoSided).map
    (fun X => WithLp.toLp 2 (finiteGapBlock X))

end Riesz2

end
end
