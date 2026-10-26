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

/-!
# Real lifts away from collisions: `Riesz2.OffLattice`

Real numbers whose image in the unit circle is nonzero. These are the lifts away from the
collision lattice ℤ on which the kernel of Subsection 1.1 is evaluated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Real numbers whose image in the unit circle is nonzero. These are the lifts away from the
collision lattice ℤ on which the kernel of Subsection 1.1 is evaluated. -/
@[reducible] def OffLattice := {x : ℝ // (x : UnitAddCircle) ≠ 0}

end Riesz2

end
end
