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
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.CyclicLift

/-!
# Microscopic nearest-neighbour gap: `Riesz2.gap`

The microscopic gap N(x_{j+1}−x_j), using the cyclic lifts of `Riesz1`. See Subsection 1.3.
This agrees definitionally with the companion formalization's gap.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The microscopic gap N(x_{j+1}−x_j), using the cyclic lifts of `Riesz1`. See Subsection 1.3.
This agrees definitionally with the companion formalization's gap. -/
def gap {N : ℕ+} (X : Riesz1.Configuration N) (j : ℤ) : ℝ :=
  (N : ℝ) * (Riesz1.cyclicLift X (j + 1) - Riesz1.cyclicLift X j)

end Riesz2

end
end
