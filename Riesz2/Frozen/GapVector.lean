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
public import Riesz2.Frozen.Gap

/-!
# Full vector of microscopic gaps: `Riesz2.gapVector`

The vector Gap_N(X) = (N(x_{i+1}−x_i))ᵢ of Subsection 1.3 and Subsection 3.2, with labels
starting at zero. It agrees definitionally with the companion formalization's gap vector.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The vector Gap_N(X) = (N(x_{i+1}−x_i))ᵢ of Subsection 1.3 and Subsection 3.2, with labels
starting at zero. It agrees definitionally with the companion formalization's gap vector. -/
def gapVector {N : ℕ+} (X : Riesz1.Configuration N) : Fin (N : ℕ) → ℝ :=
  fun i => gap X i.val

end Riesz2

end
end
