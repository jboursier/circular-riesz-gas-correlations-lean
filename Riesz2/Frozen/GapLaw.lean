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
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.GapVector
public import Riesz2.Frozen.GibbsMeasure

/-!
# Law of the microscopic gaps: `Riesz2.gapLaw`

The image G_{N,β}^g of the particle Gibbs law under the full gap map Gap_N. See Subsection
1.3 and Subsection 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The image G_{N,β}^g of the particle Gibbs law under the full gap map Gap_N. See Subsection
1.3 and Subsection 3.2. -/
def gapLaw (p : Parameters) (N : ℕ+) : Measure (Fin (N : ℕ) → ℝ) :=
  (gibbsMeasure p N).map gapVector

end Riesz2

end
end
