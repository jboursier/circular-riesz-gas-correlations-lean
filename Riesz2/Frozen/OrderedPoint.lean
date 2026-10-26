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
public import Riesz2.Frozen.OrderedPointDomain
public import Riesz2.Frozen.Count

/-!
# Ordered point in a bounded interval: `Riesz2.orderedPoint`

The jth point of a configuration in [a,b) or (a,b], defined on configurations containing at
least j such points. Local finiteness makes the defining infimum a minimum. This encodes an
ordered enumeration of the configurations of Subsection 1.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The jth point of a configuration in [a,b) or (a,b], defined on configurations containing at
least j such points. Local finiteness makes the defining infimum a minimum. This encodes an
ordered enumeration of the configurations of Subsection 1.5. -/
def orderedPoint (a b : ℝ) (leftClosed : Bool) (j : ℕ+)
    (C : OrderedPointDomain a b leftClosed j) : ℝ :=
  let I := if leftClosed then Ico a b else Ioc a b
  sInf {x : ℝ | x ∈ C.val.val ∩ I ∧ (j : ℝ≥0∞) ≤ count C.val (I ∩ Iic x)}

end Riesz2

end
end
