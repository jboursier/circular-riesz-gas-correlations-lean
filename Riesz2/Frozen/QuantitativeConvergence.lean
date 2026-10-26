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
public import Riesz2.Frozen.BlockObservable
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.UniqueRieszLimit
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.ConvergenceRate
public import Riesz2.Frozen.ExponentA
public import Riesz2.Frozen.FiniteGapBlock
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.LimitingRieszProcess
public import Riesz2.Frozen.RootedGapBlock
public import Riesz2.Frozen.RootedPalmMeasure
import Riesz2.Main.QuantitativeConvergence

/-!
# Rate of convergence of finite gap blocks: `Riesz2.quantitativeConvergence`

For β > 0 and s ∈ (0,1) ∪ (1,+∞), expectations of Lipschitz functions G of the first K
microscopic gaps converge to those under Riesz_{s,β}^0. For 1 ≤ K ≤
floor(N^{min(s,2)/2}/32), the error is at most C N^{-min(s,2)min(s,1)/4+ε} ∑ⱼ ‖∂ⱼG‖∞. The
statement also supplies the limiting process and integrability of both observables.
This is Theorem 4 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), expectations of Lipschitz functions G of the first K
microscopic gaps converge to those under Riesz_{s,β}^0. For 1 ≤ K ≤
floor(N^{min(s,2)/2}/32), the error is at most C N^{-min(s,2)min(s,1)/4+ε} ∑ⱼ ‖∂ⱼG‖∞. The
statement also supplies the limiting process and integrability of both observables.
This is Theorem 4 of the paper. -/
theorem quantitativeConvergence :
  letI := configurationMeasurableSpace
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    PalmRegular P ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N K : ℕ+, (K : ℝ) ≤ (N : ℝ) ^ exponentA p.val.2 / 32 →
        ∀ G : BlockObservable K,
          Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
            (gibbsMeasure p N) ∧
          Integrable (fun C => G.val (rootedGapBlock K C)) (rootedPalmMeasure P) ∧
          |(∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
            (∫ C, G.val (rootedGapBlock K C) ∂rootedPalmMeasure P)| ≤
              C * (N : ℝ) ^ (-convergenceRate p.val.2 + ε) * blockDerivativeNorm G :=
  by exact Riesz2.Main.quantitativeConvergence

end Riesz2

end
end
